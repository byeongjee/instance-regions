use std::iter;

use preborrowck_mir::RecordedMir;
use rustc_abi::FieldIdx;
use rustc_hir as hir;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::lang_items::LangItem;
use rustc_index::IndexSlice;
use rustc_infer::infer::canonical::{Canonical, QueryRegionConstraints};
use rustc_infer::infer::{BoundRegionConversionTime, RegionVariableOrigin};
use rustc_middle::mir::visit::{NonMutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::{
    AggregateKind, BinOp, Body, CastKind, Const, ConstOperand, HasLocalDecls, Local, LocalDecl,
    Location, NonDivergingIntrinsic, Operand, Place, PlaceElem, PlaceRef, PlaceTy, ProjectionElem,
    Promoted, RETURN_PLACE, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
    UnevaluatedConst, UserTypeProjection, UserTypeProjections,
};
use rustc_middle::traits::query::NoSolution;
use rustc_middle::traits::{ObligationCause, ObligationCauseCode};
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::cast::CastTy;
use rustc_middle::ty::{
    self, CanonicalUserTypeAnnotation, CanonicalUserTypeAnnotations, CoroutineArgsExt,
    GenericArgsRef, Ty, TyCtxt, TypeFoldable, TypeVisitableExt, Unnormalized, Upcast, UserArgs,
    UserTypeAnnotationIndex,
};
use rustc_span::{Span, Spanned};
use rustc_trait_selection::infer::InferCtxtExt;
use rustc_trait_selection::traits::query::type_op;
use rustc_trait_selection::traits::{PredicateObligations, wf};

use super::constraints::Constraints;
use super::convert::Conversion;
use super::infer::{Infer, Scraped, assert_instantiated};
use super::relations::Relations;
use super::universal::{DefiningTy, Universal};

// Generates the outlives constraints of a body by relating the types of its MIR
// the way the MIR type checker of rustc does.
pub(crate) struct TypeChecker<'a, 'tcx> {
    pub(super) infer: &'a Infer<'tcx>,
    pub(super) body: &'a Body<'tcx>,
    promoted: &'a IndexSlice<Promoted, Body<'tcx>>,
    user_type_annotations: &'a CanonicalUserTypeAnnotations<'tcx>,
    pub(super) relations: &'a Relations<'tcx>,
    pub(super) constraints: &'a mut Constraints<'tcx>,
    deferred_closure_requirements: Vec<(DefId, GenericArgsRef<'tcx>)>,
    set: &'a RecordedMir<'tcx>,
    last_span: Span,
}

pub(crate) fn type_check<'tcx>(
    infer: &Infer<'tcx>,
    body: &Body<'tcx>,
    promoted: &IndexSlice<Promoted, Body<'tcx>>,
    relations: &Relations<'tcx>,
    constraints: &mut Constraints<'tcx>,
    set: &RecordedMir<'tcx>,
) -> Vec<(DefId, GenericArgsRef<'tcx>)> {
    let mut typeck = TypeChecker {
        infer,
        body,
        promoted,
        user_type_annotations: &body.user_type_annotations,
        relations,
        constraints,
        deferred_closure_requirements: Vec::new(),
        set,
        last_span: body.span,
    };
    if !infer.failed() {
        typeck.check_user_type_annotations();
    }
    if !infer.failed() {
        typeck.visit_body(body);
    }
    if !infer.failed() {
        typeck.equate_inputs_and_outputs(&relations.normalized_inputs_and_output);
    }
    if !infer.failed() {
        typeck.check_signature_annotation();
    }
    if !infer.failed() {
        typeck.generate_liveness_constraints();
    }
    typeck.deferred_closure_requirements
}

impl<'a, 'tcx> TypeChecker<'a, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.infer.tcx
    }

    pub(super) fn universal(&self) -> &'a Universal<'tcx> {
        &self.relations.universal
    }

    fn span(&self, location: Location) -> Span {
        self.body.source_info(location).span
    }

    fn mirbug(&self, message: impl Into<String>) {
        let message: String = message.into();
        self.infer.fail(format!("broken MIR in {:?}: {message}", self.body.source.def_id()));
    }

    fn check_user_type_annotations(&mut self) {
        for user_annotation in self.user_type_annotations {
            let CanonicalUserTypeAnnotation { span, ref user_ty, inferred_ty } = *user_annotation;
            let user_ty: ty::CanonicalUserType<'tcx> = ty::Canonical {
                value: self
                    .universal()
                    .instantiate(self.tcx(), ty::EarlyBinder::bind(user_ty.value)),
                ..**user_ty
            };
            let annotation: ty::UserType<'tcx> = self.instantiate_canonical(span, &user_ty);
            self.ascribe_user_type(inferred_ty, annotation, span);
        }
    }

    pub(super) fn push_region_constraints(
        &mut self,
        span: Span,
        data: &QueryRegionConstraints<'tcx>,
    ) {
        Conversion::new(
            self.infer,
            &self.relations.universal,
            &self.relations.region_bound_pairs,
            &self.relations.known_type_outlives,
            span,
            self.constraints,
        )
        .convert_all(data);
    }

    // Adds the constraints for `a R b` where `R` is `<:` for `Covariant`, `==` for
    // `Invariant`, and `:>` for `Contravariant`.
    fn relate_types(
        &mut self,
        a: Ty<'tcx>,
        v: ty::Variance,
        b: Ty<'tcx>,
        span: Span,
    ) -> Result<(), NoSolution> {
        assert_instantiated(&a);
        assert_instantiated(&b);
        let cause: ObligationCause<'tcx> = self.infer.cause(span);
        let param_env: ty::ParamEnv<'tcx> = self.infer.param_env;
        let ((), constraints) = self
            .infer
            .scrape(
                || format!("relating {a:?} {v:?} {b:?}"),
                |ocx| ocx.relate(&cause, param_env, v, a, b).map_err(|_| NoSolution),
            )
            .map_err(|()| NoSolution)?;
        if let Some(constraints) = constraints {
            self.push_region_constraints(span, constraints);
        }
        Ok(())
    }

    fn eq_args(
        &mut self,
        a: GenericArgsRef<'tcx>,
        b: GenericArgsRef<'tcx>,
        span: Span,
    ) -> Result<(), NoSolution> {
        assert_instantiated(&a);
        assert_instantiated(&b);
        let cause: ObligationCause<'tcx> = self.infer.cause(span);
        let param_env: ty::ParamEnv<'tcx> = self.infer.param_env;
        let ((), constraints) = self
            .infer
            .scrape(
                || format!("equating {a:?} and {b:?}"),
                |ocx| {
                    for (a, b) in iter::zip(a, b) {
                        ocx.eq(&cause, param_env, a, b).map_err(|_| NoSolution)?;
                    }
                    Ok(())
                },
            )
            .map_err(|()| NoSolution)?;
        if let Some(constraints) = constraints {
            self.push_region_constraints(span, constraints);
        }
        Ok(())
    }

    fn sub_types(&mut self, sub: Ty<'tcx>, sup: Ty<'tcx>, span: Span) -> Result<(), NoSolution> {
        self.relate_types(sup, ty::Contravariant, sub, span)
    }

    fn eq_types(
        &mut self,
        expected: Ty<'tcx>,
        found: Ty<'tcx>,
        span: Span,
    ) -> Result<(), NoSolution> {
        self.relate_types(expected, ty::Invariant, found, span)
    }

    fn relate_type_and_user_type(
        &mut self,
        a: Ty<'tcx>,
        v: ty::Variance,
        user_ty: &UserTypeProjection,
        span: Span,
    ) -> Result<(), NoSolution> {
        let annotated_type: Ty<'tcx> = self.user_type_annotations[user_ty.base].inferred_ty;
        let mut curr_projected_ty: PlaceTy<'tcx> = PlaceTy::from_ty(annotated_type);
        let tcx: TyCtxt<'tcx> = self.tcx();
        for proj in &user_ty.projs {
            if !self.infer.next_trait_solver()
                && let ty::Alias(ty::AliasTy { kind: ty::Opaque { .. }, .. }) =
                    curr_projected_ty.ty.kind()
            {
                return Ok(());
            }
            let projected_ty: PlaceTy<'tcx> = curr_projected_ty.projection_ty_core(
                tcx,
                proj,
                |ty| self.structurally_resolve(ty, span),
                |ty, variant_index, field, ()| PlaceTy::field_ty(tcx, ty, variant_index, field),
                |()| unreachable!(),
            );
            curr_projected_ty = projected_ty;
        }
        let a: Ty<'tcx> = self.normalize(a, span);
        let ty: Ty<'tcx> = self.normalize(curr_projected_ty.ty, span);
        self.relate_types(ty, v.xform(ty::Contravariant), a, span)?;
        Ok(())
    }

    fn check_promoted(&mut self, promoted_body: &'a Body<'tcx>) {
        let parent_body: &'a Body<'tcx> = std::mem::replace(&mut self.body, promoted_body);
        self.visit_body(promoted_body);
        self.body = parent_body;
    }

    pub(super) fn instantiate_canonical<T>(
        &mut self,
        span: Span,
        canonical: &Canonical<'tcx, T>,
    ) -> T
    where
        T: TypeFoldable<TyCtxt<'tcx>> + std::fmt::Debug,
    {
        assert_instantiated(&canonical.value);
        let (instantiated, _) = self.infer.instantiate_canonical(span, canonical);
        instantiated
    }

    fn prove_trait_ref(&mut self, trait_ref: ty::TraitRef<'tcx>, span: Span) {
        self.prove_predicate(
            ty::Binder::dummy(ty::PredicateKind::Clause(ty::ClauseKind::Trait(
                ty::TraitPredicate { trait_ref, polarity: ty::PredicatePolarity::Positive },
            ))),
            span,
        );
    }

    fn normalize_and_prove_instantiated_predicates(
        &mut self,
        instantiated_predicates: ty::InstantiatedPredicates<'tcx>,
        span: Span,
    ) {
        for (predicate, _) in instantiated_predicates {
            let predicate: ty::Clause<'tcx> = self.normalize(predicate.skip_normalization(), span);
            self.prove_predicate(predicate, span);
        }
    }

    fn prove_predicates(
        &mut self,
        predicates: impl IntoIterator<Item: Upcast<TyCtxt<'tcx>, ty::Predicate<'tcx>> + std::fmt::Debug>,
        span: Span,
    ) {
        for predicate in predicates {
            self.prove_predicate(predicate, span);
        }
    }

    fn prove_predicate(
        &mut self,
        predicate: impl Upcast<TyCtxt<'tcx>, ty::Predicate<'tcx>> + std::fmt::Debug,
        span: Span,
    ) {
        let param_env: ty::ParamEnv<'tcx> = self.infer.param_env;
        let predicate: ty::Predicate<'tcx> = predicate.upcast(self.tcx());
        assert_instantiated(&predicate);
        let result: Result<Scraped<'tcx, ()>, ()> = match predicate.kind().no_bound_vars() {
            Some(ty::PredicateKind::Clause(ty::ClauseKind::WellFormed(term))) => {
                self.prove_well_formed(term, span)
            }
            _ => self.infer.perform(
                param_env.and(type_op::prove_predicate::ProvePredicate { predicate }),
                span,
            ),
        };
        if let Ok(((), constraints)) = result
            && let Some(constraints) = constraints
        {
            self.push_region_constraints(span, constraints);
        }
    }

    // The well-formedness of a type of a nested body of the root includes the where clauses
    // of the root, which hold by assumption: those about a type param are left out of the
    // param env, and the others are in it. Proving one about a type param through an impl
    // would relate regions the generic body never relates, so none of them is proven.
    fn prove_well_formed(
        &mut self,
        term: ty::Term<'tcx>,
        span: Span,
    ) -> Result<Scraped<'tcx, ()>, ()> {
        let tcx: TyCtxt<'tcx> = self.tcx();
        let root: DefId = self.infer.root;
        let param_env: ty::ParamEnv<'tcx> = self.infer.param_env;
        let body_id: LocalDefId = self.infer.cause(span).body_id;
        self.infer.scrape(
            || format!("well-formedness of {term:?}"),
            |ocx| {
                let obligations: PredicateObligations<'tcx> =
                    wf::obligations(ocx.infcx, param_env, body_id, 0, term, span)
                        .ok_or(NoSolution)?;
                ocx.register_obligations(obligations.into_iter().filter(|obligation| {
                    !matches!(
                        *obligation.cause.code(),
                        ObligationCauseCode::WhereClause(origin, _) if is_root_or_parent(tcx, root, origin)
                    )
                }));
                Ok(())
            },
        )
    }

    pub(super) fn normalize<T>(&mut self, value: T, span: Span) -> T
    where
        T: type_op::normalize::Normalizable<'tcx> + std::fmt::Display + Copy + 'tcx,
    {
        assert_instantiated(&value);
        let param_env: ty::ParamEnv<'tcx> = self.infer.param_env;
        match self.infer.perform(param_env.and(type_op::normalize::Normalize { value }), span) {
            Ok((value, constraints)) => {
                if let Some(constraints) = constraints {
                    self.push_region_constraints(span, constraints);
                }
                value
            }
            Err(()) => value,
        }
    }

    fn deeply_normalize<T>(&mut self, value: T, span: Span) -> T
    where
        T: type_op::normalize::Normalizable<'tcx> + std::fmt::Display + Copy + 'tcx,
    {
        assert_instantiated(&value);
        let param_env: ty::ParamEnv<'tcx> = self.infer.param_env;
        match self.infer.perform(param_env.and(type_op::normalize::DeeplyNormalize { value }), span)
        {
            Ok((value, constraints)) => {
                if let Some(constraints) = constraints {
                    self.push_region_constraints(span, constraints);
                }
                value
            }
            Err(()) => value,
        }
    }

    fn custom<R>(
        &mut self,
        span: Span,
        description: &str,
        op: impl FnOnce(
            &rustc_trait_selection::traits::ObligationCtxt<'_, 'tcx>,
        ) -> Result<R, NoSolution>,
    ) -> Result<R, ()>
    where
        R: TypeFoldable<TyCtxt<'tcx>>,
    {
        let (output, constraints) = self.infer.scrape(|| description.to_owned(), op)?;
        if let Some(constraints) = constraints {
            self.push_region_constraints(span, constraints);
        }
        Ok(output)
    }

    fn struct_tail(&mut self, ty: Ty<'tcx>, span: Span) -> Ty<'tcx> {
        assert_instantiated(&ty);
        let tcx: TyCtxt<'tcx> = self.tcx();
        let cause: ObligationCause<'tcx> = self.infer.cause(span);
        if self.infer.next_trait_solver() {
            let param_env: ty::ParamEnv<'tcx> = self.infer.param_env;
            self.custom(span, "normalizing struct tail", |ocx| {
                let structurally_normalize = |ty| {
                    ocx.structurally_normalize_ty(&cause, param_env, Unnormalized::new_wip(ty))
                        .unwrap_or_else(|_| {
                            panic!("struct tail should have been computable, since we computed it in HIR")
                        })
                };
                Ok(tcx.struct_tail_raw(ty, &cause, structurally_normalize, || {}))
            })
            .unwrap_or(ty)
        } else {
            let mut normalize = |ty| self.normalize(ty, span);
            let tail: Ty<'tcx> = tcx.struct_tail_raw(ty, &cause, &mut normalize, || {});
            normalize(tail)
        }
    }

    fn structurally_resolve(&mut self, ty: Ty<'tcx>, span: Span) -> Ty<'tcx> {
        assert_instantiated(&ty);
        if self.infer.next_trait_solver() {
            let param_env: ty::ParamEnv<'tcx> = self.infer.param_env;
            let cause: ObligationCause<'tcx> = self.infer.cause(span);
            self.custom(span, "normalizing struct tail", |ocx| {
                ocx.structurally_normalize_ty(&cause, param_env, Unnormalized::new_wip(ty))
                    .map_err(|_| NoSolution)
            })
            .unwrap_or(ty)
        } else {
            self.normalize(ty, span)
        }
    }

    pub(super) fn ascribe_user_type(
        &mut self,
        mir_ty: Ty<'tcx>,
        user_ty: ty::UserType<'tcx>,
        span: Span,
    ) {
        assert_instantiated(&mir_ty);
        assert_instantiated(&user_ty);
        let param_env: ty::ParamEnv<'tcx> = self.infer.param_env;
        if let Ok(((), constraints)) = self.infer.perform(
            param_env.and(type_op::ascribe_user_type::AscribeUserType { mir_ty, user_ty }),
            span,
        ) && let Some(constraints) = constraints
        {
            self.push_region_constraints(span, constraints);
        }
    }

    fn ascribe_user_type_skip_wf(
        &mut self,
        mir_ty: Ty<'tcx>,
        user_ty: ty::UserType<'tcx>,
        span: Span,
    ) {
        assert_instantiated(&mir_ty);
        assert_instantiated(&user_ty);
        let ty::UserTypeKind::Ty(user_ty) = user_ty.kind else {
            self.mirbug(format!("unexpected user type {user_ty:?} in a signature annotation"));
            return;
        };
        if let ty::Infer(_) = user_ty.kind() {
            let _ = self.eq_types(user_ty, mir_ty, span);
            return;
        }
        let mir_ty: Ty<'tcx> =
            if self.infer.next_trait_solver() { mir_ty } else { self.normalize(mir_ty, span) };
        let cause: ObligationCause<'tcx> = ObligationCause::dummy_with_span(span);
        let param_env: ty::ParamEnv<'tcx> = self.infer.param_env;
        let _ = self.custom(span, "ascribe_user_type_skip_wf", |ocx| {
            let user_ty: Ty<'tcx> =
                ocx.normalize(&cause, param_env, Unnormalized::new_wip(user_ty));
            ocx.eq(&cause, param_env, user_ty, mir_ty).map_err(|_| NoSolution)?;
            Ok(())
        });
    }

    fn check_signature_annotation(&mut self) {
        let mir_def_id: DefId = self.body.source.def_id();
        if !self.tcx().is_closure_like(mir_def_id) {
            return;
        }
        if self.body.tainted_by_errors.is_some() {
            return;
        }
        let user_provided_poly_sig: ty::CanonicalPolyFnSig<'tcx> =
            self.set.typeck[&mir_def_id].closure_sig.expect("a captured closure has its signature");
        let user_provided_poly_sig: ty::CanonicalPolyFnSig<'tcx> = ty::Canonical {
            value: self
                .universal()
                .instantiate(self.tcx(), ty::EarlyBinder::bind(user_provided_poly_sig.value)),
            ..user_provided_poly_sig
        };
        let user_provided_sig: ty::PolyFnSig<'tcx> =
            self.instantiate_canonical(self.body.span, &user_provided_poly_sig);
        let mut user_provided_sig: ty::FnSig<'tcx> = self.infer.instantiate_binder_with_fresh_vars(
            self.body.span,
            BoundRegionConversionTime::FnCall,
            user_provided_sig,
        );
        if let DefiningTy::CoroutineClosure(_, args) = self.universal().defining_ty {
            let tcx: TyCtxt<'tcx> = self.tcx();
            let coroutine: DefId = tcx.coroutine_for_closure(mir_def_id);
            assert!(
                matches!(
                    tcx.coroutine_kind(coroutine),
                    Some(hir::CoroutineKind::Desugared(
                        hir::CoroutineDesugaring::Async | hir::CoroutineDesugaring::Gen,
                        hir::CoroutineSource::Closure
                    ))
                ),
                "this needs to be modified if we're lowering non-async closures"
            );
            let args: ty::CoroutineClosureArgs<TyCtxt<'tcx>> = args.as_coroutine_closure();
            let tupled_upvars_ty: Ty<'tcx> =
                ty::CoroutineClosureSignature::tupled_upvars_by_closure_kind(
                    tcx,
                    args.kind(),
                    Ty::new_tup(tcx, user_provided_sig.inputs()),
                    args.tupled_upvars_ty(),
                    args.coroutine_captures_by_ref_ty(),
                    self.infer.next_region_var(RegionVariableOrigin::Misc(self.body.span)),
                );
            let resume_ty: Ty<'tcx> = self.infer.next_ty_var(self.body.span);
            let yield_ty: Ty<'tcx> = self.infer.next_ty_var(self.body.span);
            let output_ty: Ty<'tcx> = Ty::new_coroutine(
                tcx,
                coroutine,
                ty::CoroutineArgs::new(
                    tcx,
                    ty::CoroutineArgsParts {
                        parent_args: args.parent_args(),
                        kind_ty: Ty::from_coroutine_closure_kind(tcx, args.kind()),
                        return_ty: user_provided_sig.output(),
                        tupled_upvars_ty,
                        resume_ty,
                        yield_ty,
                    },
                )
                .args,
            );
            user_provided_sig = tcx.mk_fn_sig(
                user_provided_sig.inputs().iter().copied(),
                output_ty,
                user_provided_sig.fn_sig_kind,
            );
        }
        let is_coroutine_with_implicit_resume_ty: bool =
            self.tcx().is_coroutine(mir_def_id) && user_provided_sig.inputs().is_empty();
        let arg_decls: Vec<(Ty<'tcx>, Span)> = self
            .body
            .args_iter()
            .skip(1 + usize::from(is_coroutine_with_implicit_resume_ty))
            .map(|local| {
                let decl: &LocalDecl<'tcx> = &self.body.local_decls[local];
                (decl.ty, decl.source_info.span)
            })
            .collect();
        assert_eq!(user_provided_sig.inputs().len(), arg_decls.len());
        for (&user_ty, (arg_ty, span)) in iter::zip(user_provided_sig.inputs(), arg_decls) {
            self.ascribe_user_type_skip_wf(
                arg_ty,
                ty::UserType::new(ty::UserTypeKind::Ty(user_ty)),
                span,
            );
        }
        let output_decl: &LocalDecl<'tcx> = &self.body.local_decls[RETURN_PLACE];
        let (output_ty, output_span) = (output_decl.ty, output_decl.source_info.span);
        self.ascribe_user_type_skip_wf(
            output_ty,
            ty::UserType::new(ty::UserTypeKind::Ty(user_provided_sig.output())),
            output_span,
        );
    }

    fn equate_inputs_and_outputs(&mut self, normalized_inputs_and_output: &[Ty<'tcx>]) {
        let (&normalized_output_ty, normalized_input_tys) =
            normalized_inputs_and_output.split_last().expect("a signature has an output");
        for (argument_index, &normalized_input_ty) in normalized_input_tys.iter().enumerate() {
            assert!(
                argument_index + 1 < self.body.local_decls.len(),
                "found more normalized_input_ty than local_decls"
            );
            let local: Local = Local::from_usize(argument_index + 1);
            let mir_input_ty: Ty<'tcx> = self.body.local_decls[local].ty;
            let mir_input_span: Span = self.body.local_decls[local].source_info.span;
            self.equate_normalized_input_or_output(
                normalized_input_ty,
                mir_input_ty,
                mir_input_span,
            );
        }
        if let Some(mir_yield_ty) = self.body.yield_ty() {
            let yield_span: Span = self.body.local_decls[RETURN_PLACE].source_info.span;
            let yield_ty: Ty<'tcx> =
                self.universal().yield_ty.expect("a body with a yield type is a coroutine");
            self.equate_normalized_input_or_output(yield_ty, mir_yield_ty, yield_span);
        }
        if let Some(mir_resume_ty) = self.body.resume_ty() {
            let resume_span: Span = self.body.local_decls[RETURN_PLACE].source_info.span;
            let resume_ty: Ty<'tcx> =
                self.universal().resume_ty.expect("a body with a resume type is a coroutine");
            self.equate_normalized_input_or_output(resume_ty, mir_resume_ty, resume_span);
        }
        let mir_output_ty: Ty<'tcx> = self.body.return_ty();
        let output_span: Span = self.body.local_decls[RETURN_PLACE].source_info.span;
        self.equate_normalized_input_or_output(normalized_output_ty, mir_output_ty, output_span);
    }

    fn equate_normalized_input_or_output(&mut self, a: Ty<'tcx>, b: Ty<'tcx>, span: Span) {
        if self.infer.next_trait_solver() {
            if self.eq_types(a, b, span).is_err() {
                self.mirbug(format!("equate_normalized_input_or_output: `{a:?}=={b:?}` failed"));
            }
            return;
        }
        let infer: &Infer<'tcx> = self.infer;
        if infer.attempt(|| self.eq_types(a, b, span)).is_err() {
            let b: Ty<'tcx> = self.normalize(b, span);
            if self.eq_types(a, b, span).is_err() {
                self.mirbug(format!("equate_normalized_input_or_output: `{a:?}=={b:?}` failed"));
            }
        }
    }
}

impl<'a, 'tcx> Visitor<'tcx> for TypeChecker<'a, 'tcx> {
    fn visit_span(&mut self, span: Span) {
        if !span.is_dummy() {
            self.last_span = span;
        }
    }

    fn visit_body(&mut self, body: &Body<'tcx>) {
        debug_assert!(std::ptr::eq(self.body, body));
        for (local, local_decl) in body.local_decls.iter_enumerated() {
            self.visit_local_decl(local, local_decl);
        }
        for (block, block_data) in body.basic_blocks.iter_enumerated() {
            let mut location = Location { block, statement_index: 0 };
            for stmt in &block_data.statements {
                self.visit_statement(stmt, location);
                location.statement_index += 1;
            }
            self.visit_terminator(block_data.terminator(), location);
        }
    }

    fn visit_statement(&mut self, stmt: &Statement<'tcx>, location: Location) {
        if self.infer.failed() {
            return;
        }
        self.super_statement(stmt, location);
        let tcx: TyCtxt<'tcx> = self.tcx();
        let span: Span = self.span(location);
        match &stmt.kind {
            StatementKind::Assign(box (place, rv)) => {
                let place_ty: Ty<'tcx> = place.ty(self.body, tcx).ty;
                let place_ty: Ty<'tcx> = self.normalize(place_ty, span);
                let rv_ty: Ty<'tcx> = rv.ty(self.body, tcx);
                let rv_ty: Ty<'tcx> = self.normalize(rv_ty, span);
                if self.sub_types(rv_ty, place_ty, span).is_err() {
                    self.mirbug(format!("bad assignment ({place_ty:?} = {rv_ty:?})"));
                }
                if let Some(annotation_index) = Self::rvalue_user_ty(rv)
                    && self
                        .relate_type_and_user_type(
                            rv_ty,
                            ty::Invariant,
                            &UserTypeProjection { base: annotation_index, projs: vec![] },
                            span,
                        )
                        .is_err()
                {
                    self.mirbug(format!(
                        "bad user type on rvalue ({annotation_index:?} = {rv_ty:?})"
                    ));
                }
                if !tcx.features().unsized_fn_params() {
                    let trait_ref: ty::TraitRef<'tcx> = ty::TraitRef::new(
                        tcx,
                        tcx.require_lang_item(LangItem::Sized, self.last_span),
                        [place_ty],
                    );
                    self.prove_trait_ref(trait_ref, span);
                }
            }
            StatementKind::AscribeUserType(box (place, projection), variance) => {
                let place_ty: Ty<'tcx> = place.ty(self.body, tcx).ty;
                if self
                    .relate_type_and_user_type(
                        place_ty,
                        *variance,
                        projection,
                        stmt.source_info.span,
                    )
                    .is_err()
                {
                    self.mirbug(format!("bad type assert ({place_ty:?} <: {:?})", projection.base));
                }
            }
            StatementKind::Intrinsic(box NonDivergingIntrinsic::Assume(..))
            | StatementKind::FakeRead(..)
            | StatementKind::StorageLive(..)
            | StatementKind::StorageDead(..)
            | StatementKind::Retag { .. }
            | StatementKind::Coverage(..)
            | StatementKind::ConstEvalCounter
            | StatementKind::PlaceMention(..)
            | StatementKind::BackwardIncompatibleDropHint { .. }
            | StatementKind::Nop => {}
            StatementKind::Intrinsic(box NonDivergingIntrinsic::CopyNonOverlapping(..))
            | StatementKind::SetDiscriminant { .. } => {
                self.mirbug("statement not allowed in this MIR phase".to_owned());
            }
        }
    }

    fn visit_terminator(&mut self, term: &Terminator<'tcx>, term_location: Location) {
        if self.infer.failed() {
            return;
        }
        self.super_terminator(term, term_location);
        let tcx: TyCtxt<'tcx> = self.tcx();
        let span: Span = self.span(term_location);
        match &term.kind {
            TerminatorKind::Goto { .. }
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::Return
            | TerminatorKind::CoroutineDrop
            | TerminatorKind::Unreachable
            | TerminatorKind::Drop { .. }
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. }
            | TerminatorKind::InlineAsm { .. }
            | TerminatorKind::SwitchInt { .. }
            | TerminatorKind::Assert { .. } => {}
            TerminatorKind::Call { func, args, .. }
            | TerminatorKind::TailCall { func, args, .. } => {
                let (destination, is_diverging) = match term.kind {
                    TerminatorKind::Call { destination, target, .. } => {
                        (destination, target.is_none())
                    }
                    TerminatorKind::TailCall { .. } => (RETURN_PLACE.into(), false),
                    _ => unreachable!(),
                };
                let func_ty: Ty<'tcx> = func.ty(self.body, tcx);
                let sig: ty::PolyFnSig<'tcx> = match func_ty.kind() {
                    ty::FnDef(..) | ty::FnPtr(..) => func_ty.fn_sig(tcx),
                    _ => {
                        self.mirbug(format!("call to non-function {func_ty:?}"));
                        return;
                    }
                };
                let (unnormalized_sig, _) = tcx.instantiate_bound_regions(sig, |br| {
                    self.infer.next_region_var(RegionVariableOrigin::BoundRegion(
                        term.source_info.span,
                        br.kind,
                        BoundRegionConversionTime::FnCall,
                    ))
                });
                self.prove_predicates(
                    unnormalized_sig.inputs_and_output.iter().map(|ty| {
                        ty::Binder::dummy(ty::PredicateKind::Clause(ty::ClauseKind::WellFormed(
                            ty.into(),
                        )))
                    }),
                    span,
                );
                let sig: ty::FnSig<'tcx> = self.deeply_normalize(unnormalized_sig, span);
                if sig != unnormalized_sig {
                    self.prove_predicates(
                        sig.inputs_and_output.iter().map(|ty| {
                            ty::Binder::dummy(ty::PredicateKind::Clause(
                                ty::ClauseKind::WellFormed(ty.into()),
                            ))
                        }),
                        span,
                    );
                }
                self.check_call_dest(&sig, destination, is_diverging, span);
                self.check_call_inputs(&sig, args, span);
            }
            TerminatorKind::Yield { value, resume_arg, .. } => {
                match self.body.yield_ty() {
                    None => self.mirbug("yield in non-coroutine".to_owned()),
                    Some(yield_ty) => {
                        let value_ty: Ty<'tcx> = value.ty(self.body, tcx);
                        if self.sub_types(value_ty, yield_ty, span).is_err() {
                            self.mirbug(format!(
                                "type of yield value is {value_ty:?}, but the yield type is {yield_ty:?}"
                            ));
                        }
                    }
                }
                match self.body.resume_ty() {
                    None => self.mirbug("yield in non-coroutine".to_owned()),
                    Some(resume_ty) => {
                        let resume_arg_ty: Ty<'tcx> = resume_arg.ty(self.body, tcx).ty;
                        if self.sub_types(resume_ty, resume_arg_ty, span).is_err() {
                            self.mirbug(format!(
                                "type of resume place is {resume_arg_ty:?}, but the resume type is {resume_ty:?}"
                            ));
                        }
                    }
                }
            }
        }
    }

    fn visit_local_decl(&mut self, local: Local, local_decl: &LocalDecl<'tcx>) {
        self.super_local_decl(local, local_decl);
        for user_ty in
            local_decl.user_ty.as_deref().into_iter().flat_map(UserTypeProjections::projections)
        {
            let span: Span = self.user_type_annotations[user_ty.base].span;
            let ty: Ty<'tcx> = if local_decl.is_nonref_binding() {
                local_decl.ty
            } else if let &ty::Ref(_, rty, _) = local_decl.ty.kind() {
                rty
            } else {
                self.mirbug(format!("{local:?} with ref binding has wrong type {}", local_decl.ty));
                return;
            };
            if self.relate_type_and_user_type(ty, ty::Invariant, user_ty, span).is_err() {
                self.mirbug(format!("bad user type on variable {local:?}: {:?}", local_decl.ty));
            }
        }
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        self.super_rvalue(rvalue, location);
        let tcx: TyCtxt<'tcx> = self.tcx();
        let span: Span = self.span(location);
        match rvalue {
            Rvalue::Aggregate(ak, ops) => self.check_aggregate_rvalue(ak, ops, span),
            Rvalue::Repeat(operand, len) => {
                let array_ty: Ty<'tcx> = rvalue.ty(self.body.local_decls(), tcx);
                self.prove_predicate(
                    ty::PredicateKind::Clause(ty::ClauseKind::WellFormed(array_ty.into())),
                    span,
                );
                if len.try_to_target_usize(tcx).is_none_or(|len| len > 1) {
                    match operand {
                        Operand::Copy(..) | Operand::Constant(..) | Operand::RuntimeChecks(_) => {}
                        Operand::Move(place) => {
                            let ty: Ty<'tcx> = place.ty(self.body, tcx).ty;
                            let trait_ref: ty::TraitRef<'tcx> = ty::TraitRef::new(
                                tcx,
                                tcx.require_lang_item(LangItem::Copy, span),
                                [ty],
                            );
                            self.prove_trait_ref(trait_ref, span);
                        }
                    }
                }
            }
            Rvalue::Cast(cast_kind, op, ty) => self.check_cast(*cast_kind, op, *ty, span),
            Rvalue::Ref(region, _, borrowed_place) => {
                self.add_reborrow_constraint(*region, borrowed_place);
            }
            Rvalue::BinaryOp(
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge,
                box (left, right),
            ) => {
                let ty_left: Ty<'tcx> = left.ty(self.body, tcx);
                match ty_left.kind() {
                    ty::RawPtr(_, _) | ty::FnPtr(..) => {
                        let ty_right: Ty<'tcx> = right.ty(self.body, tcx);
                        let common_ty: Ty<'tcx> = self.infer.next_ty_var(span);
                        if self.sub_types(ty_left, common_ty, span).is_err() {
                            self.mirbug(format!("could not equate type variable with {ty_left:?}"));
                        }
                        if self.sub_types(ty_right, common_ty, span).is_err() {
                            self.mirbug(format!(
                                "unexpected comparison types {ty_left:?} and {ty_right:?}"
                            ));
                        }
                    }
                    ty::Int(_) | ty::Uint(_) | ty::Bool | ty::Char | ty::Float(_)
                        if ty_left == right.ty(self.body, tcx) => {}
                    _ => self.mirbug(format!(
                        "unexpected comparison types {ty_left:?} and {:?}",
                        right.ty(self.body, tcx)
                    )),
                }
            }
            Rvalue::WrapUnsafeBinder(op, ty) => {
                let operand_ty: Ty<'tcx> = op.ty(self.body, tcx);
                let ty::UnsafeBinder(binder_ty) = *ty.kind() else {
                    unreachable!();
                };
                let expected_ty: Ty<'tcx> = self.infer.instantiate_binder_with_fresh_vars(
                    span,
                    BoundRegionConversionTime::HigherRankedType,
                    binder_ty.into(),
                );
                if self.sub_types(operand_ty, expected_ty, span).is_err() {
                    self.mirbug(format!("bad unsafe binder {operand_ty:?} <: {expected_ty:?}"));
                }
            }
            Rvalue::Use(_)
            | Rvalue::UnaryOp(_, _)
            | Rvalue::CopyForDeref(_)
            | Rvalue::BinaryOp(..)
            | Rvalue::RawPtr(..)
            | Rvalue::ThreadLocalRef(..)
            | Rvalue::Discriminant(..) => {}
        }
    }

    fn visit_operand(&mut self, op: &Operand<'tcx>, location: Location) {
        self.super_operand(op, location);
        if let Operand::Constant(constant) = op {
            let maybe_uneval: Option<UnevaluatedConst<'tcx>> = match constant.const_ {
                Const::Val(..) | Const::Ty(_, _) => None,
                Const::Unevaluated(uv, _) => Some(uv),
            };
            if let Some(uv) = maybe_uneval
                && uv.promoted.is_none()
            {
                let tcx: TyCtxt<'tcx> = self.tcx();
                let def_id: DefId = uv.def;
                if tcx.def_kind(def_id) == DefKind::InlineConst {
                    let span: Span = self.span(location);
                    self.prove_closure_bounds(def_id, uv.args, span);
                }
            }
        }
    }

    fn visit_const_operand(&mut self, constant: &ConstOperand<'tcx>, location: Location) {
        self.super_const_operand(constant, location);
        let ty: Ty<'tcx> = constant.const_.ty();
        let span: Span = self.span(location);
        if let Some(annotation_index) = constant.user_ty {
            if self
                .relate_type_and_user_type(
                    constant.const_.ty(),
                    ty::Invariant,
                    &UserTypeProjection { base: annotation_index, projs: vec![] },
                    span,
                )
                .is_err()
            {
                self.mirbug(format!("bad constant user type {annotation_index:?} vs {ty:?}"));
            }
        } else {
            let tcx: TyCtxt<'tcx> = self.tcx();
            let maybe_uneval: Option<UnevaluatedConst<'tcx>> = match constant.const_ {
                Const::Ty(_, ct) => match ct.kind() {
                    ty::ConstKind::Unevaluated(uv) => {
                        Some(UnevaluatedConst { def: uv.def, args: uv.args, promoted: None })
                    }
                    _ => None,
                },
                Const::Unevaluated(uv, _) => Some(uv),
                Const::Val(..) => None,
            };
            if let Some(uv) = maybe_uneval {
                if let Some(promoted) = uv.promoted {
                    let promoted_body: &'a Body<'tcx> = &self.promoted[promoted];
                    self.check_promoted(promoted_body);
                    let promoted_ty: Ty<'tcx> = promoted_body.return_ty();
                    if self.eq_types(ty, promoted_ty, span).is_err() {
                        self.mirbug(format!("bad promoted type ({ty:?}: {promoted_ty:?})"));
                    }
                } else {
                    self.ascribe_user_type(
                        constant.const_.ty(),
                        ty::UserType::new(ty::UserTypeKind::TypeOf(
                            uv.def,
                            UserArgs { args: uv.args, user_self_ty: None },
                        )),
                        span,
                    );
                }
            } else if let Some(static_def_id) = constant.check_static_ptr(tcx) {
                let unnormalized_ty: Ty<'tcx> =
                    tcx.type_of(static_def_id).instantiate_identity().skip_norm_wip();
                let normalized_ty: Ty<'tcx> = self.normalize(unnormalized_ty, span);
                let literal_ty: Ty<'tcx> = constant
                    .const_
                    .ty()
                    .builtin_deref(true)
                    .expect("a static pointer is a pointer");
                if self.eq_types(literal_ty, normalized_ty, span).is_err() {
                    self.mirbug(format!("bad static type {constant:?}"));
                }
            } else if let Const::Ty(_, ct) = constant.const_
                && let ty::ConstKind::Param(p) = ct.kind()
            {
                let body_def_id: DefId = self.universal().defining_ty.def_id();
                let const_param: &'tcx ty::GenericParamDef =
                    tcx.generics_of(body_def_id).const_param(p, tcx);
                self.ascribe_user_type(
                    constant.const_.ty(),
                    ty::UserType::new(ty::UserTypeKind::TypeOf(
                        const_param.def_id,
                        UserArgs { args: self.universal().defining_ty.args(), user_self_ty: None },
                    )),
                    span,
                );
            }
            if let ty::FnDef(def_id, args) = *constant.const_.ty().kind() {
                let instantiated_predicates: ty::InstantiatedPredicates<'tcx> =
                    tcx.predicates_of(def_id).instantiate(tcx, args);
                self.normalize_and_prove_instantiated_predicates(instantiated_predicates, span);
                assert_eq!(tcx.trait_impl_of_assoc(def_id), None);
                self.prove_predicates(
                    args.types().map(|ty| ty::ClauseKind::WellFormed(ty.into())),
                    span,
                );
            }
        }
    }

    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        self.super_place(place, context, location);
        let tcx: TyCtxt<'tcx> = self.tcx();
        let place_ty: PlaceTy<'tcx> = place.ty(self.body, tcx);
        if let PlaceContext::NonMutatingUse(NonMutatingUseContext::Copy) = context {
            let trait_ref: ty::TraitRef<'tcx> = ty::TraitRef::new(
                tcx,
                tcx.require_lang_item(LangItem::Copy, self.last_span),
                [place_ty.ty],
            );
            self.prove_trait_ref(trait_ref, self.span(location));
        }
    }

    fn visit_projection_elem(
        &mut self,
        place: PlaceRef<'tcx>,
        elem: PlaceElem<'tcx>,
        context: PlaceContext,
        location: Location,
    ) {
        let tcx: TyCtxt<'tcx> = self.tcx();
        let base_ty: PlaceTy<'tcx> = place.ty(self.body, tcx);
        let span: Span = self.span(location);
        match elem {
            ProjectionElem::Deref
            | ProjectionElem::Index(_)
            | ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. }
            | ProjectionElem::Downcast(..) => {}
            ProjectionElem::Field(field, fty) => {
                let fty: Ty<'tcx> = self.normalize(fty, span);
                let ty: Ty<'tcx> = PlaceTy::field_ty(tcx, base_ty.ty, base_ty.variant_index, field);
                let ty: Ty<'tcx> = self.normalize(ty, span);
                if self.relate_types(ty, context.ambient_variance(), fty, span).is_err() {
                    self.mirbug(format!("bad field access ({ty:?}: {fty:?})"));
                }
            }
            ProjectionElem::OpaqueCast(ty) => {
                let ty: Ty<'tcx> = self.normalize(ty, span);
                if self.relate_types(ty, context.ambient_variance(), base_ty.ty, span).is_err() {
                    self.mirbug(format!("bad opaque cast ({ty:?}: {:?})", base_ty.ty));
                }
            }
            ProjectionElem::UnwrapUnsafeBinder(ty) => {
                let ty::UnsafeBinder(binder_ty) = *base_ty.ty.kind() else {
                    unreachable!();
                };
                let found_ty: Ty<'tcx> = self.infer.instantiate_binder_with_fresh_vars(
                    span,
                    BoundRegionConversionTime::HigherRankedType,
                    binder_ty.into(),
                );
                if self.relate_types(ty, context.ambient_variance(), found_ty, span).is_err() {
                    self.mirbug(format!("bad unsafe binder unwrap ({ty:?}: {found_ty:?})"));
                }
            }
        }
    }
}

impl<'tcx> TypeChecker<'_, 'tcx> {
    fn check_cast(&mut self, cast_kind: CastKind, op: &Operand<'tcx>, ty: Ty<'tcx>, span: Span) {
        let tcx: TyCtxt<'tcx> = self.tcx();
        match cast_kind {
            CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer(target_safety), _) => {
                self.check_reify_fn_pointer_cast(target_safety, op, ty, span);
            }
            CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer(safety), _) => {
                let sig: ty::PolyFnSig<'tcx> =
                    if let ty::Closure(_, args) = op.ty(self.body, tcx).kind() {
                        args.as_closure().sig()
                    } else {
                        self.mirbug("closure fn pointer cast of a non-closure".to_owned());
                        return;
                    };
                let ty_fn_ptr_from: Ty<'tcx> =
                    Ty::new_fn_ptr(tcx, tcx.signature_unclosure(sig, safety));
                if self.sub_types(ty_fn_ptr_from, ty, span).is_err() {
                    self.mirbug(format!("equating {ty_fn_ptr_from:?} with {ty:?} failed"));
                }
            }
            CastKind::PointerCoercion(PointerCoercion::UnsafeFnPointer, _) => {
                let fn_sig: ty::PolyFnSig<'tcx> = op.ty(self.body, tcx).fn_sig(tcx);
                let fn_sig: ty::PolyFnSig<'tcx> = self.normalize(fn_sig, span);
                let ty_fn_ptr_from: Ty<'tcx> = tcx.safe_to_unsafe_fn_ty(fn_sig);
                if self.sub_types(ty_fn_ptr_from, ty, span).is_err() {
                    self.mirbug(format!("equating {ty_fn_ptr_from:?} with {ty:?} failed"));
                }
            }
            CastKind::PointerCoercion(PointerCoercion::Unsize, _) => {
                let trait_ref: ty::TraitRef<'tcx> = ty::TraitRef::new(
                    tcx,
                    tcx.require_lang_item(LangItem::CoerceUnsized, span),
                    [op.ty(self.body, tcx), ty],
                );
                self.prove_trait_ref(trait_ref, span);
            }
            CastKind::PointerCoercion(PointerCoercion::MutToConstPointer, _) => {
                let ty::RawPtr(ty_from, hir::Mutability::Mut) = op.ty(self.body, tcx).kind() else {
                    self.mirbug(format!("unexpected base type for cast {ty:?}"));
                    return;
                };
                let ty::RawPtr(ty_to, hir::Mutability::Not) = ty.kind() else {
                    self.mirbug(format!("unexpected target type for cast {ty:?}"));
                    return;
                };
                if self.sub_types(*ty_from, *ty_to, span).is_err() {
                    self.mirbug(format!("relating {ty_from:?} with {ty_to:?} failed"));
                }
            }
            CastKind::PointerCoercion(PointerCoercion::ArrayToPointer, _) => {
                let ty_from: Ty<'tcx> = op.ty(self.body, tcx);
                let opt_ty_elem_mut: Option<(&Ty<'tcx>, hir::Mutability)> = match ty_from.kind() {
                    ty::RawPtr(array_ty, array_mut) => match array_ty.kind() {
                        ty::Array(ty_elem, _) => Some((ty_elem, *array_mut)),
                        _ => None,
                    },
                    _ => None,
                };
                let Some((ty_elem, ty_mut)) = opt_ty_elem_mut else {
                    self.mirbug(format!("ArrayToPointer cast from unexpected type {ty_from:?}"));
                    return;
                };
                let (ty_to, ty_to_mut) = if let ty::RawPtr(ty_to, ty_to_mut) = ty.kind() {
                    (ty_to, *ty_to_mut)
                } else {
                    self.mirbug(format!("ArrayToPointer cast to unexpected type {ty:?}"));
                    return;
                };
                if ty_to_mut.is_mut() && ty_mut.is_not() {
                    self.mirbug(format!("ArrayToPointer cast from const {ty:?} to mut {ty_to:?}"));
                    return;
                }
                if self.sub_types(*ty_elem, *ty_to, span).is_err() {
                    self.mirbug(format!("relating {ty_elem:?} with {ty_to:?} failed"));
                }
            }
            CastKind::PtrToPtr => self.check_ptr_to_ptr_cast(op, ty, span),
            CastKind::PointerExposeProvenance
            | CastKind::PointerWithExposedProvenance
            | CastKind::IntToInt
            | CastKind::IntToFloat
            | CastKind::FloatToInt
            | CastKind::FloatToFloat
            | CastKind::FnPtrToPtr
            | CastKind::Transmute => {}
            CastKind::Subtype => {
                self.mirbug("CastKind::Subtype shouldn't exist in borrowck".to_owned());
            }
        }
    }

    fn check_reify_fn_pointer_cast(
        &mut self,
        target_safety: hir::Safety,
        op: &Operand<'tcx>,
        ty: Ty<'tcx>,
        span: Span,
    ) {
        let tcx: TyCtxt<'tcx> = self.tcx();
        let src_ty: Ty<'tcx> = op.ty(self.body, tcx);
        let mut src_sig: ty::PolyFnSig<'tcx> = src_ty.fn_sig(tcx);
        if let ty::FnDef(def_id, _) = *src_ty.kind()
            && let ty::FnPtr(_, target_hdr) = *ty.kind()
            && tcx.codegen_fn_attrs(def_id).safe_target_features
            && target_hdr.safety().is_safe()
            && let Some(safe_sig) =
                tcx.adjust_target_feature_sig(def_id, src_sig, self.body.source.def_id())
        {
            src_sig = safe_sig;
        }
        if src_sig.safety().is_safe() && target_safety.is_unsafe() {
            src_sig = tcx.safe_to_unsafe_sig(src_sig);
        }
        if src_sig.has_bound_regions()
            && let ty::FnPtr(target_fn_tys, target_hdr) = *ty.kind()
            && let target_sig = target_fn_tys.with(target_hdr)
            && target_sig.no_bound_vars().is_some()
        {
            let src_sig: ty::FnSig<'tcx> = self.infer.instantiate_binder_with_fresh_vars(
                span,
                BoundRegionConversionTime::HigherRankedType,
                src_sig,
            );
            let src_ty: Ty<'tcx> = Ty::new_fn_ptr(tcx, ty::Binder::dummy(src_sig));
            self.prove_predicate(ty::ClauseKind::WellFormed(src_ty.into()), span);
            let src_ty: Ty<'tcx> = self.normalize(src_ty, span);
            if self.sub_types(src_ty, ty, span).is_err() {
                self.mirbug(format!("equating {ty:?} with {src_sig:?} failed"));
            }
        }
        let src_ty: Ty<'tcx> = Ty::new_fn_ptr(tcx, src_sig);
        self.prove_predicate(ty::ClauseKind::WellFormed(src_ty.into()), span);
        let src_ty: Ty<'tcx> = self.normalize(src_ty, span);
        if self.sub_types(src_ty, ty, span).is_err() {
            self.mirbug(format!("equating {src_ty:?} with {ty:?} failed"));
        }
    }

    fn check_ptr_to_ptr_cast(&mut self, op: &Operand<'tcx>, ty: Ty<'tcx>, span: Span) {
        let tcx: TyCtxt<'tcx> = self.tcx();
        let ty_from: Ty<'tcx> = op.ty(self.body, tcx);
        let Some(CastTy::Ptr(src)) = CastTy::from_ty(ty_from) else {
            unreachable!();
        };
        let Some(CastTy::Ptr(dst)) = CastTy::from_ty(ty) else {
            unreachable!();
        };
        if self.infer.type_is_sized_modulo_regions(self.infer.param_env, dst.ty) {
            let trait_ref: ty::TraitRef<'tcx> = ty::TraitRef::new(
                tcx,
                tcx.require_lang_item(LangItem::Sized, self.last_span),
                [dst.ty],
            );
            self.prove_trait_ref(trait_ref, span);
        } else if let ty::Dynamic(src_tty, src_lt) = *self.struct_tail(src.ty, span).kind()
            && let ty::Dynamic(dst_tty, dst_lt) = *self.struct_tail(dst.ty, span).kind()
        {
            match (src_tty.principal(), dst_tty.principal()) {
                (Some(_), Some(_)) => {
                    let src_obj: Ty<'tcx> = Ty::new_dynamic(
                        tcx,
                        tcx.mk_poly_existential_predicates(
                            &src_tty.without_auto_traits().collect::<Vec<_>>(),
                        ),
                        src_lt,
                    );
                    let dst_obj: Ty<'tcx> = Ty::new_dynamic(
                        tcx,
                        tcx.mk_poly_existential_predicates(
                            &dst_tty.without_auto_traits().collect::<Vec<_>>(),
                        ),
                        dst_lt,
                    );
                    if self.sub_types(src_obj, dst_obj, span).is_err() {
                        self.mirbug(format!("relating {src_obj:?} with {dst_obj:?} failed"));
                    }
                }
                (None, None) => {
                    let src_lt: ty::RegionVid = self.universal().to_region_vid(src_lt);
                    let dst_lt: ty::RegionVid = self.universal().to_region_vid(dst_lt);
                    self.constraints.push(src_lt, dst_lt);
                }
                (None, Some(_)) => {
                    self.mirbug("introducing a principal in a pointer cast".to_owned());
                }
                (Some(_), None) => {
                    self.mirbug("dropping the principal in a pointer cast".to_owned());
                }
            }
        }
    }

    fn check_call_dest(
        &mut self,
        sig: &ty::FnSig<'tcx>,
        destination: Place<'tcx>,
        is_diverging: bool,
        span: Span,
    ) {
        if is_diverging {
            return;
        }
        let tcx: TyCtxt<'tcx> = self.tcx();
        let dest_ty: Ty<'tcx> = destination.ty(self.body, tcx).ty;
        let dest_ty: Ty<'tcx> = self.normalize(dest_ty, span);
        if self.sub_types(sig.output(), dest_ty, span).is_err() {
            self.mirbug(format!("call dest mismatch ({dest_ty:?} <- {:?})", sig.output()));
        }
    }

    fn check_call_inputs(
        &mut self,
        sig: &ty::FnSig<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        span: Span,
    ) {
        if args.len() < sig.inputs().len() || (args.len() > sig.inputs().len() && !sig.c_variadic())
        {
            self.mirbug(format!("call to {sig:?} with wrong # of args"));
        }
        for (n, (fn_arg, op_arg)) in iter::zip(sig.inputs(), args).enumerate() {
            let op_arg_ty: Ty<'tcx> = op_arg.node.ty(self.body, self.tcx());
            let op_arg_ty: Ty<'tcx> = self.normalize(op_arg_ty, span);
            if self.sub_types(op_arg_ty, *fn_arg, span).is_err() {
                self.mirbug(format!("bad arg #{n:?} ({fn_arg:?} <- {op_arg_ty:?})"));
            }
        }
    }

    fn aggregate_field_ty(
        &mut self,
        ak: &AggregateKind<'tcx>,
        field_index: FieldIdx,
        span: Span,
    ) -> Option<Ty<'tcx>> {
        let tcx: TyCtxt<'tcx> = self.tcx();
        match *ak {
            AggregateKind::Adt(adt_did, variant_index, args, _, active_field_index) => {
                let def: ty::AdtDef<'tcx> = tcx.adt_def(adt_did);
                let variant: &ty::VariantDef = def.variant(variant_index);
                let adj_field_index: FieldIdx = active_field_index.unwrap_or(field_index);
                let field: &ty::FieldDef = variant.fields.get(adj_field_index)?;
                Some(self.normalize(field.ty(tcx, args), span))
            }
            AggregateKind::Closure(_, args) => {
                args.as_closure().upvar_tys().get(field_index.as_usize()).copied()
            }
            AggregateKind::Coroutine(_, args) => {
                args.as_coroutine().prefix_tys().get(field_index.as_usize()).copied()
            }
            AggregateKind::CoroutineClosure(_, args) => {
                args.as_coroutine_closure().upvar_tys().get(field_index.as_usize()).copied()
            }
            AggregateKind::Array(ty) => Some(ty),
            AggregateKind::Tuple | AggregateKind::RawPtr(..) => {
                unreachable!("This should have been covered in check_rvalues");
            }
        }
    }

    fn rvalue_user_ty(rvalue: &Rvalue<'tcx>) -> Option<UserTypeAnnotationIndex> {
        match rvalue {
            Rvalue::Use(_)
            | Rvalue::ThreadLocalRef(_)
            | Rvalue::Repeat(..)
            | Rvalue::Ref(..)
            | Rvalue::RawPtr(..)
            | Rvalue::Cast(..)
            | Rvalue::BinaryOp(..)
            | Rvalue::CopyForDeref(..)
            | Rvalue::UnaryOp(..)
            | Rvalue::Discriminant(..)
            | Rvalue::WrapUnsafeBinder(..) => None,
            Rvalue::Aggregate(aggregate, _) => match **aggregate {
                AggregateKind::Adt(_, _, _, user_ty, _) => user_ty,
                AggregateKind::Array(_)
                | AggregateKind::Tuple
                | AggregateKind::Closure(_, _)
                | AggregateKind::Coroutine(_, _)
                | AggregateKind::CoroutineClosure(_, _)
                | AggregateKind::RawPtr(_, _) => None,
            },
        }
    }

    fn check_aggregate_rvalue(
        &mut self,
        aggregate_kind: &AggregateKind<'tcx>,
        operands: &IndexSlice<FieldIdx, Operand<'tcx>>,
        span: Span,
    ) {
        let tcx: TyCtxt<'tcx> = self.tcx();
        self.prove_aggregate_predicates(aggregate_kind, span);
        if *aggregate_kind == AggregateKind::Tuple {
            return;
        }
        if let AggregateKind::RawPtr(..) = aggregate_kind {
            self.mirbug("RawPtr should only be in runtime MIR".to_owned());
            return;
        }
        for (i, operand) in operands.iter_enumerated() {
            let Some(field_ty) = self.aggregate_field_ty(aggregate_kind, i, span) else {
                self.mirbug(format!("accessed field #{} out of range", i.as_u32()));
                continue;
            };
            let operand_ty: Ty<'tcx> = operand.ty(self.body, tcx);
            let operand_ty: Ty<'tcx> = self.normalize(operand_ty, span);
            if self.sub_types(operand_ty, field_ty, span).is_err() {
                self.mirbug(format!("{operand_ty:?} is not a subtype of {field_ty:?}"));
            }
        }
    }

    // The constraints of a borrow `&'a P`: each reference `&'b` dereferenced on the
    // way to `P` must outlive `'a`.
    fn add_reborrow_constraint(
        &mut self,
        borrow_region: ty::Region<'tcx>,
        borrowed_place: &Place<'tcx>,
    ) {
        let tcx: TyCtxt<'tcx> = self.tcx();
        for (base, elem) in borrowed_place.as_ref().iter_projections().rev() {
            match elem {
                ProjectionElem::Deref => {
                    let base_ty: Ty<'tcx> = base.ty(self.body, tcx).ty;
                    match base_ty.kind() {
                        ty::Ref(ref_region, _, mutbl) => {
                            self.constraints.push(ref_region.as_var(), borrow_region.as_var());
                            match mutbl {
                                hir::Mutability::Not => break,
                                hir::Mutability::Mut => {}
                            }
                        }
                        ty::RawPtr(..) => break,
                        ty::Adt(def, _) if def.is_box() => {}
                        _ => {
                            self.mirbug(format!(
                                "unexpected deref ty {base_ty:?} in {borrowed_place:?}"
                            ));
                            return;
                        }
                    }
                }
                ProjectionElem::Field(..)
                | ProjectionElem::Downcast(..)
                | ProjectionElem::OpaqueCast(..)
                | ProjectionElem::Index(..)
                | ProjectionElem::ConstantIndex { .. }
                | ProjectionElem::Subslice { .. }
                | ProjectionElem::UnwrapUnsafeBinder(_) => {}
            }
        }
    }

    fn prove_aggregate_predicates(&mut self, aggregate_kind: &AggregateKind<'tcx>, span: Span) {
        let tcx: TyCtxt<'tcx> = self.tcx();
        let instantiated_predicates: ty::InstantiatedPredicates<'tcx> = match *aggregate_kind {
            AggregateKind::Adt(adt_did, _, args, _, _) => {
                tcx.predicates_of(adt_did).instantiate(tcx, args)
            }
            AggregateKind::Closure(def_id, args)
            | AggregateKind::CoroutineClosure(def_id, args)
            | AggregateKind::Coroutine(def_id, args) => {
                self.prove_closure_bounds(def_id, args, span);
                ty::InstantiatedPredicates::empty()
            }
            AggregateKind::Array(_) | AggregateKind::Tuple | AggregateKind::RawPtr(..) => {
                ty::InstantiatedPredicates::empty()
            }
        };
        self.normalize_and_prove_instantiated_predicates(instantiated_predicates, span);
    }

    fn prove_closure_bounds(&mut self, def_id: DefId, args: GenericArgsRef<'tcx>, span: Span) {
        let tcx: TyCtxt<'tcx> = self.tcx();
        let root_def_id: DefId = self.infer.root;
        self.deferred_closure_requirements.push((def_id, args));
        let typeck_root_args: GenericArgsRef<'tcx> = self.universal().instantiate(
            tcx,
            ty::EarlyBinder::bind(ty::GenericArgs::identity_for_item(tcx, root_def_id)),
        );
        let parent_args: &[ty::GenericArg<'tcx>] = match tcx.def_kind(def_id) {
            DefKind::Closure => &args[..typeck_root_args.len()],
            DefKind::InlineConst => args.as_inline_const().parent_args(),
            other => unreachable!("unexpected item {other:?}"),
        };
        let parent_args: GenericArgsRef<'tcx> = tcx.mk_args(parent_args);
        assert_eq!(typeck_root_args.len(), parent_args.len());
        if self.eq_args(typeck_root_args, parent_args, span).is_err() {
            self.mirbug(format!(
                "could not relate closure to parent {typeck_root_args:?} != {parent_args:?}"
            ));
        }
        // With the parent args related to the root's, the predicates of the nested body are
        // the where clauses of the root, which are not proven (see `prove_well_formed`).
    }
}

// Whether `def` is the root or an item whose generics the root inherits.
fn is_root_or_parent(tcx: TyCtxt<'_>, root: DefId, def: DefId) -> bool {
    let mut item: Option<DefId> = Some(root);
    while let Some(current) = item {
        if current == def {
            return true;
        }
        item = tcx.generics_of(current).parent;
    }
    false
}
