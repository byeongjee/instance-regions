use std::cell::RefCell;
use std::fmt::Debug;
use std::ops::Deref;

use rustc_hir::def_id::DefId;
use rustc_infer::infer::canonical::{QueryRegionConstraints, query_response};
use rustc_infer::infer::region_constraints::RegionConstraintData;
use rustc_infer::infer::{
    InferCtxt, NllRegionVariableOrigin, TyCtxtInferExt, TypeOutlivesConstraint,
};
use rustc_middle::traits::ObligationCause;
use rustc_middle::ty::{
    ArgOutlivesPredicate, ParamEnv, ParamEnvAnd, TyCtxt, TypeFoldable, TypeVisitableExt,
    TypingMode, fold_regions,
};
use rustc_span::Span;
use rustc_trait_selection::solve::NoSolution;
use rustc_trait_selection::traits::ObligationCtxt;
use rustc_trait_selection::traits::query::type_op::QueryTypeOp;

use crate::Error;

pub(crate) struct Infer<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) infcx: InferCtxt<'tcx>,
    pub(crate) def: DefId,
    pub(crate) root: DefId,
    pub(crate) param_env: ParamEnv<'tcx>,
    failure: RefCell<Option<Error>>,
}

impl<'tcx> Deref for Infer<'tcx> {
    type Target = InferCtxt<'tcx>;

    fn deref(&self) -> &InferCtxt<'tcx> {
        &self.infcx
    }
}

// rustc reports a delayed bug when the storage of an inference context is dropped
// with uses of opaque types in it, as the analysis of a rejected body leaves them.
impl Drop for Infer<'_> {
    fn drop(&mut self) {
        let _ = self.infcx.take_opaque_types();
    }
}

pub(crate) type Scraped<'tcx, R> = (R, Option<&'tcx QueryRegionConstraints<'tcx>>);

impl<'tcx> Infer<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, def: DefId, root: DefId) -> Self {
        let typing_mode: TypingMode<'tcx> = match def.as_local() {
            Some(local) if tcx.use_typing_mode_borrowck() => TypingMode::borrowck(tcx, local),
            Some(local) => TypingMode::analysis_in_body(tcx, local),
            None => TypingMode::PostAnalysis,
        };
        // The body is instantiated, so no obligation mentions a type or const param, and
        // a clause about one never applies.
        let param_env: ParamEnv<'tcx> = ParamEnv::new(
            tcx.mk_clauses_from_iter(
                tcx.param_env(def)
                    .caller_bounds()
                    .iter()
                    .filter(|clause| !clause.has_non_region_param()),
            ),
        );
        Self {
            tcx,
            infcx: tcx.infer_ctxt().build(typing_mode),
            def,
            root,
            param_env,
            failure: RefCell::new(None),
        }
    }

    pub(crate) fn fail(&self, reason: impl Into<String>) {
        self.failure.borrow_mut().get_or_insert_with(|| Error::new(reason));
    }

    // Runs an attempt whose failure the caller handles, so the failure it records is
    // forgotten, as rustc tolerates a failed relation it retries after normalizing.
    pub(crate) fn attempt<R>(&self, attempt: impl FnOnce() -> R) -> R {
        let failure: Option<Error> = self.failure.borrow().clone();
        let result: R = attempt();
        *self.failure.borrow_mut() = failure;
        result
    }

    pub(crate) fn failed(&self) -> bool {
        self.failure.borrow().is_some()
    }

    pub(crate) fn failure(&self) -> Option<Error> {
        self.failure.borrow().clone()
    }

    pub(crate) fn check(&self) -> Result<(), Error> {
        match self.failure() {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }

    pub(crate) fn cause(&self, span: Span) -> ObligationCause<'tcx> {
        match self.def.as_local() {
            Some(local) => ObligationCause::misc(span, local),
            None => ObligationCause::dummy_with_span(span),
        }
    }

    // Runs `op` and collects the region constraints it registers in the inference context.
    // A failed operation rejects the whole analysis of this body.
    pub(crate) fn scrape<R>(
        &self,
        description: impl FnOnce() -> String,
        op: impl FnOnce(&ObligationCtxt<'_, 'tcx>) -> Result<R, NoSolution>,
    ) -> Result<Scraped<'tcx, R>, ()>
    where
        R: TypeFoldable<TyCtxt<'tcx>>,
    {
        assert!(self.infcx.take_registered_region_obligations().is_empty());
        assert!(self.infcx.take_registered_region_assumptions().is_empty());
        let result: Result<R, ()> = self.infcx.commit_if_ok(|_| {
            let ocx: ObligationCtxt<'_, 'tcx> = ObligationCtxt::new(&self.infcx);
            let value: R = op(&ocx).map_err(|_| ())?;
            if ocx.evaluate_obligations_error_on_ambiguity().is_empty() {
                Ok(value)
            } else {
                Err(())
            }
        });
        let Ok(value) = result else {
            let _ = self.infcx.take_registered_region_obligations();
            let _ = self.infcx.take_registered_region_assumptions();
            let _ = self.infcx.take_and_reset_region_constraints();
            self.fail(format!("type operation failed: {}", description()));
            return Err(());
        };
        let value: R = self.infcx.resolve_vars_if_possible(value);
        // Under `TypingMode::PostAnalysis`, normalizing reveals an opaque type as the
        // hidden type rustc stored, in which the regions of a closure's parent args
        // that the opaque does not capture are erased. Such a region is no universal
        // region of this body, so it becomes a fresh existential variable, as every
        // region of the MIR does when the body is renumbered.
        let value: R = fold_regions(self.tcx, value, |region, _| {
            if region.is_erased() {
                self.infcx.next_nll_region_var(NllRegionVariableOrigin::Existential { name: None })
            } else {
                region
            }
        });
        let obligations: Vec<TypeOutlivesConstraint<'tcx>> =
            self.infcx.take_registered_region_obligations();
        let assumptions: Vec<ArgOutlivesPredicate<'tcx>> =
            self.infcx.take_registered_region_assumptions();
        let data: RegionConstraintData<'tcx> = self.infcx.take_and_reset_region_constraints();
        let constraints: QueryRegionConstraints<'tcx> =
            query_response::make_query_region_constraints(obligations, &data, assumptions);
        let constraints: Option<&'tcx QueryRegionConstraints<'tcx>> =
            (!constraints.is_empty()).then(|| &*self.tcx.arena.alloc(constraints));
        Ok((value, constraints))
    }

    pub(crate) fn perform<Q>(
        &self,
        key: ParamEnvAnd<'tcx, Q>,
        span: Span,
    ) -> Result<Scraped<'tcx, Q::QueryResponse>, ()>
    where
        Q: QueryTypeOp<'tcx>,
    {
        let description = || format!("{key:?}");
        if self.infcx.next_trait_solver() {
            return self
                .scrape(description, |ocx| Q::perform_locally_with_next_solver(ocx, key, span));
        }
        let mut extra: QueryRegionConstraints<'tcx> = QueryRegionConstraints::default();
        let (output, constraints) = self.scrape(description, |ocx| {
            let (output, _, obligations, _) =
                Q::fully_perform_into(key, &self.infcx, &mut extra, span)?;
            ocx.register_obligations(obligations);
            Ok(output)
        })?;
        if let Some(constraints) = constraints {
            extra.constraints.extend(constraints.constraints.iter().copied());
            extra.assumptions.extend(constraints.assumptions.iter().copied());
        }
        let constraints: Option<&'tcx QueryRegionConstraints<'tcx>> =
            (!extra.is_empty()).then(|| &*self.tcx.arena.alloc(extra));
        Ok((output, constraints))
    }
}

pub(crate) fn assert_instantiated<'tcx, T: TypeVisitableExt<TyCtxt<'tcx>> + Debug>(value: &T) {
    assert!(
        !value.has_non_region_param(),
        "the analysis of an instance reaches a type or const parameter in {value:?}"
    );
}
