use std::iter;

use preborrowck_mir::{RecordedMir, typing_env};
use rustc_data_structures::fx::FxIndexMap;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_hir::lang_items::LangItem;
use rustc_index::IndexVec;
use rustc_infer::infer::NllRegionVariableOrigin;
use rustc_middle::ty::{
    self, GenericArgs, GenericArgsRef, InlineConstArgs, InlineConstArgsParts, RegionVid, Ty,
    TyCtxt, TypeFoldable, fold_regions,
};

use super::infer::{Infer, assert_instantiated};
use crate::Error;

// The type whose generic parameters are in scope in the body, with its regions
// renumbered to universal region variables.
#[derive(Clone, Copy, Debug)]
pub(crate) enum DefiningTy<'tcx> {
    Closure(DefId, GenericArgsRef<'tcx>),
    Coroutine(DefId, GenericArgsRef<'tcx>),
    CoroutineClosure(DefId, GenericArgsRef<'tcx>),
    FnDef(DefId, GenericArgsRef<'tcx>),
    Const(DefId, GenericArgsRef<'tcx>),
    InlineConst(DefId, GenericArgsRef<'tcx>),
}

impl<'tcx> DefiningTy<'tcx> {
    pub(crate) fn def_id(self) -> DefId {
        match self {
            DefiningTy::Closure(def_id, _)
            | DefiningTy::Coroutine(def_id, _)
            | DefiningTy::CoroutineClosure(def_id, _)
            | DefiningTy::FnDef(def_id, _)
            | DefiningTy::Const(def_id, _)
            | DefiningTy::InlineConst(def_id, _) => def_id,
        }
    }

    pub(crate) fn args(self) -> GenericArgsRef<'tcx> {
        match self {
            DefiningTy::Closure(_, args)
            | DefiningTy::Coroutine(_, args)
            | DefiningTy::CoroutineClosure(_, args)
            | DefiningTy::FnDef(_, args)
            | DefiningTy::Const(_, args)
            | DefiningTy::InlineConst(_, args) => args,
        }
    }
}

// The free regions of a body: `'static`, the regions of the enclosing bodies,
// the regions of the body's own signature, and the region of the body itself.
pub(crate) struct Universal<'tcx> {
    indices: FxIndexMap<ty::Region<'tcx>, RegionVid>,
    pub(crate) fr_static: RegionVid,
    pub(crate) fr_fn_body: RegionVid,
    first_extern_index: usize,
    first_local_index: usize,
    num_universals: usize,
    pub(crate) defining_ty: DefiningTy<'tcx>,
    pub(crate) unnormalized_output_ty: Ty<'tcx>,
    pub(crate) unnormalized_input_tys: &'tcx [Ty<'tcx>],
    pub(crate) yield_ty: Option<Ty<'tcx>>,
    pub(crate) resume_ty: Option<Ty<'tcx>>,
}

impl<'tcx> Universal<'tcx> {
    pub(crate) fn new(
        infer: &Infer<'tcx>,
        def: DefId,
        instance_args: GenericArgsRef<'tcx>,
        set: &RecordedMir<'tcx>,
    ) -> Result<Self, Error> {
        let tcx: TyCtxt<'tcx> = infer.tcx;
        assert_eq!(infer.num_region_vars(), 0, "the universal regions are the first variables");
        let fr_static: RegionVid =
            infer.next_nll_region_var(NllRegionVariableOrigin::FreeRegion).as_var();
        let first_extern_index: usize = infer.num_region_vars();
        let defining_ty: DefiningTy<'tcx> = defining_ty(infer, def, instance_args, set)?;
        let mut indices: FxIndexMap<ty::Region<'tcx>, RegionVid> =
            compute_indices(tcx, def, fr_static, defining_ty);
        let first_local_index: usize = if tcx.is_typeck_child(def) {
            for_each_late_bound_region_in_recursive_scope(tcx, tcx.parent(def), set, |r| {
                let vid: RegionVid =
                    infer.next_nll_region_var(NllRegionVariableOrigin::FreeRegion).as_var();
                assert_eq!(indices.insert(r, vid), None);
            });
            infer.num_region_vars()
        } else {
            first_extern_index
        };
        let bound_inputs_and_output: ty::Binder<'tcx, &'tcx ty::List<Ty<'tcx>>> =
            compute_inputs_and_output(infer, &indices, def, defining_ty)?;
        for (idx, bound_var) in bound_inputs_and_output.bound_vars().iter().enumerate() {
            if let ty::BoundVariableKind::Region(kind) = bound_var {
                let kind: ty::LateParamRegionKind =
                    ty::LateParamRegionKind::from_bound(ty::BoundVar::from_usize(idx), kind);
                let r: ty::Region<'tcx> = ty::Region::new_late_param(tcx, def, kind);
                let vid: RegionVid =
                    infer.next_nll_region_var(NllRegionVariableOrigin::FreeRegion).as_var();
                assert_eq!(indices.insert(r, vid), None);
            }
        }
        let (inputs_and_output, _) = tcx.instantiate_bound_regions(bound_inputs_and_output, |br| {
            let kind: ty::LateParamRegionKind =
                ty::LateParamRegionKind::from_bound(br.var, br.kind);
            let liberated: ty::Region<'tcx> = ty::Region::new_late_param(tcx, def, kind);
            ty::Region::new_var(tcx, indices[&liberated])
        });
        let (unnormalized_output_ty, unnormalized_input_tys) = inputs_and_output
            .split_last()
            .expect("the inputs and output of a body end with the output");
        let fr_fn_body: RegionVid =
            infer.next_nll_region_var(NllRegionVariableOrigin::FreeRegion).as_var();
        let num_universals: usize = infer.num_region_vars();
        let (resume_ty, yield_ty): (Option<Ty<'tcx>>, Option<Ty<'tcx>>) = match defining_ty {
            DefiningTy::Coroutine(_, args) => {
                (Some(args.as_coroutine().resume_ty()), Some(args.as_coroutine().yield_ty()))
            }
            _ => (None, None),
        };
        assert_instantiated(&defining_ty.args());
        assert_instantiated(&inputs_and_output);
        assert_instantiated(&resume_ty);
        assert_instantiated(&yield_ty);
        Ok(Universal {
            indices,
            fr_static,
            fr_fn_body,
            first_extern_index,
            first_local_index,
            num_universals,
            defining_ty,
            unnormalized_output_ty: *unnormalized_output_ty,
            unnormalized_input_tys,
            yield_ty,
            resume_ty,
        })
    }

    pub(crate) fn instantiate<T: TypeFoldable<TyCtxt<'tcx>>>(
        &self,
        tcx: TyCtxt<'tcx>,
        value: ty::EarlyBinder<'tcx, T>,
    ) -> T {
        value.instantiate(tcx, self.defining_ty.args()).skip_norm_wip()
    }

    pub(crate) fn is_universal_region(&self, r: RegionVid) -> bool {
        (0..self.num_universals).contains(&r.index())
    }

    pub(crate) fn is_local_free_region(&self, r: RegionVid) -> bool {
        (self.first_local_index..self.num_universals).contains(&r.index())
    }

    // An external region is a region of an enclosing body.
    pub(crate) fn is_external_region(&self, r: RegionVid) -> bool {
        (self.first_extern_index..self.first_local_index).contains(&r.index())
    }

    // The original form of a universal region that has one: `'static`, an early-bound
    // region of the typeck root, or a liberated late-bound region.
    pub(crate) fn external_name(&self, r: RegionVid) -> Option<ty::Region<'tcx>> {
        self.indices.iter().find(|&(_, &vid)| vid == r).map(|(&region, _)| region)
    }

    pub(crate) fn num_global_and_external_regions(&self) -> usize {
        self.first_local_index
    }

    pub(crate) fn universal_regions_iter(&self) -> impl Iterator<Item = RegionVid> + 'static {
        (0..self.num_universals).map(RegionVid::from_usize)
    }

    pub(crate) fn implicit_region_bound(&self) -> RegionVid {
        self.fr_fn_body
    }

    // Converts a free region, a `'static` region, or a region variable of this body
    // into its region variable. Placeholders are converted by the constraint set.
    pub(crate) fn to_region_vid(&self, r: ty::Region<'tcx>) -> RegionVid {
        match r.kind() {
            ty::ReVar(..) => r.as_var(),
            ty::ReError(_) => self.fr_static,
            _ => *self
                .indices
                .get(&r)
                .unwrap_or_else(|| panic!("cannot convert `{r:?}` to a region variable")),
        }
    }

    // The values of the free regions of a closure type, in the order of the universal
    // regions of the closure body, so that its region requirements can be applied here.
    pub(crate) fn closure_mapping(
        tcx: TyCtxt<'tcx>,
        closure_args: GenericArgsRef<'tcx>,
        expected_num_vars: usize,
        closure_def_id: DefId,
        set: &RecordedMir<'tcx>,
    ) -> IndexVec<RegionVid, ty::Region<'tcx>> {
        let mut region_mapping: IndexVec<RegionVid, ty::Region<'tcx>> =
            IndexVec::with_capacity(expected_num_vars);
        region_mapping.push(tcx.lifetimes.re_static);
        tcx.for_each_free_region(&closure_args, |fr| {
            region_mapping.push(fr);
        });
        for_each_late_bound_region_in_recursive_scope(tcx, tcx.parent(closure_def_id), set, |r| {
            region_mapping.push(r);
        });
        assert_eq!(
            region_mapping.len(),
            expected_num_vars,
            "index vec had unexpected number of variables"
        );
        region_mapping
    }
}

fn replace_free_regions_with_nll_infer_vars<'tcx, T: TypeFoldable<TyCtxt<'tcx>>>(
    infer: &Infer<'tcx>,
    value: T,
) -> T {
    fold_regions(infer.tcx, value, |_, _| {
        infer.next_nll_region_var(NllRegionVariableOrigin::FreeRegion)
    })
}

fn defining_ty<'tcx>(
    infer: &Infer<'tcx>,
    def: DefId,
    instance_args: GenericArgsRef<'tcx>,
    set: &RecordedMir<'tcx>,
) -> Result<DefiningTy<'tcx>, Error> {
    let tcx: TyCtxt<'tcx> = infer.tcx;
    match tcx.def_kind(def) {
        DefKind::Closure | DefKind::Fn | DefKind::AssocFn => {
            let defining_ty: Ty<'tcx> = tcx.instantiate_and_normalize_erasing_regions(
                instance_args,
                typing_env(def),
                tcx.type_of(def),
            );
            let defining_ty: Ty<'tcx> =
                replace_free_regions_with_nll_infer_vars(infer, defining_ty);
            match *defining_ty.kind() {
                ty::Closure(def_id, args) => Ok(DefiningTy::Closure(def_id, args)),
                ty::Coroutine(def_id, args) => Ok(DefiningTy::Coroutine(def_id, args)),
                ty::CoroutineClosure(def_id, args) => {
                    Ok(DefiningTy::CoroutineClosure(def_id, args))
                }
                ty::FnDef(def_id, args) => Ok(DefiningTy::FnDef(def_id, args)),
                _ => Err(Error::new(format!(
                    "`{}` has the unexpected defining type `{defining_ty}`",
                    tcx.def_path_str(def)
                ))),
            }
        }
        DefKind::Const { .. }
        | DefKind::AssocConst { .. }
        | DefKind::AnonConst
        | DefKind::Static { .. } => {
            let args: GenericArgsRef<'tcx> =
                ty::EarlyBinder::bind(GenericArgs::identity_for_item(tcx, def))
                    .instantiate(tcx, instance_args)
                    .skip_norm_wip();
            Ok(DefiningTy::Const(def, replace_free_regions_with_nll_infer_vars(infer, args)))
        }
        DefKind::InlineConst => {
            let root: DefId = tcx.typeck_root_def_id(def);
            let ty: Ty<'tcx> = set.typeck[&def]
                .inline_const_ty
                .expect("a captured inline const has its defining type");
            let parent_args: GenericArgsRef<'tcx> =
                ty::EarlyBinder::bind(GenericArgs::identity_for_item(tcx, root))
                    .instantiate(tcx, instance_args)
                    .skip_norm_wip();
            let ty: Ty<'tcx> =
                ty::EarlyBinder::bind(ty).instantiate(tcx, instance_args).skip_norm_wip();
            let args: GenericArgsRef<'tcx> =
                InlineConstArgs::new(tcx, InlineConstArgsParts { parent_args, ty }).args;
            let args: GenericArgsRef<'tcx> = replace_free_regions_with_nll_infer_vars(infer, args);
            Ok(DefiningTy::InlineConst(def, args))
        }
        kind => Err(Error::unavailable(format!(
            "`{}` of kind {kind:?} is not analyzed",
            tcx.def_path_str(def)
        ))),
    }
}

// The early-bound regions in scope, keyed by their original form, in the order of the
// regions in the args of the defining type.
fn compute_indices<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: DefId,
    fr_static: RegionVid,
    defining_ty: DefiningTy<'tcx>,
) -> FxIndexMap<ty::Region<'tcx>, RegionVid> {
    let root: DefId = tcx.typeck_root_def_id(def);
    let identity_args: GenericArgsRef<'tcx> = GenericArgs::identity_for_item(tcx, root);
    let renumbered_args: GenericArgsRef<'tcx> = defining_ty.args();
    assert!(renumbered_args.len() >= identity_args.len());
    iter::once((tcx.lifetimes.re_static, fr_static))
        .chain(iter::zip(
            identity_args.regions(),
            renumbered_args.regions().map(rustc_middle::ty::Region::as_var),
        ))
        .collect()
}

fn compute_inputs_and_output<'tcx>(
    infer: &Infer<'tcx>,
    indices: &FxIndexMap<ty::Region<'tcx>, RegionVid>,
    def: DefId,
    defining_ty: DefiningTy<'tcx>,
) -> Result<ty::Binder<'tcx, &'tcx ty::List<Ty<'tcx>>>, Error> {
    let tcx: TyCtxt<'tcx> = infer.tcx;
    match defining_ty {
        DefiningTy::Closure(def_id, args) => {
            assert_eq!(def, def_id);
            closure_inputs_and_output(tcx, def_id, args)
        }
        DefiningTy::Coroutine(def_id, args) => {
            assert_eq!(def, def_id);
            let resume_ty: Ty<'tcx> = args.as_coroutine().resume_ty();
            let output: Ty<'tcx> = args.as_coroutine().return_ty();
            let coroutine_ty: Ty<'tcx> = Ty::new_coroutine(tcx, def_id, args);
            Ok(ty::Binder::dummy(tcx.mk_type_list(&[coroutine_ty, resume_ty, output])))
        }
        DefiningTy::CoroutineClosure(def_id, args) => {
            assert_eq!(def, def_id);
            Ok(coroutine_closure_inputs_and_output(tcx, def_id, args))
        }
        DefiningTy::FnDef(def_id, args) => {
            Ok(fn_def_inputs_and_output(infer, indices, def, def_id, args))
        }
        DefiningTy::Const(def_id, args) => {
            assert_eq!(def, def_id);
            let ty: Ty<'tcx> = tcx.type_of(def_id).instantiate(tcx, args).skip_norm_wip();
            let ty: Ty<'tcx> = fold_to_region_vids(tcx, indices, ty);
            Ok(ty::Binder::dummy(tcx.mk_type_list(&[ty])))
        }
        DefiningTy::InlineConst(def_id, args) => {
            assert_eq!(def, def_id);
            let ty: Ty<'tcx> = args.as_inline_const().ty();
            Ok(ty::Binder::dummy(tcx.mk_type_list(&[ty])))
        }
    }
}

// The bound variables of a closure signature followed by the region of the closure
// environment, and that region.
fn closure_env_region<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig_bound_vars: &'tcx ty::List<ty::BoundVariableKind<'tcx>>,
) -> (&'tcx ty::List<ty::BoundVariableKind<'tcx>>, ty::Region<'tcx>) {
    let bound_vars: &'tcx ty::List<ty::BoundVariableKind<'tcx>> = tcx
        .mk_bound_variable_kinds_from_iter(
            sig_bound_vars
                .iter()
                .chain(iter::once(ty::BoundVariableKind::Region(ty::BoundRegionKind::ClosureEnv))),
        );
    let br: ty::BoundRegion = ty::BoundRegion {
        var: ty::BoundVar::from_usize(bound_vars.len() - 1),
        kind: ty::BoundRegionKind::ClosureEnv,
    };
    (bound_vars, ty::Region::new_bound(tcx, ty::INNERMOST, br))
}

fn closure_inputs_and_output<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: GenericArgsRef<'tcx>,
) -> Result<ty::Binder<'tcx, &'tcx ty::List<Ty<'tcx>>>, Error> {
    let closure_sig: ty::PolyFnSig<'tcx> = args.as_closure().sig();
    let inputs_and_output: ty::Binder<'tcx, &'tcx ty::List<Ty<'tcx>>> =
        closure_sig.inputs_and_output();
    let (bound_vars, env_region) = closure_env_region(tcx, inputs_and_output.bound_vars());
    let closure_ty: Ty<'tcx> = tcx.closure_env_ty(
        Ty::new_closure(tcx, def_id, args),
        args.as_closure().kind(),
        env_region,
    );
    let (&output, tuplized_inputs) =
        inputs_and_output.skip_binder().split_last().expect("a closure signature has an output");
    assert_eq!(tuplized_inputs.len(), 1, "multiple closure inputs");
    let &ty::Tuple(inputs) = tuplized_inputs[0].kind() else {
        return Err(Error::new(format!("closure inputs not a tuple: {:?}", tuplized_inputs[0])));
    };
    Ok(ty::Binder::bind_with_vars(
        tcx.mk_type_list_from_iter(iter::once(closure_ty).chain(inputs).chain(iter::once(output))),
        bound_vars,
    ))
}

fn coroutine_closure_inputs_and_output<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: GenericArgsRef<'tcx>,
) -> ty::Binder<'tcx, &'tcx ty::List<Ty<'tcx>>> {
    let closure_args: ty::CoroutineClosureArgs<TyCtxt<'tcx>> = args.as_coroutine_closure();
    let closure_sig: ty::Binder<'tcx, ty::CoroutineClosureSignature<TyCtxt<'tcx>>> =
        closure_args.coroutine_closure_sig();
    let (bound_vars, env_region) = closure_env_region(tcx, closure_sig.bound_vars());
    let closure_kind: ty::ClosureKind = closure_args.kind();
    let closure_ty: Ty<'tcx> =
        tcx.closure_env_ty(Ty::new_coroutine_closure(tcx, def_id, args), closure_kind, env_region);
    let inputs: &'tcx ty::List<Ty<'tcx>> =
        closure_sig.skip_binder().tupled_inputs_ty.tuple_fields();
    let output: Ty<'tcx> = closure_sig.skip_binder().to_coroutine_given_kind_and_upvars(
        tcx,
        closure_args.parent_args(),
        tcx.coroutine_for_closure(def_id),
        closure_kind,
        env_region,
        closure_args.tupled_upvars_ty(),
        closure_args.coroutine_captures_by_ref_ty(),
    );
    ty::Binder::bind_with_vars(
        tcx.mk_type_list_from_iter(iter::once(closure_ty).chain(inputs).chain(iter::once(output))),
        bound_vars,
    )
}

// The signature of a function; a C-variadic function has a `VaList` input after the
// declared inputs.
fn fn_def_inputs_and_output<'tcx>(
    infer: &Infer<'tcx>,
    indices: &FxIndexMap<ty::Region<'tcx>, RegionVid>,
    def: DefId,
    def_id: DefId,
    args: GenericArgsRef<'tcx>,
) -> ty::Binder<'tcx, &'tcx ty::List<Ty<'tcx>>> {
    let tcx: TyCtxt<'tcx> = infer.tcx;
    let sig: ty::PolyFnSig<'tcx> = tcx.fn_sig(def_id).instantiate(tcx, args).skip_norm_wip();
    let sig: ty::PolyFnSig<'tcx> = fold_to_region_vids(tcx, indices, sig);
    let inputs_and_output: ty::Binder<'tcx, &'tcx ty::List<Ty<'tcx>>> = sig.inputs_and_output();
    if !tcx.fn_sig(def_id).skip_binder().c_variadic() {
        return inputs_and_output;
    }
    let va_list_did: DefId = tcx.require_lang_item(LangItem::VaList, tcx.def_span(def));
    let region: ty::Region<'tcx> = infer.next_nll_region_var(NllRegionVariableOrigin::FreeRegion);
    let va_list_ty: Ty<'tcx> =
        tcx.type_of(va_list_did).instantiate(tcx, &[region.into()]).skip_norm_wip();
    inputs_and_output.map_bound(|tys| {
        let (output_ty, input_tys) = tys.split_last().expect("a signature has an output");
        tcx.mk_type_list_from_iter(input_tys.iter().copied().chain([va_list_ty, *output_ty]))
    })
}

// Replaces the free regions of a signature by their universal region variables.
fn fold_to_region_vids<'tcx, T: TypeFoldable<TyCtxt<'tcx>>>(
    tcx: TyCtxt<'tcx>,
    indices: &FxIndexMap<ty::Region<'tcx>, RegionVid>,
    value: T,
) -> T {
    fold_regions(tcx, value, |region, _| match region.kind() {
        ty::ReVar(..) => region,
        ty::ReError(_) => tcx.lifetimes.re_static,
        _ => ty::Region::new_var(
            tcx,
            *indices
                .get(&region)
                .unwrap_or_else(|| panic!("cannot convert `{region:?}` to a region variable")),
        ),
    })
}

// Visits the liberated late-bound regions of `def` and of all of its enclosing
// bodies up to the typeck root.
pub(crate) fn for_each_late_bound_region_in_recursive_scope<'tcx>(
    tcx: TyCtxt<'tcx>,
    mut def: DefId,
    set: &RecordedMir<'tcx>,
    mut f: impl FnMut(ty::Region<'tcx>),
) {
    loop {
        for_each_late_bound_region_in_item(tcx, def, set, &mut f);
        if tcx.is_typeck_child(def) {
            def = tcx.parent(def);
        } else {
            break;
        }
    }
}

fn for_each_late_bound_region_in_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: DefId,
    set: &RecordedMir<'tcx>,
    mut f: impl FnMut(ty::Region<'tcx>),
) {
    let bound_vars: &'tcx ty::List<ty::BoundVariableKind<'tcx>> = match tcx.def_kind(def) {
        DefKind::Fn | DefKind::AssocFn => tcx.mk_bound_variable_kinds(&set.typeck[&def].bound_vars),
        DefKind::Closure => {
            let ty: Ty<'tcx> = tcx.type_of(def).instantiate_identity().skip_norm_wip();
            match *ty.kind() {
                ty::Closure(_, args) => args.as_closure().sig().bound_vars(),
                ty::CoroutineClosure(_, args) => {
                    args.as_coroutine_closure().coroutine_closure_sig().bound_vars()
                }
                ty::Coroutine(_, _) | ty::Error(_) => return,
                _ => unreachable!("unexpected type for closure: {ty}"),
            }
        }
        _ => return,
    };
    for (idx, bound_var) in bound_vars.iter().enumerate() {
        if let ty::BoundVariableKind::Region(kind) = bound_var {
            let kind: ty::LateParamRegionKind =
                ty::LateParamRegionKind::from_bound(ty::BoundVar::from_usize(idx), kind);
            f(ty::Region::new_late_param(tcx, def, kind));
        }
    }
}
