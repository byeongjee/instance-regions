use rustc_middle::mir::Body;
use rustc_middle::ty::{
    self, CanonicalUserTypeAnnotations, EarlyBinder, GenericArgsRef, TyCtxt, TypeVisitableExt,
    TypingEnv,
};

use crate::Error;

// The generic body with the args substituted. The user type annotations keep their
// canonical form, so only their inferred types are instantiated.
pub(crate) fn instantiate<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    args: GenericArgsRef<'tcx>,
    typing_env: TypingEnv<'tcx>,
) -> Result<Body<'tcx>, Error> {
    let mut body: Body<'tcx> = body.clone();
    let annotations: CanonicalUserTypeAnnotations<'tcx> =
        std::mem::take(&mut body.user_type_annotations);
    let mut body: Body<'tcx> =
        tcx.instantiate_and_normalize_erasing_regions(args, typing_env, EarlyBinder::bind(body));
    if body.has_non_region_param() {
        return Err(Error::new("concrete MIR still contains type or const parameters"));
    }
    body.user_type_annotations = annotations
        .into_iter()
        .map(|annotation| ty::CanonicalUserTypeAnnotation {
            inferred_ty: tcx.instantiate_and_normalize_erasing_regions(
                args,
                typing_env,
                EarlyBinder::bind(annotation.inferred_ty),
            ),
            ..annotation
        })
        .collect();
    Ok(body)
}
