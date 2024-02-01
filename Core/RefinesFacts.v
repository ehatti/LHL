From LHL.Core Require Import
  Program
  Specs
  Traces.

From LHL.Core Require Import
  TracesFacts.

Theorem obj_VComp_assoc {E F G} :
  forall (spec : Spec E) (impl : Impl E F) (impl' : Impl F G),
  ((spec :> impl) :|> impl') = (spec :> impl |> impl').
Proof.
    auto.
Qed.

Theorem mkLayer_monotonic {E F} :
  forall (spec spec' : Spec E) (impl : Impl E F),
    specRefines spec spec' -> 
    layerRefines (spec :> impl) (spec' :> impl).
Proof.
  intros. unfold layerRefines. unfold specRefines. unfold TransUtil.Incl. intros.
  induction a.
  destruct H0. destruct H0. apply nil_IsTraceOfSpec.