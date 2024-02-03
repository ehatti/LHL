From LHL.Util Require Import
  Util
  TransUtil.

From LHL.Core Require Import
  Program
  Specs
  Traces
  Eutt.

From LHL.Core Require Import
  TracesFacts.

(* Basic Refinement Properties *)

Lemma layerRefines_trans {E1 E2 E3 F} :
  forall (lay1 : Layer E1 F) (lay2 : Layer E2 F) (lay3 : Layer E3 F),
    layerRefines lay1 lay2 -> layerRefines lay2 lay3 ->
    layerRefines lay1 lay3.
Proof.
  intros. unfold layerRefines, specRefines in *.
  eapply TransUtil.Incl_trans.
  apply H. apply H0.
Qed.

(* Eutt implies refinement *)

Theorem eutt_layerRefines {E F} : 
  forall (spec : Spec E) (impl impl' : Impl E F), 
  euttImpl ieq impl impl' -> 
  layerRefines (spec :> impl) (spec :> impl').
Admitted.

(* Crucial Refinement Properties *)

Theorem mkLayer_monotonic {E F} :
  forall (spec : Spec E) (spec' : Spec E) (impl : Impl E F),
  specRefines spec' spec -> 
  layerRefines (spec' :> impl) (spec :> impl).
Admitted.

Theorem layerRefines_VComp_assoc {E F G} : 
  forall  (spec : Spec E) (impl : Impl E F) (impl' : Impl F G),
    layerRefines ((overObj (spec :> impl)) :> impl') ((spec :> impl) :|> impl').
Admitted.