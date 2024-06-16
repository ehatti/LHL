From LHL.Core Require Import
  Program
  Specs
  Traces
  Linearizability
  VCompFacts
  RefinesFacts
  Tensor.

From LHL.Util Require Import
  TransUtil
  Tactics.

(* Observational Refinement *)
Theorem lin_obs_ref {E F} : 
  forall (spec' spec : Spec E) (impl : Impl E F) ,
  Lin spec' spec -> 
  layerRefines (spec' :> impl) (spec :> impl).
intros.
apply (mkLayer_monotonic _ _ impl) in H.
assert (H' := layerRefines_VComp_assoc spec idImpl impl).
rewrite obj_VComp_assoc in H'.
assert (ID_EUTT := idImpl_is_identity_l impl).
assert (H'' := eutt_layerRefines spec _ _ ID_EUTT).
eapply layerRefines_trans. eapply layerRefines_trans.
apply H. apply H'. apply H''.
Qed.