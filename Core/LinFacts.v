From LHL.Core Require Import
  Program
  ProgramFacts
  Specs
  Traces
  Linearizability
  VCompFacts
  RefinesFacts
  Tensor
  TensorFacts.

From LHL.Util Require Import
  TransUtil
  Tactics.

(* Observational Refinement *)
Theorem lin_obs_ref {T E F} : 
  forall (spec' spec : Spec T E) (impl : Impl E F) ,
  Lin spec' spec -> 
  layerRefines (spec' :> impl) (spec :> impl).
Proof.
intros.
apply (mkLayer_monotonic _ _ impl) in H.
assert (H' := layerRefines_VComp_assoc spec idImpl impl).
rewrite obj_VComp_assoc in H'.
assert (ID_EUTT := idImpl_is_identity_l impl).
assert (H'' := eutt_layerRefines spec _ _ ID_EUTT).
eapply layerRefines_trans. eapply layerRefines_trans.
apply H. apply H'. apply H''.
Qed.

(* Locality *)
Theorem locality {T E F} :
  forall (specE specE' : Spec T E) (specF specF' : Spec T F) ,
  Lin specE' specE /\ Lin specF' specF <-> Lin (tensorSpec specE' specF') (tensorSpec specE specF).
Proof.
  intros.
  unfold Lin, KConc.
  constructor.
  - intros. destruct H.  
    assert (H1 := tensor_monotonic _ _ _ _ H H0).
    assert (H2 := tensor_layer_funct_l specE specF idImpl idImpl).
    unfold tensorLayer in H2. simpl in H2.
    assert (H3 := implEq_refines _ _ _ (tensorSpec specE specF) _ _ (@tensor_neutral E F)).
    eapply specRefines_trans. eapply specRefines_trans. 
    apply H1. apply H2. apply H3.
  - intros. 
    eapply tensor_monotonic_inv.
    assert (H1 := implEq_refines _ _ _ (tensorSpec specE specF) _ _ (implEqSym _ _ _ _ (@tensor_neutral E F))).
    assert (H2 := tensor_layer_funct_r specE specF idImpl idImpl); unfold tensorLayer in H2; simpl in H2. 
    eapply specRefines_trans. eapply specRefines_trans.
    apply H. apply H1. apply H2. 
Qed.