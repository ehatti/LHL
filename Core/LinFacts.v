From LHL.Core Require Import
  Program
  ProgramFacts
  Specs
  Traces
  Linearizability
  VCompFacts
  (* RefinesFacts *)
  Tensor
  TensorFacts
  TracesFacts.

From LHL.Util Require Import
  TransUtil
  Tactics.

Require Import Coq.Program.Equality.

Ltac ddestruct H := dependent destruction H.

Lemma idSteps_eq_proj {T E} :
  forall (p : Trace (ThreadLEvent T E E)) s t,
  Steps (ThreadsStep idImpl) s p t ->
  projOver p = projUnderThr p.
Admitted.

Lemma swap_ex {A B} {P : A -> B -> Prop} :
  (exists x y, P x y) ->
  (exists y x, P x y).
intros.
destruct H as [x [y H]].
now exists y, x.
Qed.

(* Observational Refinement *)
Theorem obs_ref {T E F} : 
  forall (spec' spec : Spec T E) (impl : Impl E F) ,
  Lin spec' spec -> 
  layerRefines (spec' :> impl) (spec :> impl).
Proof.
  unfold Lin, layerRefines, specRefines.
  unfold Incl, IsTraceOfSpec, KConc.
  intros spec' spec impl ref p steps.
  destruct steps as [st' steps'].
  rewrite decompOverObj.
  rewrite decompOverObj in steps'.
  destruct steps' as [q' [eq_over [steps' [ths_steps is_obj_tr']]]].
  assert (exists st, Steps (Step spec') (Init spec') (projUnderThr q') st).
  { now exists (snd st'). }
  apply ref in H.
  destruct H as [st lin_steps].
  rewrite decompOverObj in lin_steps.
  destruct lin_steps as [q [proj_lay_eq [steps [lin_ths_steps is_obj_tr]]]].
  cbn in *. clear ref. subst.
  exists (fst st', snd st), q'. cbn.
  repeat (easy || constructor).
  clear is_obj_tr is_obj_tr'.
  move ths_steps before lin_ths_steps.
  move st at top. move proj_lay_eq at bottom.
  move steps' before steps.
  rewrite proj_lay_eq in *.
  destruct st' as [ths' st'].
  destruct st as [ths st].
  cbn in *.

(* Locality *)
Theorem locality {E F} :
  forall (specE specE' : Spec E) (specF specF' : Spec F) ,
  Lin specE' specE /\ Lin specF' specF <-> Lin (tensorSpec specE' specF') (tensorSpec specE specF).
Proof.
  intros.
  unfold Lin, KConc.
  constructor.
  - intros. destruct H.  
    assert (H1 := tensor_monotonic _ _ _ _ H H0).
    assert (H2 := tensor_layer_funct_l specE specF idImpl idImpl).
    unfold tensorLayer in H2. simpl in H2.
    assert (H3 := implEq_refines _ _ (tensorSpec specE specF) _ _ (@tensor_neutral E F)).
    eapply specRefines_trans. eapply specRefines_trans. 
    apply H1. apply H2. apply H3.
  - intros. 
    eapply tensor_monotonic_inv.
    assert (H1 := implEq_refines _ _ (tensorSpec specE specF) _ _ (implEqSym _ _ _ _ (@tensor_neutral E F))).
    assert (H2 := tensor_layer_funct_r specE specF idImpl idImpl); unfold tensorLayer in H2; simpl in H2. 
    eapply specRefines_trans. eapply specRefines_trans.
    apply H. apply H1. apply H2. 
Qed.