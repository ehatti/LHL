From LHL.Core Require Import
  Logic
  Specs
  Traces
  Linearizability
  Program
  TracesFacts.

From LHL.Util Require Import
  TransUtil
  Tactics
  Util.

From Coq Require Import
  Program.Equality
  Lists.List
  Relations.Relation_Operators
  Logic.FunctionalExtensionality
  Logic.PropExtensionality
  Arith.PeanoNat.

Import ListNotations.
Open Scope list_scope.

From Paco Require Import
  paco.

Ltac psplit :=
match goal with
| [ |- ReltCompose ?P ?Q ?s ?ρ ?t ?σ ] =>
    do 2 eexists; split
| [ |- PrecCompose ?P ?Q ?s ?ρ ] =>
    do 2 eexists; split
| [ |- _ ] => fail "Cannot split on this goal"
end.

Ltac pdestruct H :=
match type of H with
| ReltCompose ?P ?Q ?s ?ρ ?t ?σ => do 3 destruct H
| PrecCompose ?P ?Q ?s ?ρ => do 3 destruct H
| TIdle ?i ?s ?ρ => destruct H
| TInvoke ?impl ?i ?Ret ?m ?s ?ρ ?t ?σ => do 2 destruct H
| InvokeAny ?impl ?i ?s ?ρ ?t ?σ => do 2 destruct H
| _ => fail "Cannot destruct this hypothesis"
end.

Ltac psimpl :=
repeat lazymatch goal with
| [ H : prComp ?P ?R ?s ?ρ ?t ?σ |- _ ] => destruct H
| [ H : ReltCompose ?P ?Q ?s ?ρ ?t ?σ |- _] => destruct H
| [ H : PrecCompose ?P ?Q ?s ?ρ |- _] => destruct H
| [ H : ?P /\ ?Q |- _ ] => destruct H
| [ H : exists x, ?P |- _ ] => destruct H
| [ H : TInvoke ?impl ?i ?A ?l ?s ?ρ ?t ?σ |- _ ] => destruct H
| [ H : ReltToPrec ?R ?s ?ρ |- _ ] => destruct H
| [ H : StReltToRelt ?Q ?s ?ρ ?t ?σ |- _ ] => destruct H
end;
simpl in *;
subst;
repeat lazymatch goal with
| [ H : ?A, H' : ?A |- _] => clear H'
end.

(* Ltac steps :=
repeat match goal with
| [ H : InterStep ?i ?st ?e ?st' |- _ ] => dependent destruction H
| [ H : Step ?impl ?st ?ev ?st' |- _ ] => simpl in H; destruct H;  dependent destruction H
end;
simpl in *. *)

Section lemmas.

Context {E F VE VF} {R : @Relt E F VE VF}.

Lemma reltCompIdLeft {Q : Relt VE VF} :
  Q ->> id = Q.
extensionality s.
extensionality ρ.
extensionality t.
extensionality σ.
apply propositional_extensionality.
unfold ReltCompose.
firstorder.
subst.
easy.
Qed.

Lemma reltCompIdRight {Q : Relt VE VF} :
  id ->> Q = Q.
extensionality s.
extensionality ρ.
extensionality t.
extensionality σ.
apply propositional_extensionality.
unfold ReltCompose.
firstorder.
subst.
easy.
Qed.

Lemma precCompStable {P Q} :
  Stable R P ->
  Stable R Q ->
  Stable R (P <<- Q).
intros.
unfold Stable, stablePrec, sub, subPrec.
intros.
do 2 pdestruct H1.
psplit.
exact H1.
destruct H0.
apply H4.
psplit.
exact H3.
easy.
Qed.

Lemma reltCompStable {Q S} :
  Stable R Q ->
  Stable R S ->
  Stable R (Q ->> S).
intros.
unfold Stable, stableRelt, sub, subRelt.
split.
intros.
destruct H.
destruct H0.
pdestruct H1.
pdestruct H4.
psplit.
apply H.
psplit.
exact H1.
exact H4.
easy.
intros.
do 2 pdestruct H1.
psplit.
exact H1.
destruct H0.
apply H4.
psplit.
exact H3.
easy.
Qed.

Lemma precStabilizedStable {P} :
  (R ->> R ==> R) ->
  Stable R (P <<- R).
intros.
unfold Stable, stablePrec, sub, subPrec.
intros.
do 2 pdestruct H0.
psplit.
exact H0.
apply H.
psplit.
exact H2.
easy.
Qed.

Lemma reltStabilizedStable {Q} :
  (R ->> R ==> R) ->
  Stable R (R ->> Q ->> R).
intros.
unfold Stable, stableRelt, sub, subRelt.
split.
intros.
psimpl.
psplit.
apply H.
psplit.
exact H0.
exact H1.
psplit.
exact H2.
easy.
intros.
psimpl.
psplit.
exact H0.
psplit.
exact H2.
apply H.
psplit.
exact H3.
easy.
Qed.

Lemma rtpStable {Q : Relt VE VF} :
  Stable R Q ->
  Stable R (ReltToPrec Q).
unfold Stable, stableRelt, stablePrec, ReltToPrec.
intros.
unfold sub, subPrec.
intros.
psimpl.
exists x1, x2.
apply H1.
psplit.
exact H0.
easy.
Qed.

End lemmas.

Lemma precReltCompAssoc {E F VE VF} {P : @Prec E F VE VF} Q S :
  P <<- (Q ->> S) = P <<- Q <<- S.
extensionality s.
extensionality ρ.
Admitted.

Lemma reltCompAssoc {E F} {VE : Spec E} {VF : Spec F} {R1 R2 R3 : Relt VE VF} :
  (R1 ->> R2) ->> R3 = R1 ->> R2 ->> R3.
extensionality s.
extensionality ρ.
extensionality t.
extensionality σ.
apply propositional_extensionality.
unfold ReltCompose.
firstorder; destruct_all.
repeat econstructor.
exact H.
exact H1.
easy.
repeat econstructor.
exact H.
exact H0.
easy.
Qed.

Lemma rtcTrans {E F VE VF} {R : @Relt E F VE VF} :
  (RTC R ->> RTC R) ==> RTC R.
unfold sub, subRelt, ReltCompose.
intros.
do 3 destruct H.
induction H.
easy.
econstructor.
exact H.
apply IHRTC.
easy.
Qed.

Lemma rtcTransTac {E F VE VF} {R : @Relt E F VE VF} {s ρ t σ r τ} :
  RTC R s ρ t σ ->
  RTC R t σ r τ ->
  RTC R s ρ r τ.
intros.
eapply rtcTrans.
psplit.
exact H.
easy.
Qed.

Lemma extendRtcLeft {E F VE VF} {R : @Relt E F VE VF} {s ρ t σ r τ} :
  R s ρ t σ ->
  RTC R t σ r τ ->
  RTC R s ρ r τ.
intros.
eapply RTCStep.
exact H.
easy.
Qed.

Lemma extendRtcRight {E F VE VF} {R : @Relt E F VE VF} {s ρ t σ r τ} :
  RTC R s ρ t σ ->
  R t σ r τ ->
  RTC R s ρ r τ.
intros.
eapply rtcTrans.
psplit.
exact H.
eapply RTCStep.
exact H0.
constructor.
Qed.

Axiom undef:forall{a},a.

CoFixpoint weakenSafe {E F VE VF i R G P P' A Q C} :
  (P' ==> P) ->
  SafeProg (E:=E) (F:=F) (VE:=VE) (VF:=VF) (A:=A) i R G P C Q ->
  SafeProg i R G P' C Q.
intros.
destruct H0.
{
  econstructor.
  unfold sub, subRelt. intros.
  apply H0.
  apply H.
  exact H1.
}
{
  econstructor.
  exact H0.
  exact H1.
  unfold Commit. intros.
  unfold ReltToPrec in H4. destruct_all.
  apply H in H4.
  apply H2.
  unfold ReltToPrec. repeat eexists.
  exact H4.
  exact H5.
  exact H6.
  exact H7.
  intros.
  specialize (H3 v).
  destruct_all.
  split.
  unfold Commit.
  intros.
  apply H3.
  do 5 destruct H5.
  repeat econstructor.
  apply H.
  exact H5.
  exact H9.
  exact H6.
  exact H7.
  exact H8.
  apply weakenSafe with (P:= P ->> QI ->> QR v).
  unfold sub, subRelt, ReltCompose.
  intros.
  destruct_all.
  repeat econstructor.
  apply H.
  exact H5.
  exact H6.
  exact H7.
  exact H4.
}
{
  econstructor.
  apply weakenSafe with (P:=P).
  exact H.
  exact H0.
}
Qed.


Ltac simpl_rely :=
repeat lazymatch goal with
| [ H : ?R ?s ?ρ ?t ?σ, H0 : RTC ?R ?t ?σ ?r ?τ |- _] =>
  let H2 := fresh in
  assert (H2 : RTC R s ρ r τ);
  try (eapply (extendRtcLeft H H0));
  move H2 after H;
  clear H H0 t σ
| [ H : RTC ?R ?s ?ρ ?t ?σ, H0 : ?R ?t ?σ ?r ?τ |- _] =>
  let H2 := fresh in
  assert (H2 : RTC R s ρ r τ);
  try (eapply (extendRtcRight H H0));
  move H2 after H;
  clear H H0 t σ
| [ H : RTC ?R ?s ?ρ ?t ?σ, H0 : RTC ?R ?t ?σ ?r ?τ |- _] =>
  let H2 := fresh in
  assert (H2 : RTC R s ρ r τ);
  try (eapply (rtcTransTac H H0));
  move H2 after H;
  clear H H0 t σ
end.

Definition poss_to_mod {F} {VF : Spec F} (ρ : Poss VF) : InterState F VF :=
  (
    fun i =>
      match PCalls ρ i with
      | CallIdle => Idle
      | CallPoss m => Cont m (Bind m Return)
      | CallDone m =>
        match PRets ρ i with
        | RetIdle => UCall m m Return
        | RetPoss m v => Cont m (Return v)
        end
      end,
    PState ρ
  ).

Record LHLState {E F}
  {VE : Spec E} {VF : Spec F}
  {M : Impl E F}
  {R G : ThreadName -> Relt VE VF}
  {Ps : ThreadName -> forall A, F A -> Prec VE VF}
  {Qs : ThreadName -> forall A, F A -> Post VE VF A}
  {s : InterState F VE} {ρs : PossSet VF}
:= MkLHLState {
  PrecSt : ThreadName -> Relt VE VF;
  all_prec : forall i, ReltToPrec (PrecSt i) s ρs;
  all_safe : forall i, match fst s i with
  | Idle =>
    TIdle i s ρs /\
    forall A (m : F A), Ps i A m s ρs
  | Cont m p =>
    SafeProg i (R i) (G i) (PrecSt i) p (fun v => Qs i _ m v ->> PrecToRelt (Returned i m))
  | UCall om um k =>
    exists QR, forall v,
      Commit i (G i) (PrecSt i) (RetEv um v) (PrecSt i ->> QR v) /\
      SafeProg i (R i) (G i) (PrecSt i ->> QR v) (k v) (fun v => Qs i _ om v ->> PrecToRelt (Returned i om))
  end
}.
Arguments LHLState {E F VE VF} M R G Ps Qs s ρs.

Inductive Lift {A : Type} : Prop :=
| lift : A -> Lift.
Arguments Lift : clear implicits.

Lemma swapEx {A B} {P : A -> B -> Prop} :
  (exists x y, P x y) ->
  (exists y x, P x y).
intros.
destruct_all.
exists x0, x.
easy.
Qed.

Definition invPoss {A F} {VF : Spec F} i (ρ : Poss VF) (m : F A) : Poss VF := {|
  PState := ρ.(PState);
  PCalls j := if i =? j then CallPoss m else PCalls ρ j;
  PRets j := if i =? j then RetIdle else PRets ρ j
|}.

Theorem soundness {E F} (lay : Layer E F) VF R G Ps Qs :
  VerifyImpl lay.(USpec) VF R G Ps lay.(LImpl) Qs ->
  Lin (overObj lay) VF.
intros.
destruct_all.
unfold Lin, KConc.
destruct lay. simpl in *.
rename USpec into VE. rename LImpl into M.
unfold specRefines, Incl, IsTraceOfSpec.
repeat rewrite projInterSteps. simpl.
intros. destruct_all. subst.
cut (
  exists st q,
    projOver x0 = projOver q /\
    InterSteps idImpl (allIdle, Init VF) q st
).
{
  intros.
  destruct_all.
  exists x1, x2.
  repeat split; try easy.
  dependent destruction H3.
  left. easy.
  do 2 dependent destruction H3.
  unfold ThreadStep in H3. simpl in H3.
  destruct ev, l; simpl in *.
  dependent destruction H3.
  right. repeat econstructor.
}
cut (
  exists σs,
    (exists σ, σs σ) /\
    forall σ, σs σ ->
      exists ρ, eq initPoss ρ /\
        exists q,
          projOver x0 = projOver q /\
          InterSteps (spec:=VF) idImpl (poss_to_mod ρ) q (poss_to_mod σ)
).
{
  intros.
  destruct_all.
  exists (poss_to_mod x2).
  apply H3 in H0. clear H3.
  destruct_all.
  subst.
  exists x4.
  easy.
}
cut (
  forall s ρs t e,
  (exists ρ, ρs ρ) ->
  LHLState M R G Ps Qs s ρs ->
  InterStep M s e t ->
  exists σs,
    (exists σ, σs σ) /\
    Lift (LHLState M R G Ps Qs t σs) /\
    forall σ, σs σ ->
      exists ρ, ρs ρ /\
        exists p,
          projOver p = projOver (cons e nil) /\
          InterSteps idImpl (poss_to_mod ρ) p (poss_to_mod σ)
).
clear H2.
{
  intros.
  assert (exists ρ, initPoss (VF:=VF) = ρ) by repeat econstructor.
  assert (LHLState M R G Ps Qs (allIdle, Init VE) (eq initPoss)).
  {
    apply MkLHLState with
      (PrecSt:=fun i s ρ t σ => forall A m, prComp (Ps i A m) id s ρ t σ).
    admit.
    admit.
  }
  generalize dependent (@allIdle E F, Init VE).
  generalize dependent (eq (initPoss (VF:=VF))).
  intro ρs. generalize dependent ρs.
  induction x0; simpl; intros; destruct_all.
  {
    exists ρs.
    split. exists x0. easy.
    intros.
    exists σ. split. easy.
    exists []. repeat constructor.
  }
  {
    dependent destruction H1.
    specialize (H0 p ρs st'' a).
    rename X into H4.
    apply H0 in H4.
    2:{ exists x1. easy. }
    2: easy.
    destruct_all.
    specialize (IHx0 x).
    destruct H5. rename X into H5.
    apply IHx0 in H5. destruct_all.
    2:{ exists x2. easy. }
    2: easy.
    exists x3. split. exists x4. easy.
    intros.
    apply H7 in H8. clear H7. destruct_all.
    apply H6 in H7. clear H6. destruct_all.
    exists x7. split. easy.
    exists (x8 ++ x6).
    split.
    {
      rewrite projOver_app.
      rewrite H7.
      destruct a, l; simpl; f_equal; easy.
    }
    {
      unfold InterSteps.
      rewrite <- Steps_app.
      exists (poss_to_mod x5).
      easy.
    }
  }
}
(* step refinement *)
clear H2 H1 x0 x.
intros.
rename X into H2.
unfold InterStep, ThreadsStep, StateStep in H1. destruct_all.
dependent destruction H1. unfold ThreadStep in H1.
destruct e. simpl in *.
destruct l; destruct ev.
destruct e.
{
  dependent destruction H1.
  assert (H2' := H2). move H2' at top.
  destruct H2.
  specialize (all_safe0 n). rewrite H1 in all_safe0.
  dependent destruction all_safe0.
  unfold Commit in H3. eapply H3 in H7.
  2: apply all_prec0.
  2:{ unfold differ_pointwise. symmetry. apply H6. easy. }
  2:{ econstructor. exact H5. easy. }
  destruct_all.
  exists x1. split. exists x2. easy.
  split.
  admit.
  {
    intros.
    apply H8 in H11. destruct_all.
    exists x3. split. easy. clear H11.
    induction H12.
    {
      exists nil.
      repeat constructor; easy.
    }
    {
      destruct_all.
      admit.
    }
  }
}
{

}
{

}
{
  dependent destruction H1.
  assert (H2' := H2). move H2' at top. destruct H2.
  specialize (all_safe0 n). rewrite H1 in all_safe0.
  exists (fun σ => exists ρ, ρs ρ /\ σ = invPoss n ρ m).
  repeat split.
  {
    exists (invPoss n x0 m), x0. easy.
  }
  {
    eapply MkLHLState with
      (PrecSt:=fun i =>
        if i =? n then
          prComp (Ps i _ m <<- TInvoke M i _ m) id
        else
          PrecSt0 i ->> TInvoke M i _ m).
    {
      intros.
      dec_eq_nats i n.
      {
        rewrite eqb_id.
        do 3 eexists.
        2: split; easy.
        destruct_all.
        psplit.
        apply H5.
        unfold TInvoke.
        split. easy.
        split. econstructor. econstructor; easy. easy.
        split. intros. destruct_all. subst.
        exists x1. easy.
        split. intros. destruct H2.
        apply H7 in H6. easy.
        split. intros. destruct_all. subst.
        simpl. rewrite eqb_id. easy.
        intros. destruct_all. subst. simpl.
        rewrite eqb_id. easy.
      }
      {
        rewrite eqb_nid. 2: easy.
        do 3 eexists.
        admit.
      }
    }
    {
      intros.
    }
  }
  {
    intros. destruct_all. subst.
    exists x1. split. easy.
    exists [(n, OEvent (CallEv m))].
    simpl. split. easy.
    unfold InterStep, ThreadsStep. simpl.
    unfold TIdle in H5. destruct_all.
    apply H7 in H2. destruct_all.
    econstructor. 2: constructor.
    unfold InterStep, ThreadsStep. simpl.
    split. 2: easy.
    econstructor.
    {
      simpl.
      rewrite eqb_id, H2.
      econstructor; easy.
    }
    {
      simpl. intros.
      rewrite eqb_nid. easy.
      easy.
    }
  }
}
{

}