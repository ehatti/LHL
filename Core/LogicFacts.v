From LHL.Core Require Import
  Logic
  Specs
  Traces
  Linearizability
  Program
  LogicPaco
  TracesFacts.

From LHL.Util Require Import
  TransUtil
  Tactics
  Util.

From Coq Require Import
  Program.Equality
  Lists.List
  Relations.Relation_Operators
  Relations.Operators_Properties
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
| [ |- prComp ?P ?Q ?s ?p ?t ?q ] =>
  split
| [ |- _ ] => fail "Cannot split on this goal"
end.

Ltac pdestruct H :=
match type of H with
| ReltCompose ?P ?Q ?s ?ρ ?t ?σ => do 3 destruct H
| PrecCompose ?P ?Q ?s ?ρ => do 3 destruct H
| TIdle ?i ?s ?ρ => destruct H
| TInvoke ?impl ?i ?Ret ?m ?s ?ρ ?t ?σ => do 2 destruct H
| InvokeAny ?impl ?i ?s ?ρ ?t ?σ => do 2 destruct H
| ReltToPrec ?R ?s ?ρ => do 2 destruct H; pdestruct H
| _ => fail "Cannot destruct this hypothesis"
end.

Ltac psimpl :=
repeat lazymatch goal with
| [ H : prComp ?P ?R ?s ?ρ ?t ?σ |- _ ] => destruct H
| [ H : ReltCompose ?P ?Q ?s ?ρ ?t ?σ |- _] => destruct H
| [ H : PrecCompose ?P ?Q ?s ?ρ |- _] => destruct H
| [ H : ?P /\ ?Q |- _ ] => destruct H
| [ H : exists x, ?P |- _ ] => destruct H
| [ H : ReltToPrec ?R ?s ?ρ |- _ ] => destruct H
| [ H : PrecToRelt ?R ?s ?ρ ?t ?σ |- _ ] => destruct H
end;
simpl in *;
subst;
repeat lazymatch goal with
| [ H : ?A, H' : ?A |- _] => clear H'
end.

(* Ltac steps :=
repeat match goal with
| [ H : InterStep ?i ?st ?e ?st' |- _ ] => ddestruct H
| [ H : Step ?impl ?st ?ev ?st' |- _ ] => simpl in H; destruct H;  ddestruct H
end;
simpl in *. *)

Section lemmas.

Context {T E F VE VF} {R : @Relt T E F VE VF}.

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
apply H0.
exists x, x0. easy.
Qed.

Lemma reltCompStable {Q S} :
  Stable R S ->
  Stable R (Q ->> S).
intros.
unfold Stable, stableRelt, sub, subRelt.
intros. psimpl.
exists x1, x2. split. easy.
apply H. exists x, x0. easy.
Qed.

End lemmas.

Lemma rtp_prId {T E F} {VE : Spec T E} {VF : Spec T F} :
  forall (P : Prec VE VF) Q S,
  ReltToPrec (prComp P Q ->> S) = P <<- Q <<- S.
intros.
extensionality s. extensionality ρs.
apply propositional_extensionality.
unfold ReltToPrec, prComp. firstorder.
subst.
repeat psplit.
exact H.
exact H1.
easy.
repeat eexists.
exact H.
exact H1.
easy.
Qed.

Lemma precReltCompAssoc {T E F VE VF} {P : @Prec T E F VE VF} Q S :
  P <<- (Q ->> S) = P <<- Q <<- S.
extensionality s.
extensionality ρ.
apply propositional_extensionality.
unfold PrecCompose, ReltCompose.
split; intros; destruct_all; repeat econstructor.
exact H.
exact H0.
easy.
exact H.
exact H1.
easy.
Qed.

Lemma reltCompAssoc {T E F} {VE : Spec T E} {VF : Spec T F} {R1 R2 R3 : Relt VE VF} :
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


Lemma precCompAssoc {T E F} {VE : Spec T E} {VF : Spec T F} {P} {R1 R2 : Relt VE VF} :
  P <<- R1 <<- R2 = P <<- (R1 ->> R2).
extensionality s. extensionality ρ.
apply propositional_extensionality.
unfold PrecCompose, ReltCompose.
split; intros; destruct_all.
repeat econstructor.
exact H.
exact H1.
easy.
repeat econstructor.
exact H.
exact H0.
easy.
Qed.

Lemma rtcTrans {T E F VE VF} {R : @Relt T E F VE VF} :
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

Lemma rtcTransTac {T E F VE VF} {R : @Relt T E F VE VF} {s ρ t σ r τ} :
  RTC R s ρ t σ ->
  RTC R t σ r τ ->
  RTC R s ρ r τ.
intros.
eapply rtcTrans.
psplit.
exact H.
easy.
Qed.

Lemma extendRtcLeft {T E F VE VF} {R : @Relt T E F VE VF} {s ρ t σ r τ} :
  R s ρ t σ ->
  RTC R t σ r τ ->
  RTC R s ρ r τ.
intros.
eapply RTCStep.
exact H.
easy.
Qed.

Lemma extendRtcRight {T E F VE VF} {R : @Relt T E F VE VF} {s ρ t σ r τ} :
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

Lemma weakenCommitPre {T E F} {VE : Spec T E} {VF : Spec T F} {i G Q P' e} :
  forall P : Relt VE VF,
  P' ==> P ->
  Commit i G P e Q ->
  Commit i G P' e Q.
unfold Commit. intros.
apply H0.
unfold ReltToPrec in *.
destruct_all.
exists x, x0.
apply H.
easy.
easy.
easy.
easy.
Qed.

Lemma weakenCommit {T E F} {VE : Spec T E} {VF : Spec T F} {i G P Q' e} :
  forall Q : Relt VE VF,
  Q ==> Q' ->
  Commit i G P e Q ->
  Commit i G P e Q'.
unfold Commit. intros.
eapply H0 in H4.
2: exact H1. 2: easy. 2: easy.
destruct_all.
exists x. split.
exists x0. easy.
split.
easy.
split.
apply H. easy.
easy.
Qed.

CoFixpoint weakenSafe {T E F VE VF i R G P P' A Q C m} :
  (P' ==> P) ->
  SafeProg (T:=T) (E:=E) (F:=F) (VE:=VE) (VF:=VF) (A:=A) i R G P m C Q ->
  SafeProg i R G P' m C Q.
intros.
destruct H0.
{
  econstructor.
  unfold sub, subRelt. intros.
  {
    unfold ReturnStep. intros.
    eapply H0.
    unfold ReltToPrec in *. psimpl.
    exists x, x0.
    apply H. easy.
    exact H3.
    easy.
    easy.
  }
  apply H1.
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
  exact H0.
  unfold SilentStep. intros. apply H1.
  unfold ReltToPrec in *. destruct_all.
  exists x, x0.
  apply H. easy. easy. easy.
  eapply weakenSafe with (P:= P ->> QS).
  unfold sub, subRelt. intros.
  pdestruct H3.
  apply H in H3.
  psplit.
  exact H3.
  easy.
  easy.
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

Definition p2m {T F} {VF : Spec T F} (ρ : Poss VF) : InterState F VF :=
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

Record LHLState {T E F}
  {VE : Spec T E} {VF : Spec T F}
  {M : Impl E F}
  {R G : Name T -> Relt VE VF}
  {Ps : Name T -> forall A, F A -> Prec VE VF}
  {Qs : Name T -> forall A, F A -> Post VE VF A}
  {s : InterState F VE} {ρs : PossSet VF}
:= MkLHLState {
  all_safe : forall i, match fst s i with
  | Idle =>
    TIdle i s ρs /\
    forall A (m : F A), Ps i A m s ρs
  | Cont m p =>
    exists Is,
      SafeProg i (R i) (G i) ((prComp (Ps i _ m) (TInvoke M i _ m)) ->> Is) m p (fun v => Qs i _ m v ->> PrecToRelt (Returned i m v)) /\
      (Ps i _ m <<- TInvoke M i _ m <<- Is) s ρs /\
      (Is ->> R i) ==> Is
  | UCall om um k =>
    exists Is QR, forall v,
      Commit i (G i) ((prComp (Ps i _ om) (TInvoke M i _ om)) ->> Is) (RetEv um v) (QR v) /\
      SafeProg i (R i) (G i) ((prComp (Ps i _ om) (TInvoke M i _ om)) ->> Is ->> QR v) om (k v) (fun v => Qs i _ om v ->> PrecToRelt (Returned i om v)) /\
      (Ps i _ om <<- TInvoke M i _ om <<- Is) s ρs /\
      (QR v ->> R i) ==> QR v /\
      (Is ->> R i) ==> Is
  end
}.
Arguments LHLState {T E F VE VF} M R G Ps Qs s ρs.

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

Definition invPoss {T A F} {VF : Spec T F} i (ρ : Poss VF) (m : F A) : Poss VF := {|
  PState := ρ.(PState);
  PCalls j := if i =? j then CallPoss m else PCalls ρ j;
  PRets j := if i =? j then RetIdle else PRets ρ j
|}.

Definition retPoss {T F} {VF : Spec T F} i (ρ : Poss VF) : Poss VF := {|
  PState := ρ.(PState);
  PCalls j := if i =? j then CallIdle else PCalls ρ j;
  PRets j := if i =? j then RetIdle else PRets ρ j
|}.

Theorem soundness {T E F} (lay : Layer T E F) VF R G Ps Qs :
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
  ddestruct H3.
  left. easy.
  do 2 ddestruct H3.
  unfold ThreadStep in H3. simpl in H3.
  destruct ev, l; simpl in *.
  ddestruct H3.
  right. repeat econstructor.
}
cut (
  exists σs,
    (exists σ, σs σ) /\
    forall σ, σs σ ->
      exists ρ, eq initPoss ρ /\
        exists q,
          projOver x0 = projOver q /\
          InterSteps (spec:=VF) idImpl (p2m ρ) q (p2m σ)
).
{
  intros.
  destruct_all.
  exists (p2m x2).
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
          InterSteps idImpl (p2m ρ) p (p2m σ)
).
clear H2.
{
  intros.
  assert (exists ρ, initPoss (VF:=VF) = ρ) by repeat econstructor.
  assert (LHLState M R G Ps Qs (allIdle, Init VE) (eq initPoss)).
  {
    constructor. simpl. intros.
    destruct_all. subst.
    unfold TIdle. repeat split.
    subst. easy.
    subst. easy.
    intros. apply H.(init_in_P).
  }
  generalize dependent (@allIdle T E F, Init VE).
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
    ddestruct H1.
    specialize (H0 p ρs st'' a).
    apply H0 in H4.
    2:{ exists x1. easy. }
    2: easy.
    destruct_all.
    specialize (IHx0 x).
    destruct H5.
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
      exists (p2m x5).
      easy.
    }
  }
}
(* step refinement *)
clear H2 H1 x0 x.
intros.
unfold InterStep, ThreadsStep, StateStep in H1. destruct_all.
ddestruct H2. unfold ThreadStep in H2.
destruct e. simpl in *.
destruct l; destruct ev.
destruct e.
{
  unfold StateStep in H3. simpl in H3.
  ddestruct H2. simpl in *.
  ddestruct H2.
  assert (H1' := H1). destruct H1'.
  specialize (all_safe0 n). rewrite H2 in all_safe0.
  destruct_all. ddestruct H5. unfold Commit in H7.
  apply (H7 s ρs t) in H4. clear H7. destruct_all.
  2:{
    do 2 pdestruct H9.
    exists x4, x5.
    psplit. psplit.
    easy. exact H12. easy.
  }
  2:{
    unfold differ_pointwise. intros.
    symmetry. apply H3. easy.
  }
  2:{
    econstructor.
    exact H2. easy.
  }
  exists x2.
  split.
  {
    exists x3. easy.
  }
  split.
  {
    constructor. constructor.
    intros.
    dec_eq_nats i n.
    {
      rewrite <- x.
      exists (x1 ->> QI), QR.
      intros.
      specialize (H8 v).
      destruct_all.
      split. rewrite reltCompAssoc in H8. easy.
      split. rewrite reltCompAssoc in H13. rewrite reltCompAssoc. easy.
      split.
      rewrite <- precCompAssoc.
      psplit. exact H9. easy.
      split.
      apply H6.
      rewrite reltCompAssoc.
      unfold sub, subRelt. intros.
      pdestruct H14. apply H5 in H15.
      exists x4, x5. easy.
    }
    {
      clear H8. move H1 at bottom. destruct H1.
      specialize (all_safe0 i).
      rewrite <- H3. 2: easy.
      destruct (fst s i).
      {
        unfold TIdle in *. destruct_all.
        split. split.
        rewrite <- H3; easy.
        intros. apply H7 in H15. destruct_all.
        apply H14 in H15. clear H14.
        induction H16.
        { easy. }
        {
          apply IHPossSteps. clear IHPossSteps.
          specialize (H16 i). specialize (H17 i).
          ddestruct H14.
          dec_eq_nats i i0.
          { destruct_all. congruence. }
          { rewrite <- H20, <- H21; easy. }
          dec_eq_nats i i0.
          { destruct_all. congruence. }
          { rewrite <- H20, <- H21; easy. }
        }
        {
          intros.
          apply H.(P_stable).
          psplit. apply H8.
          apply H.(G_in_R) with (i:=n); easy.
        }
      }
      {
        destruct_all.
        exists (x4 ->> R i).
        split.
        {
          apply (weakenSafe (P:= prComp (Ps i A0 m0) (TInvoke M i A0 m0) ->> x4)).
          unfold sub, subRelt. intros.
          pdestruct H15.
          apply H14 in H16.
          exists x5, x6. easy.
          easy.
        }
        split.
        {
          rewrite <- precCompAssoc.
          psplit. exact H8.
          apply H.(G_in_R) with (i:=n); easy.
        }
        {
          unfold sub, subRelt. intros.
          pdestruct H15. apply H14 in H15.
          exists x5, x6. easy.
        }
      }
      {
        destruct_all.
        exists (x4 ->> R i), (fun v => x5 v ->> R i).
        intros. specialize (H1 v). destruct_all.
        split.
        {
          eapply weakenCommit with (Q:= x5 v).
          unfold sub, subRelt. intros.
          psplit. exact H17. apply H.(R_refl).
          eapply weakenCommitPre with (P:= prComp (Ps i B0 om0)(TInvoke M i B0 om0) ->> x4).
          unfold sub, subRelt. intros.
          pdestruct H17. apply H16 in H18.
          psplit. exact H17. easy.
          easy.
        }
        split.
        {
          eapply (weakenSafe (P:= prComp (Ps i B0 om0)(TInvoke M i B0 om0) ->> x4 ->> x5 v)).
          unfold sub, subRelt. intros.
          pdestruct H17. pdestruct H18.
          apply H15 in H19. apply H16 in H18.
          psplit. exact H17. exists x8, x9. easy.
          easy.
        }
        split.
        {
          rewrite <- precCompAssoc.
          psplit. exact H14.
          apply H.(G_in_R) with (i:=n); easy.
        }
        split.
        {
          unfold sub, subRelt. intros.
          pdestruct H17. apply H15 in H17.
          exists x6, x7. easy.
        }
        {
          unfold sub, subRelt. intros.
          pdestruct H17. apply H16 in H17.
          exists x6, x7. easy.
        }
      }
    }
  }
  {
    intros.
    apply H7 in H13. clear H7. destruct_all.
    exists x4. split. easy. clear H7.
    induction H13.
    {
      exists []. repeat constructor.
    }
    {
      destruct_all.
      ddestruct H7.
      {
        exists ((i, UEvent (Some (CallEv m0))) :: x4).
        simpl. split. easy.
        eapply StepsMore with (st'':= p2m σ).
        2: easy.
        econstructor. econstructor. simpl.
        destruct_all.
        rewrite H13, H14, H16.
        econstructor; easy.
        simpl. intros.
        rewrite H17, H18; easy.
        easy.
      }
      {
        exists ((i, UEvent (Some (RetEv m0 v))) :: x4).
        simpl. split. easy.
        eapply StepsMore with (st'':= p2m σ).
        2: easy.
        econstructor. econstructor. simpl.
        destruct_all.
        rewrite H13, H15, H14, H16.
        econstructor; easy.
        simpl. intros.
        rewrite H17, H18; easy.
        easy.
      }
    }
  }
}
{
  unfold StateStep in H3. simpl in H3.
  ddestruct H2. simpl in *.
  ddestruct H2.
  assert (H1' := H1). destruct H1'.
  specialize (all_safe0 n). rewrite H2 in all_safe0.
  destruct_all. specialize (H5 n0). destruct_all.
  rewrite <- rtp_prId in H7.
  assert (H7' := H7).
  unfold Commit in H5. apply H5 with (t:=t) in H7. clear H5.
  2:{ unfold differ_pointwise. symmetry. apply H3. easy. }
  2:{ econstructor. exact H2. easy. }
  2: easy.
  destruct_all.
  exists x3.
  split.
  {
    exists x4. easy.
  }
  split.
  {
    constructor.
    constructor.
    intros.
    dec_eq_nats i n.
    {
      rewrite <- x.
      exists (x1 ->> x2 n0).
      split. easy.
      split.
      {
        rewrite <- precCompAssoc.
        psplit.
        rewrite rtp_prId in H7'. exact H7'.
        easy.
      }
      {
        unfold sub, subRelt. intros.
        rewrite reltCompAssoc in H12.
        pdestruct H12. apply H8 in H13.
        exists x5, x6. easy.
      }
    }
    {
      rewrite <- H3. 2: easy.
      move H1 at bottom. destruct H1.
      specialize (all_safe0 i).
      destruct (fst s i).
      {
        unfold TIdle in *. destruct_all.
        split. split.
        rewrite <- H3; easy.
        intros.
        apply H7 in H15. clear H7. destruct_all.
        apply H14 in H7. clear H14.
        induction H15.
        {
          easy.
        }
        {
          specialize (H15 i). specialize (H16 i).
          dec_eq_nats i0 i.
          {
            apply IHPossSteps.
            ddestruct H14; destruct_all; congruence.
          }
          {
            rewrite H15, H16 in H7.
            apply IHPossSteps. easy.
            easy. easy.
          }
        }
        intros.
        apply H.(P_stable).
        psplit.
        apply H13.
        apply H.(G_in_R) with (i:=n); easy.
      }
      {
        destruct_all.
        exists (x5 ->> R i).
        split.
        {
          apply (weakenSafe (P:= prComp (Ps i A0 m0) (TInvoke M i A0 m0) ->> x5)).
          unfold sub, subRelt. intros.
          pdestruct H15. apply H14 in H16.
          psplit. exact H15. easy.
          easy.
        }
        split.
        {
          rewrite <- precCompAssoc.
          psplit. exact H13.
          apply H.(G_in_R) with (i:=n); easy.
        }
        {
          unfold sub, subRelt. intros.
          pdestruct H15. apply H14 in H15.
          exists x6, x7. easy.
        }
      }
      {
        destruct_all.
        exists (x5 ->> R i), (fun v => x6 v ->> R i).
        intros. specialize (H1 v). destruct_all.
        split.
        {
          eapply weakenCommit with (Q:= x6 v).
          unfold sub, subRelt. intros.
          psplit. exact H17. apply H.(R_refl).
          eapply weakenCommitPre with (P:= prComp (Ps i B0 om0) (TInvoke M i B0 om0) ->> x5).
          unfold sub, subRelt. intros.
          pdestruct H17. apply H16 in H18.
          psplit. exact H17. easy.
          easy.
        }
        split.
        {
          eapply (weakenSafe (P:= prComp (Ps i B0 om0) (TInvoke M i B0 om0) ->> x5 ->> x6 v)).
          unfold sub, subRelt. intros.
          pdestruct H17. pdestruct H18.
          apply H15 in H19. apply H16 in H18.
          psplit. exact H17. exists x9, x10. easy.
          easy.
        }
        split.
        {
          rewrite <- precCompAssoc.
          psplit. exact H14.
          apply H.(G_in_R) with (i:=n); easy.
        }
        split.
        {
          unfold sub, subRelt. intros.
          pdestruct H17. apply H15 in H17.
          exists x7, x8. easy.
        }
        {
          unfold sub, subRelt. intros.
          pdestruct H17. apply H16 in H17.
          exists x7, x8. easy.
        }
      }
    }
  }
  {
    intros. apply H7 in H12. clear H7. destruct_all.
    exists x5. split. easy. clear H7.
    induction H12.
    {
      exists []. repeat constructor.
    }
    {
      destruct_all.
      ddestruct H7; destruct_all.
      {
        exists ((i, UEvent (Some (CallEv m0))) :: x5).
        split. easy.
        econstructor. 2: exact H20.
        econstructor. econstructor.
        econstructor; simpl.
        rewrite H12. easy.
        rewrite H13, H15. easy.
        simpl. intros.
        rewrite H16, H17; easy.
        easy.
      }
      {
        exists ((i, UEvent (Some (RetEv m0 v))) :: x5).
        split. easy.
        econstructor. 2: exact H20.
        econstructor. econstructor.
        econstructor; simpl.
        rewrite H12, H14. easy.
        rewrite H13, H15. easy.
        simpl. intros.
        rewrite H16, H17; easy.
        easy.
      }
    }
  }
}
{
  unfold StateStep in H3. simpl in H3.
  ddestruct H2. simpl in *.
  ddestruct H2.
  assert (H1' := H1). move H1 at bottom. destruct H1.
  specialize (all_safe0 n). rewrite H2 in all_safe0.
  destruct_all. ddestruct H1.
  exists ρs.
  split.
  {
    exists x0. easy.
  }
  split.
  {
    constructor. constructor.
    intros.
    destruct s, t. simpl in *. subst.
    rewrite <- rtp_prId in H7.
    unfold SilentStep in H5.
    assert (H7' := H7).
    apply H5 with (tht:=t) in H7. destruct_all.
    2:{ unfold differ_pointwise. symmetry. apply H3. easy. }
    2:{ econstructor. exact H2. easy. }
    dec_eq_nats i n.
    {
      rewrite <- x.
      exists (x1 ->> QS).
      split.
      rewrite <- reltCompAssoc. easy.
      split.
      rewrite <- precCompAssoc.
      psplit. rewrite rtp_prId in H7'. exact H7'.
      easy.
      unfold sub, subRelt. intros.
      rewrite reltCompAssoc in H9. pdestruct H9.
      apply H1 in H10.
      exists x2, x3. easy.
    }
    {
      move H1' at bottom.
      destruct H1'. specialize (all_safe0 i). simpl in *.
      rewrite <- H3. 2: easy.
      destruct (t0 i).
      {
        unfold TIdle in *. destruct_all. simpl in *.
        split. split.
        rewrite <- H3; easy.
        easy.
        intros.
        apply H.(P_stable).
        psplit. apply H11.
        eapply H.(G_in_R) with (i:=n). easy.
        easy.
      }
      {
        destruct_all.
        exists (x2 ->> R i).
        split.
        {
          apply (weakenSafe (P:= prComp (Ps i A0 m) (TInvoke M i A0 m) ->> x2)).
          unfold sub, subRelt. intros.
          pdestruct H13. apply H12 in H14.
          psplit.
          exact H13. easy.
          easy.
        }
        split.
        {
          rewrite <- precCompAssoc.
          psplit. exact H11.
          apply H.(G_in_R) with (i:=n). easy.
          easy.
        }
        {
          unfold sub, subRelt. intros.
          pdestruct H13. apply H12 in H13.
          exists x3, x4. easy.
        }
      }
      {
        destruct_all.
        exists (x2 ->> R i), (fun v => x3 v ->> R i).
        intros. specialize (H10 v). destruct_all.
        split.
        {
          eapply weakenCommitPre with (P:= prComp (Ps i B om0) (TInvoke M i B om0) ->> x2).
          unfold sub, subRelt. intros.
          pdestruct H15.
          apply H14 in H16.
          exists x4, x5. easy.
          eapply weakenCommit with (Q:= x3 v).
          unfold sub, subRelt. intros.
          psplit. 2: apply H.(R_refl). easy.
          easy.
        }
        split.
        {
          eapply (weakenSafe (P:= prComp (Ps i B om0) (TInvoke M i B om0) ->> x2 ->> x3 v)).
          unfold sub, subRelt. intros.
          pdestruct H15. pdestruct H16.
          apply H14 in H16. apply H13 in H17.
          psplit. exact H15.
          exists x6, x7. easy.
          easy.
        }
        split.
        {
          rewrite <- precCompAssoc.
          psplit. exact H12.
          apply H.(G_in_R) with (i:=n); easy.
        }
        split.
        {
          unfold sub, subRelt. intros.
          pdestruct H15. apply H13 in H15.
          exists x4, x5. easy.
        }
        {
          unfold sub, subRelt. intros.
          pdestruct H15. apply H14 in H15.
          exists x4, x5. easy.
        }
      }
    }
  }
  {
    intros.
    exists σ. split. easy.
    exists [].
    repeat constructor.
  }
}
{
  unfold StateStep in H3. simpl in H3.
  ddestruct H2. simpl in *.
  ddestruct H2.
  assert (H1' := H1). destruct H1'.
  specialize (all_safe0 n). rewrite H2 in all_safe0.
  unfold TIdle in all_safe0. destruct_all.
  exists (fun σ => exists ρ, ρs ρ /\ σ = invPoss n ρ m).
  split.
  {
    exists (invPoss n x0 m), x0. easy.
  }
  split.
  {
    constructor. constructor.
    intros.
    dec_eq_nats i n.
    {
      rewrite <- x.
      exists (R n).
      split.
      apply H.(all_verified).
      split.
      {
        psplit. 2: apply H.(R_refl).
        psplit. apply H6.
        unfold TInvoke, TIdle.
        split.
        easy.
        split.
        econstructor. econstructor; easy. easy.
        split. easy.
        intros. destruct_all. subst. simpl.
        extensionality σ. apply propositional_extensionality.
        split; intros; psimpl.
        {
          exists x1. cbn. rewrite eqb_id.
          repeat split; (easy || apply differ_pointwise_trivial).
        }
        {
          exists x1. unfold invPoss. destruct σ, x1. cbn in *.
          repeat split; f_equal; try easy.
          extensionality j. dec_eq_nats n j.
          rewrite eqb_id. easy.
          rewrite eqb_nid. apply H12. easy. easy.
          extensionality j. dec_eq_nats n j.
          rewrite eqb_id. easy.
          rewrite eqb_nid. apply H13. easy. easy.
        }
      }
      {
        apply H.(R_trans).
      }
    }
    {
      destruct H1. specialize (all_safe0 i).
      rewrite <- H3. 2: easy.
      destruct (fst s i).
      {
        unfold TIdle in all_safe0. destruct_all.
        split.
        split.
        rewrite <- H3; easy.
        intros. destruct_all. subst. simpl.
        rewrite eqb_nid. apply H10. easy. easy.
        intros.
        apply H.(P_stable).
        psplit.
        apply H9.
        eapply H.(Inv_in_R) with (i:=n). easy.
        eexists _, m. unfold TInvoke.
        split. easy.
        split.
        econstructor. econstructor; easy. easy.
        split. easy.
        extensionality σ. apply propositional_extensionality.
        split; intros; psimpl.
        {
          exists x1. cbn. rewrite eqb_id.
          repeat split; (easy || apply differ_pointwise_trivial).
        }
        {
          exists x1. unfold invPoss. destruct σ, x1. cbn in *.
          repeat split; f_equal; try easy.
          extensionality j. dec_eq_nats n j.
          rewrite eqb_id. easy.
          rewrite eqb_nid. apply H15. easy. easy.
          extensionality j. dec_eq_nats n j.
          rewrite eqb_id. easy.
          rewrite eqb_nid. apply H16. easy. easy.
        }
      }
      {
        destruct_all.
        exists (x1 ->> R i).
        split.
        {
          apply (weakenSafe (P:= prComp (Ps i A0 m0) (TInvoke M i A0 m0) ->> x1)).
          unfold sub, subRelt. intros.
          pdestruct H11.
          apply H10 in H12.
          psplit. exact H11. easy.
          easy.
        }
        split.
        {
          pdestruct H9.
          psplit.
          exact H9.
          psplit.
          exact H11.
          eapply H.(Inv_in_R) with (i:=n). easy.
          eexists _, m. unfold TInvoke.
          split. easy.
          split.
          econstructor. econstructor; easy. easy.
          split. easy.
          extensionality σ. apply propositional_extensionality.
          split; intros; psimpl.
          {
            exists x5. cbn. rewrite eqb_id.
            repeat split; (easy || apply differ_pointwise_trivial).
          }
          {
            exists x5. unfold invPoss. destruct σ, x5. cbn in *.
            repeat split; f_equal; try easy.
            extensionality j. dec_eq_nats n j.
            rewrite eqb_id. easy.
            rewrite eqb_nid. apply H16. easy. easy.
            extensionality j. dec_eq_nats n j.
            rewrite eqb_id. easy.
            rewrite eqb_nid. apply H17. easy. easy.
          }
        }
        {
          unfold sub, subRelt. intros.
          pdestruct H11. apply H10 in H11.
          exists x2, x3. easy.
        }
      }
      {
        move all_safe0 at bottom.
        destruct_all.
        exists (x1 ->> R i), (fun v => x2 v ->> R i).
        intros. specialize (H1 v). destruct_all.
        split.
        {
          eapply weakenCommitPre with (P:= prComp (Ps i B om) (TInvoke M i B om) ->> x1).
          unfold sub, subRelt. intros.
          pdestruct H13.
          apply H12 in H14.
          exists x3, x4. easy.
          eapply weakenCommit with (Q:= x2 v).
          unfold sub, subRelt. intros.
          psplit. 2: apply H.(R_refl). easy.
          easy.
        }
        split.
        {
          eapply (weakenSafe (P:= prComp (Ps i B om) (TInvoke M i B om) ->> x1 ->> x2 v)).
          unfold sub, subRelt. intros.
          pdestruct H13. pdestruct H14.
          apply H11 in H15. apply H12 in H14.
          psplit. exact H13.
          exists x5, x6. easy.
          easy.
        }
        split.
        {
          rewrite <- precCompAssoc.
          psplit. exact H10.
          apply H.(Inv_in_R) with (i:=n). easy.
          eexists _, m.
          split. easy.
          split. econstructor. econstructor; easy. easy.
          split. easy.
          intros. destruct_all. subst. simpl.
          extensionality σ. apply propositional_extensionality.
          split; intros; psimpl.
          {
            exists x4. cbn. rewrite eqb_id.
            repeat split; (easy || apply differ_pointwise_trivial).
          }
          {
            exists x4. unfold invPoss. destruct σ, x4. cbn in *.
            repeat split; f_equal; try easy.
            extensionality j. dec_eq_nats n j.
            rewrite eqb_id. easy.
            rewrite eqb_nid. apply H17. easy. easy.
            extensionality j. dec_eq_nats n j.
            rewrite eqb_id. easy.
            rewrite eqb_nid. apply H18. easy. easy.
          }
        }
        split.
        {
          unfold sub, subRelt. intros.
          pdestruct H13. apply H11 in H13.
          exists x3, x4. easy.
        }
        {
          unfold sub, subRelt. intros.
          pdestruct H13. apply H12 in H13.
          exists x3, x4. easy.
        }
      }
    }
  }
  {
    intros. destruct_all. subst. simpl.
    exists x1. split. easy.
    exists [(n, OEvent (CallEv m))].
    split. easy.
    econstructor. 2: constructor.
    econstructor. econstructor. simpl.
    rewrite eqb_id.
    apply H7 in H8. destruct_all.
    rewrite H8. econstructor; easy.
    simpl. intros.
    rewrite eqb_nid. easy.
    easy.
    easy.
  }
}
{
  unfold StateStep in H3. simpl in H3.
  ddestruct H2. simpl in *.
  ddestruct H2.
  exists (fun σ =>
    exists ρ, ρs ρ /\
      ρ.(PRets) n = RetPoss m n0 /\
      ρ.(PCalls) n = CallDone m /\
      mapRetPoss n m n0 ρ σ).
  assert (H1' := H1). move H1' at top. move H1 at bottom.
  admit.
}
Admitted.

Definition m2p {T F} {VF : Spec T F} (s : InterState F VF) : Poss VF := {|
  PState := snd s;
  PCalls i := match fst s i with
  | Idle => CallIdle
  | Cont m (Bind _ _) => CallPoss m
  | Cont m (Return _) => CallDone m
  | UCall m _ _ => CallDone m
  | _ => CallIdle
  end;
  PRets i := match fst s i with
  | UCall m _ _ => RetIdle
  | Cont m (Return v) => RetPoss m v 
  | _ => RetIdle
  end
|}.

Variant FullPossStep {T F} {VF : Spec T F} i (ρ σ : Poss VF) : LEvent F F -> Prop :=
| PPendCall A (m : F A) :
  ρ.(PState) = σ.(PState) ->
  ρ.(PCalls) i = CallIdle ->
  σ.(PCalls) i = CallPoss m ->
  ρ.(PRets) i = RetIdle ->
  σ.(PRets) i = RetIdle ->
  FullPossStep i ρ σ (OEvent (CallEv m))
| PCommitCall A (m : F A) :
  VF.(Step) ρ.(PState) (i, CallEv m) σ.(PState) ->
  ρ.(PCalls) i = CallPoss m ->
  σ.(PCalls) i = CallDone m ->
  ρ.(PRets) i = RetIdle ->
  σ.(PRets) i = RetIdle ->
  FullPossStep i ρ σ (UEvent (Some (CallEv m)))
| PCommitRet A (m : F A) v :
  VF.(Step) ρ.(PState) (i, RetEv m v) σ.(PState) ->
  ρ.(PCalls) i = CallDone m ->
  σ.(PCalls) i = CallDone m ->
  ρ.(PRets) i = RetIdle ->
  σ.(PRets) i = RetPoss m v ->
  FullPossStep i ρ σ (UEvent (Some (RetEv m v)))
| PPendRet A (m : F A) v :
  ρ.(PState) = σ.(PState) ->
  ρ.(PCalls) i = CallDone m ->
  σ.(PCalls) i = CallIdle ->
  ρ.(PRets) i = RetPoss m v ->
  σ.(PRets) i = RetIdle ->
  FullPossStep i ρ σ (OEvent (RetEv m v)).

Inductive FullPossSteps {T F} {VF : Spec T F} : Poss VF -> Trace (ThreadLEvent T F F) -> Poss VF -> Prop :=
| PossStepsRefl ρ :
    FullPossSteps ρ [] ρ
| PossStepsStep i e p ρ σ τ :
    FullPossStep i ρ σ e ->
    (forall j, i <> j -> PCalls ρ j = PCalls σ j) ->
    (forall j, i <> j -> PRets ρ j = PRets σ j) ->
    FullPossSteps σ p τ ->
    FullPossSteps ρ ((i, e) :: p) τ.

Lemma FullPossSteps_trans {T F} {VF : Spec T F} :
  forall p q (ρ τ : Poss VF),
  (exists σ,
    FullPossSteps ρ p σ /\
    FullPossSteps σ q τ) ->
  FullPossSteps ρ (p ++ q) τ.
intros. psimpl.
induction H. easy.
econstructor.
exact H. easy. easy.
apply IHFullPossSteps. easy.
Qed.

Lemma FullPossSteps_trans_inv {T F} {VF : Spec T F} :
  forall p q (ρ τ : Poss VF),
  FullPossSteps ρ (p ++ q) τ ->
  exists σ,
    FullPossSteps ρ p σ /\
    FullPossSteps σ q τ.
intros. psimpl.
generalize dependent ρ.
induction p; cbn; intros.
{
  exists ρ. split. constructor. easy.
}
{
  ddestruct H.
  apply IHp in H2. destruct_all.
  exists x. split. 2: easy.
  econstructor. 4: exact H2.
  all: easy.
}
Qed.


Fixpoint liftOver {T E F} (p : Trace (ThreadEvent T F)) : Trace (ThreadLEvent T E F) :=
  match p with
  | [] => []
  | (i, e) :: p => (i, OEvent e) :: liftOver p
  end.

Lemma liftOver_app {T E F} :
  forall p q : Trace (ThreadEvent T F),
  liftOver (E:=E) (p ++ q) = liftOver p ++ liftOver q.
intros. induction p. easy.
destruct a. cbn. f_equal. easy.
Qed.

Inductive no_self {T A} (i : Name T) : Trace (Name T * A) -> Prop :=
| NSNil :
    no_self i nil
| NSCons j e p :
    i <> j ->
    no_self i p ->
    no_self i ((j, e) :: p).

Notation fullSet p := (fun σ =>
  exists q,
    projOver p = projOver q /\
    FullPossSteps initPoss q σ).

Definition comp_inv {T E F}
  (VE : Spec T E) (VF : Spec T F) (M : Impl E F)
  : Prec VE VF :=
  fun t σs =>
  exists p,
    InterSteps (spec:=VE) M (allIdle, Init VE) p t /\
    (exists σ, σs σ) /\
    forall σ, σs σ -> fullSet p σ.

Definition comp_rely {T E F}
  (VE : Spec T E) (VF : Spec T F) (M : Impl E F)
  : Name T -> Relt VE VF :=
  fun i s ρs t σs =>
    comp_inv VE VF M s ρs -> comp_inv VE VF M t σs.

Definition comp_guar {T E F}
  (VE : Spec T E) (VF : Spec T F) (M : Impl E F)
  : Name T -> Relt VE VF :=
  fun i s ρs t σs =>
    forall j, i <> j -> comp_rely VE VF M j s ρs t σs.

Ltac set_ext x := extensionality x; apply propositional_extensionality.

Lemma AllCallEv_cong {T F} :
  forall p q : Trace (ThreadEvent T F),
  AllCallEv p ->
  AllCallEv q ->
  AllCallEv (p ++ q).
intros. induction H. easy.
econstructor. easy.
Qed.

Lemma HBRw_cong {T E} :
  forall pL qL pR qR : Trace (ThreadEvent T E),
  HBRw pL qL ->
  HBRw pR qR ->
  HBRw (pL ++ pR) (qL ++ qR).
intros. induction H.
{
  induction H0. constructor. clear H0.
  eapply clos_rt_rt1n_iff, rt_trans.
  2:{
    apply clos_rt_rt1n_iff.
    exact IHclos_refl_trans_1n.
  }
  clear IHclos_refl_trans_1n.
  apply clos_rt_rt1n_iff.
  dependent destruction H;
  repeat rewrite app_assoc with
    (l:=x) (m:=l);
  econstructor;
  constructor;
  easy.
}
clear H1.
eapply clos_rt_rt1n_iff, rt_trans.
2:{
  apply clos_rt_rt1n_iff.
  exact IHclos_refl_trans_1n.
}
clear IHclos_refl_trans_1n H0.
apply clos_rt_rt1n_iff.
dependent destruction H;
repeat rewrite <- app_assoc;
econstructor;
constructor;
easy.
Qed.

Lemma no_self_cong {T A} :
  forall i p q,
  @no_self T A i (p ++ q) ->
  no_self i p /\ no_self i q.
intros. induction p; cbn in *.
repeat constructor; easy.
ddestruct H. apply IHp in H0.
destruct_all. split.
constructor; easy.
easy.
Qed.

Lemma extract_oevent {T E F} :
  forall (p : Trace (ThreadLEvent T F F)),
  forall (q : Trace (ThreadLEvent T E F)),
  forall i (ev : Event F),
  (i, ev) :: projOver p = projOver q ->
  exists l r,
    projOver l = [] /\
    q = l ++ (i, OEvent ev) :: r.
intros.
generalize dependent p.
induction q; cbn; intros.
discriminate.
destruct a, l; cbn in *.
{
  apply IHq in H. psimpl.
  exists ((n, UEvent ev0) :: x), x0.
  easy.
}
{
  ddestruct H.
  exists [], q.
  easy.
}
Qed.

Lemma extract_end {A} {xs ys zs : list A} {x : A} :
  xs ++ [x] = ys ++ zs ->
  zs = [] \/
  exists ws, zs = ws ++ [x].
intros.
generalize dependent xs.
generalize dependent zs.
induction ys; cbn; intros.
{
  subst. right. exists xs. easy.
}
{
  destruct xs; cbn in *.
  {
    ddestruct H. symmetry in x.
    apply app_eq_nil in x. psimpl.
    left. easy.
  }
  {
    ddestruct H. apply IHys in x.
    psimpl. destruct x; psimpl.
    left. easy.
    right. exists x. easy.
  }
}
Qed.

Lemma cut_at_ret {T F} :
  forall (p q r sC : Trace (ThreadEvent T F)) i A (m : F A) v,
  AllCallEv sC ->
  p ++ sC = q ++ [(i, RetEv m v)] ++ r ->
  exists w,
    p = q ++ [(i, RetEv m v)] ++ w /\
    r = w ++ sC.
intros.
generalize dependent sC.
generalize dependent q.
generalize dependent r.
induction p; cbn in *; intros.
{
  exfalso.
  generalize dependent q.
  induction H; intros.
  destruct q; cbn in *; discriminate.
  destruct q; cbn in *; ddestruct H0.
  eapply IHAllCallEv. easy.
}
{
  ddestruct q; cbn in *;
  ddestruct H0.
  {
    exists p. easy.
  }
  {
    apply IHp in x. psimpl.
    exists x. easy. easy.
  }
}
Qed.

Lemma split_projOver {T E F} :
  forall (p : Trace (ThreadLEvent T E F)) i A (m : F A) v l r,
  projOver p = l ++ [(i, RetEv m v)] ++ r ->
  exists l' r',
    l = projOver l' /\
    r = projOver r' /\
    p = l' ++ [(i, OEvent (RetEv m v))] ++ r'.
intros. generalize dependent l.
induction p; cbn; intros.
{
  destruct l; cbn in *; discriminate.
}
{
  destruct a, l0; cbn in *.
  {
    apply IHp in H. psimpl.
    exists ((n, UEvent ev) :: x), x0.
    cbn. easy.
  }
  {
    destruct l; cbn in *;
    ddestruct H.
    {
      exists [], p.
      easy.
    }
    {
      apply IHp in x. psimpl.
      exists ((n, OEvent ev) :: x), x0.
      cbn. easy.
    }
  }
}
Qed.

Lemma projOver_extract_ret {T E F} :
  forall i A (m : F A) v,
  forall (p : Trace (ThreadLEvent T F F)) (q : Trace (ThreadLEvent T E F)),
  projOver p = projOver q ++ [(i, RetEv m v)] ->
  exists q' r,
    projOver q = projOver q' /\
    projOver r = [] /\
    p = q' ++ [(i, OEvent (RetEv m v))] ++ r.
intros.
apply split_projOver in H. psimpl.
exists x, x0. easy.
Qed.

Lemma AllRetEv_inj {T F} :
  forall p q : Trace (ThreadEvent T F),
  AllRetEv (p ++ q) ->
  AllRetEv p /\ AllRetEv q.
intros. induction p; cbn in *.
repeat constructor; easy.
ddestruct H. apply IHp in H.
destruct_all. split.
constructor. easy.
easy.
Qed.

Lemma AllRetEv_cong {T F} :
  forall p q : Trace (ThreadEvent T F),
  AllRetEv p ->
  AllRetEv q ->
  AllRetEv (p ++ q).
intros. induction H. easy.
cbn. constructor. easy.
Qed.

Lemma cons_app {A} {x : A} {xs : list A} :
  x :: xs = [x] ++ xs.
easy.
Qed.

Lemma invoke_in_rely {T E F} {VE : Spec T E} {VF : Spec T F } {M : Impl E F} :
  (forall st p,
    InterSteps M (allIdle, Init VE) p st ->
    exists st' q,
      projOver p = projOver q /\
      FullPossSteps (VF:=VF) initPoss q st') ->
  forall i j : Name T, InvokeAny M i ==> comp_rely VE VF M j.
unfold InvokeAny, TInvoke, TIdle, comp_rely, comp_inv, sub, subRelt.
intros. psimpl. psimpl.
{
  exists (x ++ [(i, OEvent (CallEv x2))]).
  split.
  {
    unfold InterSteps. rewrite <- Steps_app.
    exists s. split. easy.
    econstructor. 2: constructor.
    destruct H4. cbn in *.
    split. 2: easy.
    constructor; easy.
  }
  split.
  {
    exists (invPoss i x0 x2), x0.
    cbn. rewrite eqb_id.
    repeat split; (easy || apply differ_pointwise_trivial).
  }
  {
    intros. psimpl. assert (H6' := H6).
    apply H3 in H6. psimpl.
    exists (x4 ++ [(i, OEvent (CallEv x2))]).
    split.
    {
      repeat rewrite projOver_app.
      cbn. rewrite H6. easy.
    }
    {
      apply FullPossSteps_trans.
      exists x3. split. easy.
      econstructor. 4: constructor.
      assert (PCalls x3 i = CallIdle /\ PRets x3 i = RetIdle).
      {
        apply H7. easy.
      }
      psimpl.
      constructor; try easy.
      intros. rewrite H11; easy.
      intros. rewrite H12; easy.
    }
  }
}
Qed.

Lemma local_to_full {T F} {VF : Spec T F} :
  forall x y : Poss VF,
  PossSteps x y ->
  exists p,
    projOver p = [] /\
    FullPossSteps x p y.
intros. induction H.
exists []. repeat constructor; easy.
psimpl. ddestruct H.
{
  exists ((i, UEvent (Some (CallEv m))) :: x).
  split. cbn. easy.
  econstructor. 4: exact H8.
  constructor; easy.
  easy. easy.
}
{
  exists ((i, UEvent (Some (RetEv m v))) :: x).
  split. cbn. easy.
  econstructor. 4: exact H8.
  constructor; easy.
  easy. easy.
}
Qed.

Lemma return_in_rely {T E F} {VE : Spec T E} {VF : Spec T F } {M : Impl E F} :
  (forall st p,
    InterSteps M (allIdle, Init VE) p st ->
    exists st' q,
      projOver p = projOver q /\
      FullPossSteps (VF:=VF) initPoss q st') ->
  forall i j : Name T, ReturnAny M i ==> comp_rely VE VF M j.
unfold ReturnAny, TReturn, Returned, comp_rely, comp_inv, sub, subRelt.
intros. psimpl.
{
  exists (x ++ [(i, OEvent (RetEv x2 x3))]). split.
  {
    unfold InterSteps. rewrite <- Steps_app.
    exists s. split. easy.
    econstructor. 2: constructor.
    destruct H4. cbn in *.
    split. 2: easy.
    constructor; easy.
  }
  split.
  {
    apply H3 in H2. clear H3. psimpl.
    destruct H4. cbn in *. ddestruct H4.
    apply H0 in H1. clear H0. psimpl.
    exists (retPoss i x6), x6.
    split. easy.
    unfold mapRetPoss. cbn. rewrite eqb_id.
    repeat match goal with
    | [ |- ?P /\ ?Q ] => split; try easy
    end.
    unfold differ_pointwise. intros. rewrite eqb_nid; easy.
    unfold differ_pointwise. intros. rewrite eqb_nid; easy.
  }
  {
    unfold mapRetPoss. intros. psimpl.
    apply H3 in H6. psimpl.
    exists (x5 ++ [(i, OEvent (RetEv x2 x3))]).
    split.
    {
      repeat rewrite projOver_app. cbn.
      rewrite H6. easy.
    }
    {
      apply FullPossSteps_trans.
      exists x4. split. easy.
      econstructor. 4: constructor.
      constructor; try easy.
      intros. rewrite H13; easy.
      intros. rewrite H14; easy.
    }
  }
}
Qed.

Lemma comp_commit {T E F} {VE : Spec T E} {VF : Spec T F} {M : Impl E F} i e :
  (forall st p,
    InterSteps M (allIdle, Init VE) p st ->
    exists st' q,
      projOver p = projOver q /\
      FullPossSteps (VF:=VF) initPoss q st') ->
  Commit i (comp_guar VE VF M i) (comp_inv VE VF M) e (fun _ _ => comp_inv VE VF M).
unfold Commit, comp_inv. intros. psimpl.
assert (
  InterSteps M
    (allIdle, Init VE)
    (x ++ [(i, UEvent (Some e))])
    t
).
{
  unfold InterSteps. rewrite <- Steps_app.
  exists s. split. easy.
  econstructor. 2: constructor.
  split. 2: easy.
  constructor; cbn. easy.
  intros. rewrite H1; easy.
}
exists (fun y => exists x, ρs x /\ PossSteps x y).
split.
{
  exists x0, x0.
  split. easy.
  constructor.
}
split.
{
  easy.
}
split.
{
  exists (x ++ [(i, UEvent (Some e))]).
  split. easy.
  split.
  {
    exists x0, x0.
    split. easy.
    constructor.
  }
  {
    intros. psimpl.
    apply H5 in H7. clear H5. psimpl.
    apply local_to_full in H8. psimpl.
    exists (x2 ++ x3). repeat rewrite projOver_app.
    cbn. rewrite H8. repeat rewrite app_nil_r.
    split. easy.
    apply FullPossSteps_trans.
    exists x1. easy.
  }
}
{
  unfold comp_guar, comp_rely, comp_inv.
  intros. psimpl. exists (x ++ [(i, UEvent (Some e))]).
  split. easy. split. exists x2, x2.
  split. easy. constructor.
  intros. psimpl.
  apply local_to_full in H12. psimpl.
  apply H5 in H11. clear H5. psimpl.
  exists (x5 ++ x4). repeat rewrite projOver_app.
  cbn. rewrite H12. repeat rewrite app_nil_r.
  split. easy.
  apply FullPossSteps_trans.
  exists x3. easy. 
}
Qed.

Fixpoint numSilent {T F} (p : Trace (ThreadLEvent T F F)) : nat :=
  match p with
  | [] => 0
  | (_, UEvent None) :: p => S (numSilent p)
  | _ :: p => numSilent p
  end.

Theorem completeness {T E F} (lay : Layer T E F) VF :
  Lin (overObj lay) VF ->
  exists R G Ps Qs,
    VerifyImpl lay.(USpec) VF R G Ps lay.(LImpl) Qs.
unfold Lin, KConc, specRefines, Incl, IsTraceOfSpec.
repeat rewrite projInterSteps.
destruct lay. cbn. intros.
rename USpec into VE. rename LImpl into M.
assert (
  forall st p,
    InterSteps M (allIdle, Init VE) p st ->
    exists st' q,
      projOver p = projOver q /\
      FullPossSteps (VF:=VF) initPoss q st'
).
{
  intros. specialize (H (projOver p)).
  assert (
    exists st q,
      projOver p = projOver q /\
      InterSteps M (allIdle, Init VE) q st /\
      IsOverObjTrace q
  ).
  {
    exists st, p. repeat split; try easy.
    ddestruct H0.
    left. easy.
    unfold InterStep, ThreadsStep, StateStep in H0. cbn in H0.
    destruct_all.
    destruct ev, l; cbn in *.
    ddestruct H0. cbn in H0.
    ddestruct H0.
    right. repeat econstructor.
  }
  apply H in H1. clear H. destruct_all.
  exists (m2p x), x0. split. easy.
  clear - H1.
  change initPoss
  with (m2p (allIdle, Init VF)).
  assert (
    forall i,
      (@allIdle T F F i = Idle) \/
      (exists A (m : F A), @allIdle T F F i = Cont m (Bind m Return)) \/
      (exists A (m : F A), @allIdle T F F i = UCall m m Return) \/
      (exists A (m : F A) v, @allIdle T F F i = Cont m (Return v))
  ).
  { left. easy. }
  change (@allIdle T F F)
  with (fst (@allIdle T F F, Init VF))
  in H.
  generalize dependent (@allIdle T F F, Init VF).
  induction x0; intros.
  {
    ddestruct H1.
    constructor.
  }
  {
    ddestruct H1. destruct a.
    unfold InterStep, ThreadsStep, StateStep in H.
    psimpl. ddestruct H. cbn in *.
    eapply PossStepsStep with
      (σ:= m2p st'').
    2:{ unfold m2p. intros. cbn. rewrite H0; easy. }
    2:{ unfold m2p. intros. cbn. rewrite H0; easy. }
    2:{
      apply IHx0. easy.
      clear - H H3 H0. intros.
      specialize (H3 i).
      dec_eq_nats i n.
      {
        clear H0.
        repeat match goal with
        | [ H : ?P \/ ?Q |- _] => destruct H; destruct_all
        end.
        {
          rewrite H0 in H.
          destruct l; cbn in *; ddestruct H.
          right. left. exists _, m. easy.
        }
        {
          rewrite H0 in H.
          destruct l; cbn in *; ddestruct H.
          right. right. left. exists _, x0. easy.
        }
        {
          rewrite H0 in H.
          destruct l; cbn in *; ddestruct H.
          right. right. right. exists _, x0, v. easy.
        }
        {
          rewrite H0 in H.
          destruct l; cbn in *; ddestruct H.
          left. easy.
        }
      }
      {
        rewrite H0 in H3; easy.
      }
    }
    {
      clear - H3 H2 H0 H.
      specialize (H3 n).
      repeat match goal with
      | [ H : ?P \/ ?Q |- _] => destruct H; destruct_all
      end.
      {
        rewrite H1 in H.
        destruct l; cbn in *; ddestruct H.
        constructor. easy.
        cbn. rewrite H1. easy.
        cbn. rewrite <- x. easy.
        cbn. rewrite H1. easy.
        cbn. rewrite <- x. easy.
      }
      {
        rewrite H1 in H.
        destruct l; cbn in *; ddestruct H.
        constructor. easy.
        cbn. rewrite H1. easy.
        cbn. rewrite <- x. easy.
        cbn. rewrite H1. easy.
        cbn. rewrite <- x. easy.
      }
      {
        rewrite H1 in H.
        destruct l; cbn in *; ddestruct H.
        constructor. easy.
        cbn. rewrite H1. easy.
        cbn. rewrite <- x. easy.
        cbn. rewrite H1. easy.
        cbn. rewrite <- x. easy.
      }
      {
        rewrite H1 in H.
        destruct l; cbn in *; ddestruct H.
        constructor. easy.
        cbn. rewrite H1. easy.
        cbn. rewrite <- x. easy.
        cbn. rewrite H1. easy.
        cbn. rewrite <- x. easy.
      }
    }
  }
}
clear H. rename H0 into H.
exists
  (comp_rely VE VF M),
  (comp_guar VE VF M),
  (fun _ _ _ => comp_inv VE VF M),
  (fun _ _ _ _ _ _ => comp_inv VE VF M).
constructor.
{
  easy.
}
{
  unfold comp_rely, sub, subRelt. intros. psimpl.
  apply H2, H0. easy.
}
{
  unfold comp_guar, sub, subRelt. intros.
  apply H1. easy.
}
{
  intros. apply invoke_in_rely; easy.
}
{
  intros. apply return_in_rely; easy.
}
{
  unfold comp_inv. intros.
  exists []. split. constructor.
  split. repeat econstructor.
  intros. subst.
  exists []. repeat constructor.
}
{
  unfold Stable, stablePrec, sub, subPrec.
  intros. psimpl. apply H1. easy.
}
{
  unfold Stable, stablePost, stableRelt, sub, subRelt.
  intros. psimpl. apply H1. easy.
}
{
  unfold sub, subPrec. intros. psimpl.
  assert (comp_rely VE VF M i x x0 s ρ).
  {
    eapply return_in_rely. easy.
    exists _, m1, v. exact H1.
  }
  apply H4. easy.
}
{
  intros.
  assert (
    prComp (comp_inv VE VF M) (TInvoke M i A m) ->> comp_rely VE VF M i ==> (fun _ _ => comp_inv VE VF M)
  ).
  {
    unfold sub, subRelt. intros. psimpl.
    apply H1.
    assert (comp_rely VE VF M i s ρ x x0).
    {
      eapply invoke_in_rely. easy.
      exists _, m. exact H2.
    }
    apply H3. easy.
  }
  unfold VerifyProg. rewrite paco_eqv.
  generalize dependent (M A m).
  generalize dependent (prComp (comp_inv VE VF M) (TInvoke M i A m) ->> comp_rely VE VF M i).
  pcofix rec. intros. destruct p; pfold.
  {
    assert (
      ReltToPrec (fun _ _=> comp_inv VE VF M) =
      comp_inv VE VF M
    ).
    {
      extensionality s.
      extensionality ρs.
      apply propositional_extensionality.
      split; intros; psimpl; easy.
    }
    eapply SafeBind with
      (QI:=fun _ _ => comp_inv VE VF M)
      (QR:=fun _ _ _ => comp_inv VE VF M).
    {
      unfold Stable, stableRelt, sub, subRelt.
      intros. psimpl. apply H3. easy.
    }
    {
      unfold Stable, stablePost, stableRelt, sub, subRelt.
      intros. psimpl. apply H3. easy.
    }
    {
      eapply weakenCommitPre. exact H1.
      rewrite H0.
      apply comp_commit.
      easy.
    }
    split.
    {
      eapply weakenCommitPre.
      {
        unfold sub, subRelt. intros. psimpl.
        exact H3.
      }
      rewrite H0 at 1.
      apply comp_commit.
      easy.
    }
    {
      right. apply rec.
      unfold sub, subRelt. intros. psimpl.
      easy.
    }
  }
  {
    eapply SafeReturn with
      (P':=fun _ _ _ t ys =>
        comp_inv VE VF M t ys /\
        Returned i m a t ys).
    {
      unfold ReturnStep. intros.
      unfold ReltToPrec in *. psimpl.
      apply H1 in H0. clear H1.
      unfold comp_inv in *. psimpl.
    }
    {
      unfold sub, subRelt. intros. psimpl.
      psplit. exact H0.
      split. 2: easy. easy.
    }
  }
  {
    eapply SafeNoOp with
      (QS:=fun _ _ => comp_inv VE VF M).
    {
      unfold Stable, stableRelt, sub, subRelt.
      intros. psimpl. apply H2. easy.
    }
    {
      unfold SilentStep. intros.
      unfold ReltToPrec in H0. psimpl.
      apply H1 in H0. unfold comp_inv in *.
      psimpl.
      split.
      exists (x1 ++ [(i, UEvent None)]).
      split.
      {
        unfold InterSteps. rewrite <- Steps_app.
        exists (ths, s). split. easy.
        econstructor. 2: constructor.
        split. 2: easy.
        constructor; try easy.
        intros. rewrite H2; easy.
      }
      split.
      {
        exists x2. easy.
      }
      {
        intros.
        apply H5 in H6. psimpl.
        exists x0. rewrite projOver_app.
        cbn. rewrite app_nil_r.
        easy.
      }
      {
        unfold comp_guar, comp_rely, comp_inv.
        intros. psimpl.
        exists (x0 ++ [(i, UEvent None)]).
        split.
        {
          unfold InterSteps. rewrite <- Steps_app.
          exists (ths, s). split. easy.
          econstructor. 2: constructor.
          split. 2: easy.
          constructor; try easy.
          intros. rewrite H2; easy.
        }
        split.
        {
          exists x3. easy.
        }
        {
          intros. psimpl.
          apply H9 in H10. psimpl.
          exists x4.
          rewrite projOver_app. cbn.
          rewrite app_nil_r.
          easy.
        }
      }
    }
    {
      right. apply rec.
      unfold sub, subRelt.
      intros. psimpl. easy.
    }
  }
}
Qed.