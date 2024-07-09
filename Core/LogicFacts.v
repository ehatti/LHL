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
| [ H : InterStep ?i ?st ?e ?st' |- _ ] => dependent destruction H
| [ H : Step ?impl ?st ?ev ?st' |- _ ] => simpl in H; destruct H;  dependent destruction H
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

CoFixpoint weakenSafe {T E F VE VF i R G P P' A Q C} :
  (P' ==> P) ->
  SafeProg (T:=T) (E:=E) (F:=F) (VE:=VE) (VF:=VF) (A:=A) i R G P C Q ->
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
      SafeProg i (R i) (G i) ((prComp (Ps i _ m) (TInvoke M i _ m)) ->> Is) p (fun v => Qs i _ m v ->> PrecToRelt (Returned i m)) /\
      (Ps i _ m <<- TInvoke M i _ m <<- Is) s ρs /\
      (Is ->> R i) ==> Is
  | UCall om um k =>
    exists Is QR, forall v,
      Commit i (G i) ((prComp (Ps i _ om) (TInvoke M i _ om)) ->> Is) (RetEv um v) (QR v) /\
      SafeProg i (R i) (G i) ((prComp (Ps i _ om) (TInvoke M i _ om)) ->> Is ->> QR v) (k v) (fun v => Qs i _ om v ->> PrecToRelt (Returned i om)) /\
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
    dependent destruction H1.
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
dependent destruction H2. unfold ThreadStep in H2.
destruct e. simpl in *.
destruct l; destruct ev.
destruct e.
{
  unfold StateStep in H3. simpl in H3.
  dependent destruction H2. simpl in *.
  dependent destruction H2.
  assert (H1' := H1). destruct H1'.
  specialize (all_safe0 n). rewrite H2 in all_safe0.
  destruct_all. dependent destruction H5. unfold Commit in H7.
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
          dependent destruction H14.
          dec_eq_nats i i0.
          { destruct_all. congruence. }
          { rewrite <- H19, <- H20; easy. }
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
      dependent destruction H7.
      {
        exists ((i, UEvent (Some (CallEv m0))) :: x4).
        simpl. split. easy.
        eapply StepsMore with (st'':= p2m σ).
        2: easy.
        econstructor. econstructor. simpl.
        destruct_all.
        rewrite H13, H21, H15.
        econstructor; easy.
        simpl. intros.
        rewrite H16, H17; easy.
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
  dependent destruction H2. simpl in *.
  dependent destruction H2.
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
            dependent destruction H14; destruct_all; congruence.
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
      dependent destruction H7; destruct_all.
      {
        exists ((i, UEvent (Some (CallEv m0))) :: x5).
        split. easy.
        econstructor. 2: exact H19.
        econstructor. econstructor.
        econstructor; simpl.
        rewrite H12. easy.
        rewrite H20, H14. easy.
        simpl. intros.
        rewrite H15, H16; easy.
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
  dependent destruction H2. simpl in *.
  dependent destruction H2.
  assert (H1' := H1). move H1 at bottom. destruct H1.
  specialize (all_safe0 n). rewrite H2 in all_safe0.
  destruct_all. dependent destruction H1.
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
  dependent destruction H2. simpl in *.
  dependent destruction H2.
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
  dependent destruction H2. simpl in *.
  dependent destruction H2.
  exists (fun σ =>
    exists ρ, ρs ρ /\
      ρ.(PRets) n = RetPoss m n0 /\
      ρ.(PCalls) n = CallDone m /\
      mapRetPoss n m n0 ρ σ).
  assert (H1' := H1). move H1' at top. move H1 at bottom.
  split.
  {
    destruct H1. specialize (all_safe0 n).
    rewrite H2 in all_safe0. destruct_all.
    dependent destruction H1.
    rewrite <- rtp_prId in H5. unfold ReltToPrec in H5.
    destruct_all. apply H1 in H5. clear H1. psimpl.
    unfold Returned in H5.
    eassert _.
    { apply H5. exact H2. exact H0. }
    psimpl.
    exists (retPoss n x0), x0. split. easy.
    unfold mapRetPoss. cbn. rewrite eqb_id.
    repeat split; (easy || apply differ_pointwise_trivial).
  }
  split.
  {
    destruct H1.
    specialize (all_safe0 n). rewrite H2 in all_safe0. destruct_all.
    dependent destruction H1.
    constructor. constructor. intros.
    do 2 pdestruct H5.
    eassert ((Qs n A m n0 ->> PrecToRelt (Returned n m)) x4 x5 s ρs).
    {
      apply H1.
      psplit. 2: exact H7.
      split. 2: easy.
      easy.
    }
    dec_eq_nats i n.
    {
      rewrite <- x.
      split. split.
      { easy. }
      {
        intros. destruct_all. subst. simpl.
        unfold mapRetPoss in H13. easy.
      }
      {
        intros.
        eapply H.(switch_code) with (m1:=m) (v:=n0).
        pdestruct H9.
        psplit. psplit. unfold ReltToPrec.
        repeat eexists. exact H5. exact H9. exact H10.
        split.
        unfold PrecToRelt, Returned in H10. psimpl.
        apply H10. easy.
        split.
        split. 2: easy.
        constructor; easy.
        easy.
      }
    }
    {
      move H1' at bottom. destruct H1'. specialize (all_safe0 i).
      rewrite <- H3. 2: easy.
      pdestruct H9. unfold PrecToRelt, Returned in H11. destruct_all.
      remember (fst s i). destruct t0.
      {
        unfold TIdle in *. destruct_all.
        unfold mapRetPoss. split.
        rewrite <- H3. 2: easy. split. easy.
        intros. psimpl. rewrite H24, H25; try easy.
        apply H16. easy.
        intros. apply H.(P_stable).
        psplit. apply H15.
        eapply H.(Ret_in_R) with (i:=n). easy. subst.
        eexists _, m, n0.
        split.
        {
          apply H11. easy.
        }
        split.
        {
          split; cbn.
          econstructor; easy.
          easy.
        }
        split. easy.
        intros. psimpl.
        repeat split; try easy.
      }
      {
        destruct_all.
        exists (x8 ->> R i).
        split.
        {
          eapply (weakenSafe (P:= prComp (Ps i A0 m0) (TInvoke M i A0 m0) ->> x8)).
          2: easy.
          unfold sub, subRelt. intros.
          pdestruct H17.
          psplit.
          exact H17.
          apply H16 in H18.
          easy.
        }
        split.
        {
          rewrite <- precCompAssoc.
          psplit.
          exact H15. subst.
          apply H.(Ret_in_R) with (i:=n). easy.
          eexists _, m, n0.
          split.
          {
            apply H11. easy.
          }
          split.
          econstructor; simpl. econstructor; easy. easy.
          split. easy.
          intros. destruct_all. subst. simpl.
          easy.
        }
        {
          unfold sub, subRelt. intros.
          pdestruct H17. apply H16 in H17.
          exists x9, x10. easy.
        }
      }
      {
        destruct_all.
        exists (x8 ->> R i), (fun v => x9 v ->> R i).
        intros. specialize (H14 v). destruct_all.
        split.
        {
          eapply weakenCommitPre with (P:= prComp (Ps i B om) (TInvoke M i B om) ->> x8).
          unfold sub, subRelt. intros.
          pdestruct H19.
          apply H18 in H20.
          exists x10, x11. easy.
          eapply weakenCommit with (Q:= x9 v).
          unfold sub, subRelt. intros.
          psplit. 2: apply H.(R_refl). easy.
          easy.
        }
        split.
        {
          eapply (weakenSafe (P:= prComp (Ps i B om) (TInvoke M i B om) ->> x8 ->> x9 v)).
          unfold sub, subRelt. intros.
          pdestruct H19. pdestruct H20.
          apply H17 in H21. apply H18 in H20.
          psplit. exact H19.
          exists x12, x13. easy.
          easy.
        }
        split.
        {
          rewrite <- precCompAssoc.
          psplit. exact H16. subst.
          apply H.(Ret_in_R) with (i:=n). easy.
          eexists _, m, n0.
          split.
          {
            apply H11. easy.
          }
          split. econstructor. econstructor; easy. easy.
          split. easy.
          intros. destruct_all. subst. simpl.
          easy.
        }
        split.
        {
          unfold sub, subRelt. intros.
          pdestruct H19. apply H17 in H19.
          exists x10, x11. easy.
        }
        {
          unfold sub, subRelt. intros.
          pdestruct H19. apply H18 in H19.
          exists x10, x11. easy.
        }
      }
    }
  }
  {
    intros. destruct_all. subst. simpl.
    exists x1. split. easy.
    exists [(n, OEvent (RetEv m n0))].
    split. easy.
    destruct H1.
    specialize (all_safe0 n). rewrite H2 in all_safe0.
    destruct_all.
    dependent destruction H1.
    econstructor. 2: constructor.
    unfold mapRetPoss in H8. psimpl.
    unfold InterStep, ThreadsStep.
    destruct x1, σ. cbn in *.
    split. 2: easy.
    econstructor. cbn.
    rewrite H7, H6, H8. econstructor; easy.
    cbn. intros. rewrite H14, H15; easy.
  }
}
Qed.

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

Definition idImpl_constraint {F} (s : ThreadState F F) :=
  s = Idle \/
  (exists B m, s = Cont m (Bind (B:=B) m Return)) \/
  (exists A m, s = UCall (A:=A) m m Return) \/
  (exists A m v, s = Cont (A:=A) m (Return v)).

Lemma help_projOver {T E1 E2 E3 F} :
  forall (p : Trace (ThreadLEvent T E1 F)),
  forall (q : Trace (ThreadLEvent T E2 F)),
  forall (r : Trace (ThreadLEvent T E3 F)),
  forall i e,
  projOver p = projOver q ++ [(i, e)] ++ projOver r ->
  exists q' r',
    p = q' ++ [(i, OEvent e)] ++ r' /\
    projOver q = projOver q' /\
    projOver r = projOver r'.
Admitted.

Lemma get_idImpl_constraint {T F} {VF : Spec T F} :
  forall p st,
  InterSteps idImpl (allIdle, Init VF) p st ->
  forall i, idImpl_constraint (fst st i).
intros.
assert (forall i, @idImpl_constraint F (allIdle (T:=T) i)).
left. easy.
generalize dependent (@allIdle T F F).
generalize dependent (Init VF).
induction p; intros.
dependent destruction H. cbn. easy.
dependent destruction H. destruct st''.
apply IHp in H0. clear IHp. easy.
intros. specialize (H1 i0).
clear H0. unfold InterStep, ThreadsStep in H.
cbn in *. destruct_all. dependent destruction H.
unfold ThreadStep in H. destruct a. cbn in *.
dec_eq_nats i0 n.
2:{ rewrite <- H0; easy. }
destruct l; dependent destruction H.
rewrite <- x0 in H2. rewrite <- x.
unfold idImpl_constraint in H2.
destruct H2. discriminate.
destruct H. destruct_all. dependent destruction H.
right. right. left. repeat econstructor.
destruct H. destruct_all. discriminate.
destruct_all. discriminate.
rewrite <- x0 in H2. rewrite <- x.
clear IHp.
unfold idImpl_constraint in *.
destruct H2. discriminate.
destruct H. destruct_all. discriminate.
destruct H. destruct_all. dependent destruction H.
right. right. right. repeat econstructor.
destruct_all. discriminate.
rewrite <- x0 in H2. rewrite <- x.
clear IHp. unfold idImpl_constraint in H2.
destruct H2. discriminate.
destruct H. destruct_all. discriminate.
destruct H. destruct_all. discriminate.
destruct H. destruct_all. discriminate.
rewrite <- x0 in H2. rewrite <- x.
clear IHp. unfold idImpl_constraint in *.
destruct H2. right. left. repeat econstructor.
destruct H. destruct_all. discriminate.
destruct H. destruct_all. discriminate.
destruct H. destruct_all. discriminate.
rewrite <- x0 in H2. rewrite <- x.
clear IHp. unfold idImpl_constraint in *.
destruct H2. discriminate.
destruct H. destruct_all. discriminate.
destruct H. destruct_all. discriminate.
destruct H. destruct_all. dependent destruction H.
left. easy.
Qed.

Lemma m2p2m {T F} {VF : Spec T F} {s : InterState F VF} :
  (forall i, idImpl_constraint (fst s i)) ->
  p2m (m2p s) = s.
intros.
unfold p2m, m2p. destruct s. f_equal.
extensionality i. cbn. specialize (H i).
unfold idImpl_constraint in H. cbn in *.
destruct H. rewrite H. easy.
destruct H. destruct_all. rewrite H. easy.
destruct H. destruct_all. rewrite H. easy.
destruct_all. rewrite H. easy.
Qed.

Variant FullPossStep {T F} {VF : Spec T F} i (ρ σ : Poss VF) : LEvent F F -> Prop :=
| PPendCall A (m : F A) :
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
  ρ.(PCalls) i = CallDone m ->
  σ.(PCalls) i = CallIdle ->
  ρ.(PRets) i = RetPoss m v ->
  σ.(PRets) i = RetIdle ->
  FullPossStep i ρ σ (OEvent (RetEv m v)).

(* Inductive FullPossSteps {T F} {VF : Spec T F} : Poss VF -> Trace (ThreadLEvent F F) -> Poss VF -> Prop :=
| PossStepsRefl ρ :
    FullPossSteps ρ [] ρ
| PossStepsStep i e p ρ σ τ :
    FullPossStep i ρ σ e ->
    (forall j, i <> j -> PCalls ρ j = PCalls σ j) ->
    (forall j, i <> j -> PRets ρ j = PRets σ j) ->
    FullPossSteps σ p τ ->
    FullPossSteps ρ ((i, e) :: p) τ. *)

(* Definition comp_inv {T E F}
  (VE : Spec T E) (VF : Spec T F) (M : Impl E F)
  : Name T -> Prec VE VF :=
  fun i t σs =>
  exists p,
    InterSteps (spec:=VE) M (allIdle, Init VE) p t /\
    σs = (fun σ =>
      exists q,
        projOver p = projOver q /\
        FullPossSteps initPoss q σ).

Definition comp_rely {E F}
  (VE : Spec E) (VF : Spec F) (M : Impl E F)
  : ThreadName -> Relt VE VF :=
  fun i s ρs t σs =>
    exists p,
      OtherSteps (spec:=VE) i M s p t /\
      forall σ,
        (exists ρ, ρs ρ /\ exists q,
          projOver p = projOver q /\
          InterSteps (spec:=VF) idImpl (p2m ρ) q (p2m σ)) ->
        σs σ.

Definition comp_guar {E F}
  (VE : Spec E) (VF : Spec F) (M : Impl E F)
  : ThreadName -> Relt VE VF :=
  fun i s ρs t σs =>
    forall j, i <> j -> comp_rely VE VF M j s ρs t σs.

Ltac set_ext x := extensionality x; apply propositional_extensionality.

Theorem completeness {E F} (lay : Layer E F) VF :
  (forall A (m : F A) v,
    lay.(LImpl) _ m <> Return v) ->
  Lin (overObj lay) VF ->
  exists R G Ps Qs,
    VerifyImpl lay.(USpec) VF R G Ps lay.(LImpl) Qs.
unfold Lin, KConc, specRefines, Incl, IsTraceOfSpec.
repeat rewrite projInterSteps.
destruct lay. cbn. intro WF. intros.
rename USpec into VE. rename LImpl into M.
assert (
  forall st p,
    InterSteps M (allIdle, Init VE) p st ->
    exists st' q,
      projOver p = projOver q /\
      InterSteps idImpl (allIdle, Init VF) q st'
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
    dependent destruction H0.
    left. easy.
    unfold InterStep, ThreadsStep in H0. destruct_all.
    dependent destruction H0. unfold ThreadStep in H0.
    destruct ev, l; cbn in *.
    dependent destruction H0.
    right. repeat econstructor. 
  }
  apply H in H1. clear H. destruct_all.
  exists x, x0. easy.
}
clear H. rename H0 into H.
exists
  (comp_rely VE VF M),
  (comp_guar VE VF M),
  (fun i _ _ => comp_inv VE VF M i),
  (fun i _ _ _ _ _ => comp_inv VE VF M i).
constructor.
{
  unfold comp_rely.
  intros. exists []. repeat constructor.
  
}
{
  unfold comp_rely, sub, subRelt. intros. psimpl.
  exists (x2 ++ x1). split.
  unfold OtherSteps. rewrite <- Steps_app.
  exists x. easy. intros.
  admit.
}
{
  unfold comp_guar, sub, subRelt. intros. psimpl.
  apply H1. easy.
}
{
  unfold sub, subRelt, InvokeAny, TInvoke, TIdle, comp_rely, comp_inv.
  intros. psimpl.
  exists [(i, OEvent (CallEv x0))]. split.
  {
    econstructor. 2: constructor. split. easy.
    destruct H2. cbn in *.
    split. 2: easy.
    econstructor; easy.
  }
  {
    intros. psimpl.
  }
}
{
  unfold sub, subRelt, ReturnAny, TReturn, comp_rely, comp_inv.
  intros. psimpl. destruct s, t. psimpl.
  exists [(i, OEvent (RetEv x0 x1))]. split.
  {
    econstructor. 2: constructor. split. easy.
    split. 2: easy.
    destruct H2. cbn in *.
    constructor; easy.
  }
  {
    admit.
  }
}
{
  unfold comp_inv. exists nil.
  split. constructor.
  intros. psimpl.
  set_ext ρ. split; intros; psimpl.
  exists []. repeat constructor.
  admit.
}
{
  unfold Stable, stablePrec, sub, subPrec. intros. psimpl.
  admit.
}
{
  unfold Stable, stableRelt, sub, subRelt.
  admit.
}
{
  unfold sub, subPrec, TReturn, comp_inv, Returned. intros. psimpl.
  destruct H2. cbn in *. dependent destruction H2.
  exists (x5 ++ [(i, OEvent (RetEv m1 v))]). split.
  {
    unfold InterSteps. rewrite <- Steps_app.
    exists x0. split. easy.
    econstructor. 2: constructor.
    split. 2: easy.
    econstructor; cbn. econstructor; easy. easy.
  }
  {
    intros. psimpl.
    admit.
  }
}
{
  unfold VerifyProg. intros. rewrite paco_eqv.
  assert (prComp (comp_inv VE VF M i) (TInvoke M i A m) ->> comp_rely VE VF M i ==> (fun _ _ => comp_inv_wk VE VF M i)).
  {
    unfold sub, subRelt, comp_inv, comp_rely, TInvoke, TIdle.
    intros. psimpl.
    exists (x2 ++ (i, OEvent (CallEv m)) :: x1). split.
    {
      unfold InterSteps. rewrite <- Steps_app.
      exists s. split. easy.
      eapply StepsMore with (st'':=x).
      destruct H3. cbn in *.
      split. 2: easy.
      constructor; easy.
      eapply other_inter. exact H1.
    }
    {
      intros. psimpl. apply H7. clear H7.
      rewrite projOver_app in H5. cbn in H5.
      apply help_projOver in H5. psimpl.
      unfold InterSteps in H8.
      rewrite <- Steps_app in H8. destruct_all.
      dependent destruction H8.
      unfold InterStep, ThreadsStep, StateStep in H8.
      destruct_all. cbn in *. dependent destruction H8.
      cbn in *. dependent destruction H8.
      exists (m2p st''). split.
      {
        exists (m2p x0). split.
        exists x3. rewrite m2p2m. easy.
        eapply get_idImpl_constraint. exact H5.
        cbn. rewrite <- x. cbn.
        split. easy. split. easy. split. easy. split.
        unfold differ_pointwise. intros. rewrite H10; easy.
        unfold differ_pointwise. intros. rewrite H10; easy.
      }
      {
        rewrite m2p2m.
        2:{
          eapply get_idImpl_constraint with
            (p:= x3 ++ [(i, OEvent (CallEv m))]).
          unfold InterSteps. rewrite <- Steps_app.
          exists x0. split. easy.
          econstructor. 2: constructor.
          split. 2: easy.
          constructor; cbn. constructor; easy. easy.
        }
        exists x4. easy.
      }
    }
  }
  generalize dependent (prComp (comp_inv VE VF M i) (TInvoke M i A m) ->> comp_rely VE VF M i).
  generalize dependent (M _ m).
  pcofix rec.
  intros. destruct p; pfold.
  admit.
  admit.
  admit.
} *)