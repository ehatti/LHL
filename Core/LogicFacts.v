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

Definition initIs {E F} {VE : Spec E} {VF : Spec F} : ThreadName -> Relt VE VF :=
  fun _ s ρ t σ =>
    s = t /\ ρ = σ /\
    t = (allIdle, Init VE) /\
    σ = eq initPoss.

Theorem soundness {E F} (lay : Layer E F) VF R G Ps Qs
  (Rid : forall i s ρ, R i s ρ s ρ)
  (Rtrans : forall i, (R i ->> R i) ==> R i) :
  VerifyImpl lay.(USpec) VF R G Ps lay.(LImpl) Qs ->
  Lin (overObj lay) VF.
intros.
destruct_all.
unfold Lin, KConc.
destruct lay.
simpl in *.
unfold VerifyImpl in H.
destruct_all.
rename USpec into VE.
unfold specRefines, Incl, IsTraceOfSpec.
intros.
destruct_all.
repeat rewrite projInterSteps in *.
destruct_all.
simpl in *.
cut (
  exists q t,
    a = projOver q /\
    InterSteps idImpl (allIdle, Init VF) q t
).
{
  intros.
  destruct_all.
  subst.
  exists x2, x1.
  repeat split; try easy.
  dependent destruction H7.
  left. easy.
  dependent destruction H3.
  unfold ThreadsStep in H3.
  simpl in *.
  dependent destruction H3.
  destruct ev, l; simpl in *.
  dependent destruction H3.
  right. repeat econstructor.
}
subst. clear H5.
cut (
  forall (p : Trace (ThreadLEvent E F)) t,
  forall s : InterState F VE,
  InterSteps LImpl s p t ->
  forall ρs : PossSet VF,
  (exists ρ, ρs ρ) ->
  forall Is : ThreadName -> Relt VE VF,
  (forall i, ReltToPrec (Is i) s ρs) ->
  (forall i, Stable (R i) (Is i)) ->
  (forall i,
    match fst s i with
    | Idle =>
      forall A m, Ps i A m s ρs
    | Cont m C =>
      SafeProg i (R i) (G i) (Is i) C (Qs i _ m)
    | UCall om um k =>
      forall v,
        exists QR,
          Commit i (G i) (Is i) (RetEv um v) (QR v) /\
          SafeProg i (R i) (G i) (Is i ->> QR v) (k v) (Qs i _ om) /\
          Stable (R i) QR 
    end) ->
  exists σs,
    (exists σ, σs σ) /\
    forall σ, σs σ ->
      exists ρ, ρs ρ /\
        exists q,
          projOver q = projOver p /\
          InterSteps idImpl (poss_to_mod ρ) q (poss_to_mod σ)
).
{
  intros.
  apply H3 with (ρs:= eq initPoss) (Is:=R) in H4. clear H3.
  2:{ exists initPoss. easy. }
  2:{ unfold initIs, ReltToPrec. repeat econstructor. apply Rid. }
  2:{ split; apply Rtrans. }
  2:{
    simpl. intros.
    specialize (H0 i A m).
    easy.
  }
  destruct_all.
  apply H4 in H3. clear H4.
  destruct_all.
  subst.
  exists x4, (poss_to_mod x2).
  easy.
}
clear H4 x0 x.
intros p t.
induction p; simpl in *; intros.
{
  exists ρs.
  intros.
  dependent destruction H3.
  split.
  easy.
  intros.
  destruct_all.
  exists σ.
  split. easy.
  exists [].
  repeat constructor.
}
{
  dependent destruction H3.
  unfold InterStep, ThreadsStep, StateStep in H3. destruct_all.
  destruct a. simpl in *.
  dependent destruction H3. simpl in *.
  unfold ThreadStep in H3.
  assert (H10' := H10). move H10' at top.
  specialize (H10 n).
  destruct l; simpl in *.
  destruct ev; simpl in *.
  3: dependent destruction H3.
  dependent destruction H3.
  {
    rewrite H3 in H10.
    dependent destruction H10.
    assert (H7' := H7).
    unfold Commit in H12. apply H12 with (t:=st'') in H7. clear H12.
    destruct_all.
    2:{ unfold differ_pointwise. symmetry. apply H4. easy. }
    2:{ econstructor. exact H3. easy. }
    2:{ easy. }
    eapply IHp with
      (ρs:=x1)
      (Is:=fun i =>
        if i =? n then
          Is i ->> QI
        else
          Is i ->> R i)
      in H5.
    clear IHp.
    (* start side conditions *)
    2:{ exists x2. easy. }
    2:{
      intros.
      specialize (H7' i). unfold ReltToPrec in H7'.
      destruct_all.
      dec_eq_nats i n.
      {
        rewrite eqb_id.
        repeat eexists.
        exact H16. easy.
      }
      {
        rewrite eqb_nid.
        repeat eexists.
        exact H16.
        eapply H with (i:=n). easy.
        easy.
        easy.
      }
    }
    2:{
      intros.
      move H8 at bottom.
      specialize (H8 i).
      dec_eq_nats i n.
      {
        rewrite eqb_id.
        apply reltCompStable; easy.
      }
      {
        rewrite eqb_nid.
        apply reltCompStable.
        easy.
        unfold Stable, stableRelt.
        split; apply Rtrans.
        easy.
      }
    }
    2:{
      intros.
      dec_eq_nats i n.
      {
        rewrite eqb_id in *.
        rewrite <- x.
        intros.
        specialize (H13 v).
        exists QR.
        rewrite reltCompAssoc.
        easy.
      }
      {
        rewrite eqb_nid.
        move H10' at bottom.
        specialize (H10' i).
        rewrite <- H4.
        2: easy. 2: easy.
        destruct (fst s i).
        {
          intros.
          specialize (H0 i _ m). destruct H0, H17.
          apply H17.
          repeat econstructor.
          apply H10'.
          eapply H.
          symmetry. exact H16.
          easy.
        }
        apply (weakenSafe (P:= Is i)).
        apply H8.
        easy.
        intros.
        specialize (H10' v).
        destruct_all.
        exists x3.
        split.
        {
          unfold Commit. intros.
          apply H17.
          unfold ReltToPrec in H20. unfold ReltToPrec.
          destruct_all.
          exists x4, x5.
          apply H8.
          easy.
          easy.
          easy.
          easy.
        }
        split.
        {
          apply (weakenSafe (P:= Is i ->> x3 v)).
          unfold sub, subRelt, ReltCompose. intros. destruct_all.
          repeat econstructor.
          move H8 at bottom.
          specialize (H8 i). destruct H8.
          apply H23.
          repeat econstructor.
          exact H20.
          exact H22.
          easy.
          easy.
        }
        {
          easy.
        }
      }
    }
    (* end side conditions *)
    destruct_all.
    exists x3.
    split. exists x4. easy.
    intros.
    apply H16 in H17. clear H16. destruct_all.
    apply H12 in H16. clear H12. destruct_all.
    exists x7.
    split. easy.
    clear H12.
    induction H16.
    { exists x6. easy. }
    {
      apply IHPossSteps in H18. clear IHPossSteps.
      destruct_all.
      dependent destruction H12; destruct_all.
      {
        exists ((i, UEvent (Some (CallEv m))) :: x5).
        simpl. split. easy.
        eapply StepsMore with (st'':= poss_to_mod σ0).
        repeat econstructor.
        simpl. rewrite H16. easy.
        simpl. rewrite H25, H18. easy.
        simpl. intros.
        rewrite H19, H20. easy.
        easy.
        easy.
        easy.
        easy.
      }
      {
        exists ((i, UEvent (Some (RetEv m v))) :: x5).
        simpl. split. easy.
        eapply StepsMore with (st'':= poss_to_mod σ0).
        repeat econstructor.
        simpl. rewrite H16, H18. easy.
        simpl. rewrite H17, H19. easy.
        simpl. intros.
        rewrite H20, H21. easy.
        easy.
        easy.
        easy.
        easy.
      }
    }
  }
  {
    rewrite H3 in H10. specialize (H10 v). destruct_all.
    assert (H7' := H7).
    specialize (H7 n).
    unfold Commit in H10. apply H10 with (t:=st'') in H7. clear H10.
    destruct_all.
    2:{ unfold differ_pointwise. symmetry. apply H4. easy. }
    2:{ econstructor. exact H3. easy. }
    2:{ easy. }
    eapply IHp with
      (ρs:=x2)
      (Is:=fun i =>
        if i =? n then
          Is i ->> x1 v
        else
          Is i ->> R i)
      in H5.
    clear IHp.
    destruct_all.
    (* start side conditions *)
    2:{ exists x3. easy. }
    2:{
      intros.
      specialize (H7' i). unfold ReltToPrec in H7'.
      destruct_all.
      dec_eq_nats i n.
      {
        rewrite eqb_id.
        repeat eexists.
        exact H15. easy.
      }
      {
        rewrite eqb_nid.
        repeat eexists.
        exact H15.
        eapply H with (i:=n). easy.
        easy.
        easy.
      }
    }
    2:{
      intros.
      move H8 at bottom.
      specialize (H8 i).
      dec_eq_nats i n.
      {
        rewrite eqb_id.
        apply reltCompStable.
        easy.
        apply H12.
      }
      {
        rewrite eqb_nid.
        apply reltCompStable.
        easy.
        unfold Stable, stableRelt.
        split; apply Rtrans.
        easy.
      }
    }
    2:{
      intros.
      dec_eq_nats i n.
      {
        rewrite <- x, eqb_id.
        easy.
      }
      {
        rewrite eqb_nid.
        2: easy.
        move H10' at bottom.
        specialize (H10' i).
        rewrite <- H4. 2: easy.
        destruct (fst s i).
        {
          intros.
          specialize (H0 i _ m). destruct H0, H16.
          apply H16.
          repeat econstructor.
          apply H10'.
          eapply H.
          symmetry. exact H15.
          easy.
        }
        {
          apply (weakenSafe (P:=Is i)).
          apply H8.
          easy.
        }
        intros.
        specialize (H10' v0).
        destruct_all.
        exists x4.
        split.
        {
          unfold Commit. intros.
          apply H16.
          move H8 at bottom.
          specialize (H8 i). destruct H8.
          unfold ReltToPrec in H19. unfold ReltToPrec.
          destruct_all.
          repeat eexists.
          apply H23. exact H19.
          easy.
          easy.
          easy.
        }
        split.
        {
          apply (weakenSafe (P:= Is i ->> x4 v0)).
          unfold sub, subRelt, ReltCompose. intros. destruct_all.
          repeat econstructor.
          exact H19.
          specialize (H18 v0). destruct H18.
          apply H18.
          repeat eexists.
          exact H21.
          exact H20.
          easy.
        }
        {
          easy.
        }
      }
    }
    (* end side conditions *)
    exists x4. split. exists x5. easy.
    intros.
    apply H15 in H16. clear H15. destruct_all.
    apply H10 in H15. clear H10. destruct_all.
    exists x8. split. easy.
    clear H10.
    induction H15.
    { exists x7. easy. }
    {
      apply IHPossSteps in H17. clear IHPossSteps.
      destruct_all.
      dependent destruction H10; destruct_all.
      {
        exists ((i, UEvent (Some (CallEv m))) :: x6).
        simpl. split. easy.
        eapply StepsMore with (st'':= poss_to_mod σ0).
        repeat econstructor.
        simpl. rewrite H15. easy.
        simpl. rewrite H24, H17. easy.
        simpl. intros.
        rewrite H18, H19. easy.
        easy.
        easy.
        easy.
        easy.
      }
      {
        exists ((i, UEvent (Some (RetEv m v0))) :: x6).
        simpl. split. easy.
        eapply StepsMore with (st'':= poss_to_mod σ0).
        repeat econstructor.
        simpl. rewrite H15, H17. easy.
        simpl. rewrite H16, H18. easy.
        simpl. intros.
        rewrite H19, H20. easy.
        easy.
        easy.
        easy.
        easy.
      }
    }
  }
  {
    dependent destruction H3.
    apply IHp with (s:=st'') (Is:=Is).
    easy.
    exists x0. easy.
    2:{ easy. }
    2:{
      admit.
    }
    {
      admit.
    }
  }
  {
    rewrite H3 in H10.
    specialize (H10 A m).
    apply IHp with
      (ρs:=ρs)
      (Is:=fun i =>
        if i =? n then
          prComp (Ps n A m <<- TInvoke LImpl i _ m) id
        else
          Is i)
      in H5. clear IHp.
    2:{ exists x0. easy. }
    2:{
      intros.
      dec_eq_nats i n.
      {
        rewrite eqb_id.
        unfold ReltToPrec, prComp, PrecCompose.
        do 2 eexists.
        split. 2: easy.
        do 3 eexists.
        2:{
          unfold TInvoke.
        }
      }
    }
  }
  {

  }
}