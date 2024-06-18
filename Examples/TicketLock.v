From LHL.Core Require Import
  Program
  ProgramRules
  Specs
  Logic
  LogicFacts
  Tensor
  Traces
  Linearizability.

From LHL.Examples Require Import
  LockSpec
  FAISpec
  YieldSpec
  CounterSpec
  VarSpec.

From LHL.Util Require Import
  Tactics
  TransUtil
  Util.

From Coq Require Import
  Arith.PeanoNat
  Program.Equality
  Logic.FunctionalExtensionality
  Logic.PropExtensionality
  Logic.Classical_Prop.

Definition Underlay := FAISig |+| CounterSig |+| VarSig nat.

Definition acq : Prog Underlay unit :=
  my_tick <- call FAI;
  call (SetVar my_tick);;
  while (cur_tick <- call Get; ret (negb (cur_tick =? my_tick)))
    skip;;
  call ClrVar.

Definition rel : Prog Underlay unit :=
  call Inc.

Definition ticketLockImpl : Impl Underlay LockSig :=
  fun _ m => match m with
  | Acq => acq
  | Rel => rel
  end.

Definition E := Underlay.
Definition F := LockSig.
Definition VE := tensorSpec faiSpec (tensorSpec counterSpec (varSpec nat)).
Definition VF := lockSpec.

Definition Relt := Relt VE VF.
Definition Prec := Prec VE VF.
Definition Post := Post VE VF.

Definition countState (s : @InterState E F VE) : State counterSpec :=
  fst (snd (snd s)).
Definition varState (s : @InterState E F VE) : State (varSpec nat) :=
  snd (snd (snd s)).

Definition newtkt (s : @InterState E F VE) : nat :=
  fst (fst (snd s)).
Definition ctrval (s : @InterState E F VE) : nat :=
  match countState s with
  | CounterDef n _ => n
  | CounterUB => 0
  end.
Definition mytkt i (s : @InterState E F VE) : option nat :=
  match snd (snd (snd s)) i with
  | VarUnset => None
  | VarSet n _ => Some n
  end.

Definition Inv (i : ThreadName) : Prec :=
  fun s ρs => exists ρ, ρs = eq ρ /\
    countState s <> CounterUB /\
    (forall tkt,
      Some tkt = mytkt i s ->
      ctrval s <= tkt) /\
    ctrval s <= newtkt s /\
    (mytkt i s = Some (ctrval s) ->
      owner (PState ρ) = Some i \/ owner (PState ρ) = None) /\
    (newtkt s = ctrval s ->
      PState ρ = LockUnowned) /\
    (owner (PState ρ) = Some i ->
      mytkt i s = Some (ctrval s)).

Definition Acqed (i : ThreadName) : Prec := fun s ρs =>
  exists ρ, ρs = eq ρ /\
  (owner (PState ρ) = Some i /\ Inv i s ρs) \/
  (owner (PState ρ) <> Some i).

Definition Reled (i : ThreadName) : Prec := fun s ρs =>
  exists ρ, ρs = eq ρ /\
  (owner (PState ρ) <> Some i /\ Inv i s ρs) \/
  (owner (PState ρ) = Some i).

Definition Precs (i : ThreadName) {A} (m : LockSig A) : Prec :=
  fun s ρs => exists ρ, ρs = eq ρ /\
    match m with
    | Acq =>
        owner (PState ρ) <> Some i ->
          Inv i s ρs
    | Rel =>
        owner (PState ρ) = Some i ->
          Inv i s ρs
    end.

Definition Posts (i : ThreadName) {A} (m : LockSig A) : Post A :=
  fun _ s ρs t σs => forall ρ, ρs = eq ρ -> exists σ, σs = eq σ /\
    match m with
    | Acq =>
        owner (PState ρ) <> Some i ->
          owner (PState σ) = Some i /\
          Inv i t σs
    | Rel =>
        owner (PState ρ) = Some i ->
          owner (PState σ) <> Some i /\
          Inv i t σs
    end.

Definition ManyInvokeReturn i : Relt :=
  RTC (fun s ρs t σs =>
    exists j, j <> i /\
      (InvokeAny ticketLockImpl j s ρs t σs \/
       ReturnAny ticketLockImpl j s ρs t σs)).

Definition Rely (i : ThreadName) : Relt :=
  fun s ρs t σs => forall ρ, ρs = eq ρ -> exists σ, σs = eq σ /\ (
    ManyInvokeReturn i s ρs t σs \/
    (countState s <> CounterUB ->
      countState t <> CounterUB) /\
    ((forall tkt, Some tkt = mytkt i s -> ctrval s <= tkt) ->
      forall tkt',
      Some tkt' = mytkt i t ->
      ctrval t <= tkt') /\
    (ctrval s <= newtkt s ->
      ctrval t <= newtkt t) /\
    ((mytkt i s = Some (ctrval s) -> owner (PState ρ) = Some i \/ owner (PState ρ) = None) ->
      mytkt i t = Some (ctrval t) ->
      owner (PState σ) = Some i \/ owner (PState σ) = None) /\
    ((newtkt s = ctrval s -> PState ρ = LockUnowned) ->
      newtkt t = ctrval t ->
      PState σ = LockUnowned) /\
    ((owner (PState ρ) = Some i -> mytkt i s = Some (ctrval s)) ->
      owner (PState σ) = Some i ->
      mytkt i t = Some (ctrval t)) /\
    (owner (PState ρ) = Some i <-> owner (PState σ) = Some i) /\
    (owner (PState ρ) = Some i ->
      PState ρ = PState σ /\
      countState s = countState t) /\
    (owner (PState ρ) <> Some i <-> owner (PState σ) <> Some i) /\
    fst s i = fst t i
  ).

Definition Guar (i : ThreadName) : Relt :=
  fun s ρs t σs =>
    forall j, i <> j -> Rely j s ρs t σs.

(* Extra lemmas *)

Lemma tollens {P Q : Prop} :
  ~Q -> (P -> Q) -> ~P.
tauto.
Qed.

Lemma eq_inj {A} :
  forall x y : A, eq x = eq y -> x = y.
intros.
assert (forall z, eq x z = eq z y).
{
  intros. apply propositional_extensionality.
  split; intros.
  rewrite H in H0. easy.
  rewrite H. easy.
}
specialize (H0 x).
rewrite <- H0. easy.
Qed.

Lemma newtkt_eq :
  forall s t : @InterState E F VE,
  snd s = snd t ->
  newtkt s = newtkt t.
unfold newtkt. congruence.
Qed.

Lemma ctrval_eq :
  forall s t : @InterState E F VE,
  snd s = snd t ->
  ctrval s = ctrval t.
unfold ctrval, countState. intros.
rewrite H. easy.
Qed.

Lemma mytkt_eq i :
  forall s t : @InterState E F VE,
  snd s = snd t ->
  mytkt i s = mytkt i t.
unfold mytkt. intros.
rewrite H. easy.
Qed.

Lemma countState_eq :
  forall s t : @InterState E F VE,
  snd s = snd t ->
  countState s = countState t.
unfold countState. intros.
rewrite H. easy.
Qed.

Lemma cntSt_to_ctrval :
  forall s t : @InterState E F VE,
  countState s = countState t ->
  ctrval s = ctrval t.
unfold ctrval. intros.
rewrite H. easy.
Qed.

Lemma noStateChange :
  forall i s ρs t σs,
  ManyInvokeReturn i s ρs t σs ->
  fst s i = fst t i /\
  snd s = snd t /\
  forall σ, σs σ ->
    exists ρ, ρs ρ /\
      PState ρ = PState σ.
intros.
induction H.
{
  split. easy.
  split. easy.
  intros. exists σ. easy.
}
{
  clear H0.
  destruct_all.
  destruct H3.
  {
    unfold InvokeAny, TInvoke, mapInvPoss in H3. psimpl.
    destruct H4. cbn in *.
    split. transitivity (fst t i). apply H7. easy. easy.
    split. transitivity (snd t); easy.
    intros. apply H2 in H8. clear H2. psimpl.
    destruct H6. clear H6.
    apply H9 in H2. psimpl.
    exists x3. split. easy.
    congruence.
  }
  {
    unfold ReturnAny, TReturn, mapRetPoss in H3. psimpl.
    destruct H3. cbn in *.
    split. transitivity (fst t i). apply H6. easy. easy.
    split. transitivity (snd t); easy.
    intros. apply H2 in H7. clear H2. psimpl.
    destruct H5. clear H5.
    apply H8 in H2. psimpl.
    exists x4. split. easy.
    congruence.
  }
}
Qed.

Lemma Inv_stable :
  forall i, Stable (Rely i) (Inv i).
unfold Stable, stablePrec, sub, subPrec, Rely, Inv. intros.
psimpl.
specialize (H0 x1 eq_refl). destruct_all. subst.
exists x0. split. easy.
destruct H0.
{
  apply noStateChange in H. destruct_all.
  specialize (H7 x0 eq_refl). destruct_all. subst.
  rewrite <- H8. symmetry in H0.
  repeat rewrite (countState_eq _ _ H0).
  repeat rewrite (newtkt_eq _ _ H0).
  repeat rewrite (mytkt_eq _ _ _ H0).
  repeat rewrite (ctrval_eq _ _ H0).
  easy.
}
{
  destruct_all.
  repeat split; auto.
}
Qed.

Lemma Rely_pres_single :
  forall i s ρ t σs,
  Rely i s (eq ρ) t σs ->
  exists σ, σs = eq σ.
unfold Rely. intros.
specialize (H ρ eq_refl). psimpl.
exists x. easy.
Qed.

Lemma Rely_pres_not_owned :
  forall i s ρ t σ,
  Rely i s (eq ρ) t (eq σ) ->
  owner (PState σ) <> Some i <->
  owner (PState ρ) <> Some i.
unfold Rely. intros. specialize (H ρ eq_refl). psimpl.
apply eq_inj in H. subst.
destruct H0.
{
  apply noStateChange in H. psimpl.
  specialize (H1 x eq_refl). psimpl.
  rewrite H2. easy.
}
{
  psimpl. easy.
}
Qed.


Lemma Rely_pres_owned :
  forall i s ρ t σ,
  Rely i s (eq ρ) t (eq σ) ->
  owner (PState σ) = Some i <->
  owner (PState ρ) = Some i.
unfold Rely. intros. specialize (H ρ eq_refl). psimpl.
apply eq_inj in H. subst.
destruct H0.
{
  apply noStateChange in H. psimpl.
  specialize (H1 x eq_refl). psimpl.
  rewrite H2. easy.
}
{
  psimpl. easy.
}
Qed.

Lemma mapPossInv_pres_single :
  forall i ρ σs A (m : F A),
  mapPoss (VF:=VF) (eq ρ) σs (mapInvPoss i m) ->
  exists σ, σs = eq σ.
unfold mapInvPoss. intros.
destruct H. specialize (H ρ eq_refl). destruct_all.
exists x. extensionality x1. apply propositional_extensionality.
split; intros.
{
  apply H0 in H8. clear H0. destruct_all. subst.
  destruct x, x0, x1. cbn in *.
  f_equal.
  { congruence. }
  {
    extensionality k.
    dec_eq_nats i k.
    congruence.
    etransitivity.
    apply H5. easy.
    symmetry. apply H12. easy.
  }
  {
    extensionality k.
    dec_eq_nats i k.
    congruence.
    etransitivity.
    apply H6. easy.
    symmetry. apply H13. easy.
  }
}
{
  subst. easy.
}
Qed.

Lemma mapPossRet_pres_single :
  forall i ρ σs A (m : F A) v,
  mapPoss (VF:=VF) (eq ρ) σs (mapRetPoss i m v) ->
  σs = eq (retPoss i ρ).
unfold mapRetPoss. intros. destruct H.
specialize (H ρ eq_refl). destruct_all.
extensionality x0. apply propositional_extensionality.
split; intros.
{
  apply H0 in H8. clear H0. psimpl.
  unfold retPoss. destruct x1, x0. psimpl.
  f_equal.
  extensionality j. dec_eq_nats i j.
  rewrite eqb_id. easy.
  rewrite eqb_nid. symmetry. apply H12; easy. easy.
  extensionality j. dec_eq_nats i j.
  rewrite eqb_id. easy.
  rewrite eqb_nid. symmetry. apply H13; easy. easy.
}
{
  subst. assert (H' := H).
  apply H0 in H'. clear H0. psimpl.
  assert (x = retPoss i x0).
  destruct x, x0. unfold retPoss. psimpl.
  f_equal.
  extensionality j. dec_eq_nats i j.
  rewrite eqb_id. easy.
  rewrite eqb_nid. apply H5. easy. easy.
  extensionality j. dec_eq_nats i j.
  rewrite eqb_id. easy.
  rewrite eqb_nid. apply H6. easy. easy.
  subst. easy.
}
Qed.

(* Program logic obligations *)

Lemma Rely_refl :
  forall i s ρ, Rely i s ρ s ρ.
unfold Rely. intros. subst.
exists ρ0. split. easy.
left. constructor.
Qed.

Lemma Rely_trans :
  forall i, Rely i ->> Rely i ==> Rely i.
unfold sub, subRelt. intros. pdestruct H.
unfold Rely in H. unfold Rely. intros. subst.
specialize (H ρ0 eq_refl). destruct_all. subst.
specialize (H0 x1 eq_refl). destruct_all. subst.
exists x0. split. easy.
destruct H0, H1.
{
  left. eapply rtcTrans. repeat eexists.
  exact H0. easy.
}
{
  right.
  apply noStateChange in H. destruct_all.
  move H10 at bottom. symmetry in H10.
  specialize (H11 x0 eq_refl). destruct_all. subst.
  symmetry in H12. move H12 at bottom.
  repeat rewrite (countState_eq _ _ H10) in *.
  repeat rewrite (ctrval_eq _ _ H10) in *.
  repeat rewrite (mytkt_eq _ _ _ H10) in *.
  repeat rewrite (newtkt_eq _ _ H10) in *.
  repeat rewrite H12 in *.
  rewrite H9.
  easy.
}
{
  right.
  apply noStateChange in H0. destruct_all.
  specialize (H2 x1 eq_refl). destruct_all. subst.
  symmetry in H1. move H1 at bottom.
  repeat rewrite (countState_eq _ _ H1) in *.
  repeat rewrite (ctrval_eq _ _ H1) in *.
  repeat rewrite (mytkt_eq _ _ _ H1) in *.
  repeat rewrite (newtkt_eq _ _ H1) in *.
  repeat rewrite H12 in *.
  rewrite H0.
  easy.
}
{
  right. destruct_all.
  split. auto.
  split. auto.
  split. auto.
  split. auto.
  split. auto.
  split. auto.
  split. rewrite H6. easy.
  split.
  {
    intros. assert (H19' := H19). apply H7 in H19. psimpl.
    rewrite H19 in H19'. apply H16 in H19'. psimpl.
    rewrite H19, H20. easy.
  }
  split. rewrite H8. easy.
  rewrite H9. easy.
}
Qed.

Lemma Guar_in_Rely :
  forall i j : ThreadName, i <> j -> Guar i ==> Rely j.
unfold Guar, sub, subRelt. intros. destruct_all.
apply H0. easy.
Qed.

Lemma Inv_in_Rely :
  forall i j : ThreadName, i <> j -> InvokeAny ticketLockImpl i ==> Rely j.
unfold InvokeAny, TInvoke, Rely, sub, subRelt, TIdle. intros.
destruct_all. subst. destruct H2. cbn in *.
specialize (H5 ρ0 eq_refl). destruct_all.
assert (exists τ, σ = eq τ).
eapply mapPossInv_pres_single. exact H4.
destruct_all. subst.
exists x1. split. easy.
destruct H4. clear H7.
specialize (H4 ρ0 eq_refl).
unfold mapInvPoss in H4. destruct_all. subst.
symmetry in H13. repeat rewrite H13.
repeat rewrite (mytkt_eq _ _ _ H3).
repeat rewrite (countState_eq _ _ H3).
repeat rewrite (newtkt_eq _ _ H3).
repeat rewrite (ctrval_eq _ _ H3).
rewrite H2. 2: easy.
right. easy.
Qed.

Lemma Ret_in_Rely :
  forall i j : ThreadName, i <> j -> ReturnAny ticketLockImpl i ==> Rely j.
unfold ReturnAny, TReturn, Rely, sub, subRelt, TIdle. intros.
destruct_all. subst. cbn in *.
assert (σ = eq (retPoss i ρ0)).
eapply mapPossRet_pres_single. exact H3.
destruct_all. subst. destruct H3.
exists (retPoss i ρ0). split. easy.
destruct H0.
specialize (H1 ρ0 eq_refl). specialize (H3 (retPoss i ρ0) eq_refl).
psimpl. unfold mapRetPoss in H6. psimpl.
symmetry in H9. repeat rewrite H9.
symmetry in H2.
repeat rewrite (mytkt_eq _ _ _ H2).
repeat rewrite (countState_eq _ _ H2).
repeat rewrite (newtkt_eq _ _ H2).
repeat rewrite (ctrval_eq _ _ H2).
rewrite H4. 2: easy.
right. easy.
Qed.

Lemma init_in_Precs :
  forall i A (m : LockSig A), Precs i m (allIdle, Init VE) (eq initPoss).
unfold Precs, Reled, Acqed, Inv. intros.
exists initPoss. split. easy.
destruct m; simpl.
{
  intros. exists initPoss. split. easy.
  easy.
}
{
  intros. exists initPoss. split. easy.
  easy.
}
Qed.

Ltac decide_prop P :=
  let H := fresh in
  assert (H : P \/ ~P) by apply excluded_middle;
  destruct H.

Lemma Precs_stable :
  forall i A (m : LockSig A), Stable (Rely i) (Precs i m).
unfold Precs, Acqed, Reled. intros. destruct m.
{
  unfold Stable, stablePrec, sub, subPrec. intros. psimpl.
  assert (exists τ, ρ = eq τ).
  eapply Rely_pres_single. exact H0. psimpl.
  exists x0. split. easy. intros.
  assert (owner (PState x1) <> Some i).
  eapply (Rely_pres_not_owned _ _ _ _ _ H0). easy.
  apply H1 in H2. clear H1.
  apply Inv_stable.
  psplit. exact H2. easy.
}
{
  unfold Stable, stablePrec, sub, subPrec. intros. psimpl.
  assert (exists τ, ρ = eq τ).
  eapply Rely_pres_single. exact H0. psimpl.
  exists x0. split. easy. intros.
  assert (owner (PState x1) = Some i).
  eapply (Rely_pres_owned _ _ _ _ _ H0). easy.
  apply H1 in H2. clear H1.
  apply Inv_stable.
  psplit. exact H2. easy.
}
Qed.

Lemma Posts_stable :
  forall i A (m : LockSig A) v, Stable (Rely i) (Posts i m v).
unfold Posts, Acqed, Reled. intros. destruct m.
{
  unfold Stable, stablePost, stableRelt, sub, subRelt.
  split; intros; psimpl.
  {
    assert (exists τ, x0 = eq τ).
    eapply Rely_pres_single. exact H. psimpl.
    specialize (H1 x1 eq_refl). psimpl.
    exists x0. split. easy.
    intros. apply H1.
    eapply Rely_pres_not_owned.
    exact H. easy.
  }
  {
    specialize (H ρ0 eq_refl). psimpl.
    assert (exists τ, σ = eq τ).
    eapply Rely_pres_single. exact H1. psimpl.
    exists x0. split. easy.
    intros. apply H0 in H. clear H0.
    psimpl. split.
    eapply Rely_pres_owned. 
    exact H1. easy.
    apply Inv_stable.
    psplit. exact H0. easy.
  }
}
{
  unfold Stable, stablePost, stableRelt, sub, subRelt.
  split; intros; psimpl.
  {
    assert (exists τ, x0 = eq τ).
    eapply Rely_pres_single. exact H. psimpl.
    specialize (H1 x1 eq_refl). psimpl.
    exists x0. split. easy.
    intros. apply H1. clear H1.
    eapply Rely_pres_owned. exact H.
    easy. 
  }
  {
    specialize (H ρ0 eq_refl). psimpl.
    assert (exists τ, σ = eq τ).
    eapply Rely_pres_single. exact H1. psimpl.
    exists x0. split. easy.
    intros. apply H0 in H. clear H0. psimpl.
    split.
    eapply Rely_pres_not_owned. exact H1. easy.
    apply Inv_stable.
    psplit. exact H0. easy.
  }
}
Qed.

Lemma ticketLockImpl_switch_code :
  forall i A (m1 : LockSig A) B (m2 : LockSig B) v,
  prComp (Precs i m1) (Posts i m1 v) <<- PrecToRelt (Returned i m1) <<-
  TReturn ticketLockImpl i m1 ==>
  Precs i m2.
unfold sub, subPrec, Precs, Posts. intros. destruct m1, m2.
{
  psimpl. specialize (H2 x5 eq_refl). psimpl.
  unfold TReturn, InterOStep in H0. psimpl. destruct x0.
  eapply mapPossRet_pres_single in H4. subst.
  exists (retPoss i x1). split. easy.
  simpl. intros.
  
}
Qed.

Theorem ticketLockCorrect :
  VerifyImpl VE VF Rely Guar Precs ticketLockImpl Posts.
constructor.
apply Rely_refl.
apply Rely_trans.
apply Guar_in_Rely.
apply Inv_in_Rely.
apply Ret_in_Rely.
apply init_in_Precs.
apply Precs_stable.
apply Posts_stable.
apply ticketLockImpl_switch_code.