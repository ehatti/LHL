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
  Tactics.

From Coq Require Import
  Arith.PeanoNat
  Program.Equality
  Logic.FunctionalExtensionality
  Logic.PropExtensionality.

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
  (owner (PState ρ) = Some i ->
    Inv i s ρs).

Definition Reled (i : ThreadName) : Prec := fun s ρs =>
  exists ρ, ρs = eq ρ /\
  (owner (PState ρ) <> Some i ->
    Inv i s ρs).

Definition Precs (i : ThreadName) {A} (m : LockSig A) : Prec :=
  fun s ρs =>
    match m with
    | Acq => Reled i s ρs
    | Rel => Acqed i s ρs
    end.

Definition Posts (i : ThreadName) {A} (m : LockSig A) : Post A :=
  fun _ _ _ t σ =>
    match m with
    | Acq => Acqed i t σ
    | Rel => Reled i t σ
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
    (owner (PState ρ) = Some i ->
      PState ρ = PState σ /\
      ctrval s = ctrval t) /\
    (owner (PState ρ) <> Some i ->
      owner (PState σ) <> Some i)
  ).

Definition Guar (i : ThreadName) : Relt :=
  fun s ρs t σs =>
    forall j, i <> j -> Rely j s ρs t σs.

(* Extra lemmas *)

Lemma noStateChange :
  forall i s ρs t σs,
  ManyInvokeReturn i s ρs t σs ->
  snd s = snd t /\
  forall σ, σs σ ->
    exists ρ, ρs ρ /\
      PState ρ = PState σ.
intros.
induction H.
{
  split. easy.
  intros. exists σ. easy.
}
{
  clear H0.
  destruct_all.
  destruct H2.
  {
    unfold InvokeAny, TInvoke in H2. destruct_all.
    destruct H3. simpl in *.
    split. transitivity (snd t); easy.
    intros.
    apply H1 in H7. destruct_all.
    apply H5 in H7. destruct_all.
    exists x3. split. easy.
    congruence.
  }
  {
    unfold ReturnAny, TReturn in H2. destruct_all.
    destruct H2. simpl in *.
    split. transitivity (snd t); easy.
    intros.
    apply H1 in H6. destruct_all.
    apply H4 in H6. destruct_all.
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
  specialize (H0 x0 eq_refl). destruct_all. subst.
  rewrite <- H7. symmetry in H.
  repeat rewrite (countState_eq _ _ H).
  repeat rewrite (newtkt_eq _ _ H).
  repeat rewrite (mytkt_eq _ _ _ H).
  repeat rewrite (ctrval_eq _ _ H).
  easy.
}
{
  destruct_all.
  repeat split; auto.
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
  move H at bottom. symmetry in H.
  specialize (H8 x0 eq_refl). destruct_all. subst.
  symmetry in H9. move H9 at bottom.
  repeat rewrite (countState_eq _ _ H).
  repeat rewrite (ctrval_eq _ _ H).
  repeat rewrite (mytkt_eq _ _ _ H).
  repeat rewrite (newtkt_eq _ _ H).
  repeat rewrite H9.
  easy.
}
{
  right.
  apply noStateChange in H0. destruct_all.
  specialize (H1 x1 eq_refl). destruct_all. subst.
  symmetry in H9. move H9 at bottom.
  repeat rewrite (countState_eq _ _ H0) in *.
  repeat rewrite (ctrval_eq _ _ H0) in *.
  repeat rewrite (mytkt_eq _ _ _ H0) in *.
  repeat rewrite (newtkt_eq _ _ H0) in *.
  repeat rewrite H9 in *.
  easy.
}
{
  right. destruct_all.
  repeat split; intros; try auto.
  assert (H15' := H15).
  apply H6 in H15. destruct_all. rewrite H15 in H15'.
  apply H13 in H15'. destruct_all.
  rewrite H15. easy.
  assert (H15' := H15).
  apply H6 in H15. destruct_all. rewrite H15 in H15'.
  apply H13 in H15'. destruct_all.
  rewrite H16. easy.
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
{
  destruct H4. specialize (H4 ρ0 eq_refl). destruct_all.
  exists x1.
  extensionality x2. apply propositional_extensionality.
  split; intros.
  {
    apply H7 in H15. clear H7. destruct_all. subst.
    destruct x1, x2, x3. cbn in *.
    f_equal.
    { congruence. }
    {
      extensionality k.
      dec_eq_nats i k.
      congruence.
      etransitivity.
      apply H12. easy.
      symmetry. apply H19. easy.
    }
    {
      extensionality k.
      dec_eq_nats i k.
      congruence.
      etransitivity.
      apply H13. easy.
      symmetry. apply H20. easy.
    }
  }
  {
    subst. easy.
  }
}
destruct_all. subst.
exists x1. split. easy.
destruct H4. clear H7.
specialize (H4 ρ0 eq_refl). destruct_all. subst.
symmetry in H13. repeat rewrite H13.
repeat rewrite (mytkt_eq _ _ _ H3).
repeat rewrite (countState_eq _ _ H3).
repeat rewrite (newtkt_eq _ _ H3).
repeat rewrite (ctrval_eq _ _ H3).
right. easy.
Qed.

Lemma Ret_in_Rely :
  forall i j : ThreadName, i <> j -> ReturnAny ticketLockImpl i ==> Rely j.
unfold ReturnAny, TReturn, Rely, sub, subRelt, TIdle. intros.
destruct_all. subst. destruct H3. cbn in *.
Admitted.

Theorem ticketLockCorrect :
  VerifyImpl VE VF Rely Guar Precs ticketLockImpl Posts.
constructor.
apply Rely_refl.
apply Rely_trans.
apply Guar_in_Rely.
apply Inv_in_Rely.
apply Ret_in_Rely.
