From LHL.Core Require Import
  Program
  Specs
  Logic
  LogicFacts
  Tensor
  Traces
  Linearizability.

From LHL.Util Require Import
  TransUtil.

From LHL.Examples Require Import
  RacyCounter
  CounterSpecs
  Lock.

From Coq Require Import
  Arith.PeanoNat
  Program.Equality
  Lists.List
  Relations.Relation_Operators
  Logic.FunctionalExtensionality.
Import ListNotations.
Open Scope list_scope.

From Hammer Require Import Hammer.

Definition atomicCounterSpec : Spec CounterSig := {|
  State := AtomicCounterState;
  Step := AtomicCounterStep;
  Init := CounterIdle 0
|}.

Definition Underlay := LockSig |+| CounterSig.

Definition inc : Prog Underlay unit :=
  _ <- inl Acq;
  _ <- inr Inc;
  _ <- inl Rel;
  Return tt.

Definition get : Prog Underlay nat :=
  _ <- inl Acq;
  n <- inr Get;
  _ <- inl Rel;
  Return n.

Definition atomicCounterImpl : Impl (LockSig |+| CounterSig) CounterSig :=
  fun _ m => match m with
  | Inc => inc
  | Get => get
  end.

Definition E := Underlay.
Definition F := CounterSig.
Definition VE := tensorSpec lockSpec racyCounterSpec.
Definition VF := atomicCounterSpec.

Definition Relt := Relt VE VF.
Definition Prec := Prec VE VF.
Definition Post := Post VE VF.

Definition countState (s : @InterState E F VE) : RacyCounterState :=
  snd (snd s).

Definition lockState (s : @InterState E F VE) : LockState :=
  fst (snd s).

(*
We start with the lock being unowned and the underlay counter equaling the overlay counter, and after R this should should still be true. We then proceed to acquiring the lock, and after R should now do nothing.
*)

Definition defined s (ρ : Poss VF) :=
  exists k,
    countState s = CounterDSt (CounterIdle k) /\
    PState ρ = CounterIdle k.

Definition invariant : Prec :=
  fun s ρ =>
    lockState s = LockIdle ->
      defined s ρ.

Definition rely (i : ThreadName) : Relt :=
  fun s ρ t σ =>
    invariant t σ /\
    PCalls ρ i = PCalls σ i /\
    PRets ρ i = PRets σ i /\
    fst s i = fst t i /\
    (OwnsLock i (lockState s) ->
      countState s = countState t /\
      PState ρ = PState σ /\
      OwnsLock i (lockState t)).

Definition guar (i : ThreadName) : Relt :=
  fun s ρ t σ =>
    invariant t σ /\
    (forall j,
      i <> j ->
      PCalls ρ j = PCalls σ j) /\
    (forall j,
      i <> j ->
      PRets ρ j = PRets σ j) /\
    (forall j,
      i <> j ->
      fst s j = fst t j) /\
    (forall j,
      i <> j ->
      OwnsLock j (lockState s) ->
      countState s = countState t /\
      PState ρ = PState σ /\
      OwnsLock j (lockState t)).

Definition precs : ThreadName -> forall Ret, CounterSig Ret -> Prec :=
  fun i Ret m s ρ =>
    invariant s ρ.

Definition posts : ThreadName -> forall Ret, CounterSig Ret -> Post Ret :=
  fun i Ret m v s ρ t σ =>
    invariant t σ.

Definition runIncPoss i n (ρ : Poss VF) : Poss VF := MkPoss F VF
  (CounterIncRunning i n)
  (fun j => if i =? j then None else ρ.(PCalls) j)
  ρ.(PRets).

Definition retIncPoss i n (ρ : Poss VF) : Poss VF := MkPoss F VF
  (CounterIdle (S n))
  ρ.(PCalls)
  (fun j => if i =? j then Some (existT _ _ tt) else ρ.(PRets) j).

Definition runGetPoss i n (ρ : Poss VF) : Poss VF := MkPoss F VF
  (CounterGetRunning i n)
  (fun j => if i =? j then None else ρ.(PCalls) j)
  ρ.(PRets).

Definition retGetPoss i n (ρ : Poss VF) : Poss VF := MkPoss F VF
  (CounterIdle n)
  ρ.(PCalls)
  (fun j => if i =? j then Some (existT _ _ n) else ρ.(PRets) j).


Definition acqPost i : Relt :=
  fun s ρ t σ =>
    defined t σ /\
    PCalls ρ i = PCalls σ i /\
    PRets ρ i = PRets σ i /\
    OwnsLock i (lockState t).

Ltac commit := unfold Commit, precs, guar, acqPost, invariant, defined, countState, lockState, id; intros; psimpl.
Ltac stable := unfold Stable, stablePrec, stablePost, stableRelt, sub, subRelt, subPrec, invariant, precs, posts, rely, acqPost; intros; psimpl.

Lemma acqPostStable i :
  Stable (rely i) (acqPost i).
stable.
split; intros; psimpl.
repeat split.
easy.
congruence.
congruence.
easy.
assert (H7' := H7).
apply H4 in H7'.
unfold defined in *.
psimpl.
split.
exists x1.
split.
congruence.
congruence.
split.
congruence.
split.
congruence.
easy.
Qed.

Lemma eqbNeq :
  forall i j, i <> j -> i =? j = false.
fix rec 1.
intros.
destruct i, j.
easy.
easy.
easy.
simpl.
apply rec.
congruence.
Qed.

Theorem atomicCounterCorrect :
  VerifyImpl VE VF rely guar precs atomicCounterImpl posts.
unfold VerifyImpl.
split.
{
  unfold sub, subRelt, guar, rely.
  intros.
  psimpl.
  split.
  easy.
  split.
  apply H1.
  easy.
  split.
  apply H2.
  easy.
  split.
  apply H3.
  easy.
  intros.
  apply H4 with (j:=j).
  easy.
  unfold OwnsLock, not in *.
  intros.
  firstorder; congruence.
}
split.
split.
{
  exists 0.
  easy.
}
split.
{
  stable.
  easy.
}
{
  stable.
  split; intros; psimpl; easy.
}
split.
{
  unfold precs, posts, PrecToRelt, TReturn, sub, subPrec.
  intros.
  psimpl.
  steps.
  unfold invariant, defined, lockState, countState in *.
  simpl in *.
  intros.
  apply H8 in H7.
  psimpl.
  exists x.
  split.
  congruence.
  congruence.
}
intros.
destruct m.
simpl.
unfold inc.
eapply SafeBind with
  (QI:= acqPost i)
  (QR:=fun _ => acqPost i).
apply acqPostStable.
unfold Stable, stablePost.
intros.
apply acqPostStable.
{
  commit.
  steps.
  exists ρ.
  split.
  apply rt_refl.
  steps.
  symmetry in x0.
  assert (x0' := x0).
  apply H in x0. clear H.
  psimpl.
  split.
  split.
  exists x0.
  split.
  congruence.
  congruence.
  split.
  easy.
  split.
  easy.
  unfold OwnsLock.
  left.
  easy.
  split.
  intros.
  exists x0.
  split; congruence.
  split.
  easy.
  split.
  easy.
  split.
  intros.
  unfold updThs.
  rewrite eqbNeq.
  easy.
  easy.
  intros.
  split.
  easy.
  split.
  easy.
  unfold OwnsLock in *.
  firstorder; congruence.
}
split.
{
  commit.
  exists ρ.
  split.
  apply rt_refl.
  steps.
  split.
  split.
  exists x4.
  split.
  congruence.
  congruence.
  unfold OwnsLock.
  firstorder.
  split.
  intros.
  congruence.
  split.
  easy.
  split.
  easy.
  split.
  intros.
  unfold updThs.
  rewrite eqbNeq.
  easy.
  easy.
  intros.
  unfold OwnsLock in *.
  firstorder; congruence.
}
eapply SafeBind with
  (QI:=fun s ρ t (σ : Poss VF) =>
    OwnsLock i (lockState t) /\
    PRets ρ i = PRets σ i /\
    exists k,
      countState t = CounterDSt (CounterIncRunning i k) /\
      PState σ = CounterIncRunning i k)
  (QR:=fun _ s ρ t (σ : Poss VF) =>
    OwnsLock i (lockState t) /\
    PRets σ i = Some (existT _ _ tt) /\
    exists k,
      countState t = CounterDSt (CounterIdle k) /\
      PState σ = CounterIdle k).
{
  stable.
  split; intros; psimpl.
  split.
  easy.
  split.
  rewrite <- H1 in *.
  easy.
  exists x1.
  easy.
  assert (H' := H).
  apply H4 in H'. clear H4.
  psimpl.
  split.
  easy.
  split.
  congruence.
  exists x1.
  split.
  congruence.
  congruence.
}
{
  stable.
  split; intros; psimpl.
  split.
  easy.
  split.
  easy.
  exists x1.
  easy.
  apply H4 in H. clear H3.
  psimpl.
  split.
  easy.
  split.
  congruence.
  exists x1.
  split.
  congruence.
  congruence.
}
{
  commit.
  exists (runIncPoss i x6 ρ).
  steps.
  congruence.
  congruence.
  dependent destruction H3.
  split.
  apply rt_step.
  eapply PCommitCall.
  simpl.
  rewrite H11.
  constructor.
  simpl.
  split.
  congruence.
  rewrite eqbEql.
  easy.
  easy.
  split.
  split.
  unfold OwnsLock in *.
  destruct H7.
  left.
  congruence.
  destruct H3.
  right.
  left.
  congruence.
  right.
  right.
  congruence.
  split.
  easy.
  exists n.
  split.
  easy.
  assert (x6 = n).
  congruence.
  subst.
  easy.
  split.
  intros.
  rewrite H14 in *.
  unfold OwnsLock.
  firstorder; congruence.
  split.
  intros.
  rewrite eqbNeq.
  easy.
  easy.
  split.
  easy.
  split.
  intros.
  unfold updThs.
  rewrite eqbNeq.
  easy.
  easy.
  intros.
  unfold OwnsLock in *.
  firstorder; congruence.
}
split.
{
  commit.
  steps.
  congruence.
  dependent destruction H7.
  exists (retIncPoss i n ρ).
  assert (x4 = n).
  congruence.
  subst.
  split.
  apply rt_step.
  eapply PCommitRet.
  rewrite H4.
  simpl.
  constructor.
  easy.
  simpl.
  unfold TIdle in *.
  psimpl.
  etransitivity.
  symmetry.
  exact H2.
  etransitivity.
  symmetry.
  exact H10.
  etransitivity.
  symmetry.
  exact H13.
  rewrite H22.
  easy.
  simpl.
  rewrite eqbEql.
  easy.
  split.
  unfold OwnsLock in *.
  rewrite H18 in *.
  split.
  firstorder; congruence.
  split.
  simpl.
  rewrite eqbEql.
  easy.
  exists (S n).
  easy.
  split.
  intros.
  rewrite H18 in *.
  unfold OwnsLock in *.
  firstorder; congruence.
  split.
  intros.
  easy.
  split.
  intros.
  simpl.
  rewrite eqbNeq.
  easy.
  easy.
  split.
  intros.
  unfold updThs.
  rewrite eqbNeq.
  easy.
  easy.
  intros.
  intros.
  unfold OwnsLock in *.
  rewrite H18 in *.
  firstorder; congruence.
}
eapply SafeBind with
  (QI:= acqPost i)
  (QR:=fun _ s ρ t σ =>
    invariant t σ /\
    PRets ρ i = PRets σ i).
apply acqPostStable.
{
  stable.
  split; intros; psimpl.
  split.
  firstorder.
  congruence.
  split.
  firstorder.
  congruence.
}
{
  commit.
  steps.
  exists ρ.
  split.
  apply rt_refl.
  split.
  split.
  exists x6.
  split.
  congruence.
  congruence.
  split.
  easy.
  split.
  easy.
  right.
  right.
  easy.
  split.
  intros.
  congruence.
  split.
  easy.
  split.
  easy.
  split.
  intros.
  unfold updThs.
  rewrite eqbNeq.
  easy.
  easy.
  intros.
  unfold OwnsLock in *.
  firstorder; congruence.
}
split.
{
  commit.
  steps.
  exists ρ.
  split.
  apply rt_refl.
  split.
  split.
  intros.
  exists x4.
  split.
  congruence.
  congruence.
  easy.
  split.
  intros.
  exists x4.
  split.
  congruence.
  congruence.
  split.
  easy.
  split.
  easy.
  intros.
  split.
  intros.
  unfold updThs.
  rewrite eqbNeq.
  easy.
  easy.
  intros.
  unfold OwnsLock in *.
  firstorder; congruence.
}
eapply SafeReturn.
{
  unfold sub, subRelt.
  intros.
  psimpl.
  steps.
  psplit.
  unfold posts.
  exact H2.
  unfold PrecToRelt, Returned.
  split.
  exists tt.
  unfold acqPost in *.
  psimpl.
  congruence.
  easy.
}
unfold get.
eapply SafeBind with
  (QI:= acqPost i)
  (QR:=fun _ => acqPost i).
apply acqPostStable.
unfold Stable, stablePost.
intros.
apply acqPostStable.
{
  commit.
  exists ρ.
  split.
  apply rt_refl.
  steps.
  symmetry in x0.
  assert (x0' := x0).
  apply H in x0. clear H.
  psimpl.
  split.
  split.
  exists x0.
  split.
  congruence.
  congruence.
  split.
  easy.
  split.
  easy.
  unfold OwnsLock.
  left.
  easy.
  split.
  intros.
  exists x0.
  split; congruence.
  split.
  easy.
  split.
  easy.
  split.
  intros.
  unfold updThs.
  rewrite eqbNeq.
  easy.
  easy.
  intros.
  split.
  easy.
  split.
  easy.
  unfold OwnsLock in *.
  firstorder; congruence.
}
split.
{
  commit.
  exists ρ.
  split.
  apply rt_refl.
  steps.
  split.
  split.
  exists x4.
  split.
  congruence.
  congruence.
  unfold OwnsLock.
  firstorder.
  split.
  intros.
  congruence.
  split.
  easy.
  split.
  easy.
  split.
  intros.
  unfold updThs.
  rewrite eqbNeq.
  easy.
  easy.
  intros.
  unfold OwnsLock in *.
  firstorder; congruence.
}
eapply SafeBind with
  (QI:=fun s ρ t (σ : Poss VF) =>
    OwnsLock i (lockState t) /\
    PRets ρ i = PRets σ i /\
    exists k,
      countState t = CounterDSt (CounterGetRunning i k) /\
      PState σ = CounterGetRunning i k)
  (QR:=fun _ s ρ t (σ : Poss VF) =>
    OwnsLock i (lockState t) /\
    exists k,
    PRets σ i = Some (existT _ _ k) /\
      countState t = CounterDSt (CounterIdle k) /\
      PState σ = CounterIdle k).
{
  stable.
  split; intros; psimpl.
  split.
  easy.
  split.
  rewrite <- H1 in *.
  easy.
  exists x1.
  easy.
  assert (H' := H).
  apply H4 in H'. clear H4.
  psimpl.
  split.
  easy.
  split.
  congruence.
  exists x1.
  split.
  congruence.
  congruence.
}
{
  stable.
  split; intros; psimpl.
  split.
  easy.
  exists x1.
  easy.
  apply H4 in H. clear H3.
  psimpl.
  split.
  easy.
  exists x1.
  split.
  congruence.
  split.
  congruence.
  congruence.
}
{
  commit.
  exists (runGetPoss i x6 ρ).
  steps.
  congruence.
  dependent destruction H3.
  split.
  apply rt_step.
  eapply PCommitCall.
  simpl.
  rewrite H11.
  constructor.
  simpl.
  split.
  congruence.
  rewrite eqbEql.
  easy.
  easy.
  split.
  split.
  unfold OwnsLock in *.
  destruct H7.
  left.
  congruence.
  destruct H3.
  right.
  left.
  congruence.
  right.
  right.
  congruence.
  split.
  easy.
  exists n.
  split.
  easy.
  assert (x6 = n).
  congruence.
  subst.
  easy.
  split.
  intros.
  rewrite H14 in *.
  unfold OwnsLock.
  firstorder; congruence.
  split.
  intros.
  rewrite eqbNeq.
  easy.
  easy.
  split.
  easy.
  split.
  intros.
  unfold updThs.
  rewrite eqbNeq.
  easy.
  easy.
  intros.
  unfold OwnsLock in *.
  firstorder; congruence.
}
split.
{
  commit.
  steps.
  congruence.
  dependent destruction H7.
  exists (retGetPoss i v0 ρ).
  assert (x4 = v0).
  congruence.
  subst.
  split.
  apply rt_step.
  eapply PCommitRet.
  rewrite H4.
  simpl.
  constructor.
  easy.
  simpl.
  unfold TIdle in *.
  psimpl.
  etransitivity.
  symmetry.
  exact H2.
  etransitivity.
  symmetry.
  exact H10.
  etransitivity.
  symmetry.
  exact H13.
  rewrite H22.
  easy.
  simpl.
  rewrite eqbEql.
  easy.
  split.
  unfold OwnsLock in *.
  rewrite H18 in *.
  split.
  firstorder; congruence.
  exists v0.
  split.
  simpl.
  rewrite eqbEql.
  easy.
  split.
  congruence.
  easy.
  split.
  intros.
  unfold OwnsLock in *.
  rewrite H18 in *.
  firstorder; congruence.
  split.
  easy.
  split.
  simpl.
  intros.
  rewrite eqbNeq.
  easy.
  easy.
  split.
  intros.
  unfold updThs.
  rewrite eqbNeq.
  easy.
  easy.
  intros.
  unfold OwnsLock in *.
  firstorder; congruence.
}
eapply SafeBind with
  (QI:= acqPost i)
  (QR:=fun _ s ρ t σ =>
    invariant t σ /\
    PRets ρ i = PRets σ i).
apply acqPostStable.
{
  stable.
  split; intros; psimpl.
  split.
  firstorder.
  congruence.
  split.
  firstorder.
  congruence.
}
{
  commit.
  steps.
  exists ρ.
  split.
  apply rt_refl.
  split.
  split.
  exists x6.
  split.
  congruence.
  congruence.
  split.
  easy.
  split.
  easy.
  right.
  right.
  easy.
  split.
  intros.
  congruence.
  split.
  easy.
  split.
  easy.
  split.
  intros.
  unfold updThs.
  rewrite eqbNeq.
  easy.
  easy.
  intros.
  unfold OwnsLock in *.
  firstorder; congruence.
}
split.
{
  commit.
  steps.
  exists ρ.
  split.
  apply rt_refl.
  split.
  split.
  intros.
  exists x4.
  split.
  congruence.
  congruence.
  easy.
  split.
  intros.
  exists x4.
  split.
  congruence.
  congruence.
  split.
  easy.
  split.
  easy.
  intros.
  split.
  intros.
  unfold updThs.
  rewrite eqbNeq.
  easy.
  easy.
  intros.
  unfold OwnsLock in *.
  firstorder; congruence.
}
eapply SafeReturn.
{
  unfold sub, subRelt.
  intros.
  psimpl.
  steps.
  psplit.
  unfold posts.
  exact H2.
  unfold PrecToRelt, Returned.
  split.
  exists x8.
  unfold acqPost in *.
  psimpl.
  congruence.
  easy.
}
Qed.