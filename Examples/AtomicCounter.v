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
  Relations.Relation_Operators.
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

Definition AtomicCounterSteps :
  AtomicCounterState -> Trace (ThreadEvent CounterSig) -> AtomicCounterState -> Prop :=
  Steps AtomicCounterStep.

Definition invariant : Prec :=
  fun s ρ =>
    exists s',
      countState s = CounterDSt s' /\
      (~(exists i, lockState s = LockOwned i) ->
        ρ.(PState) = s').

Definition rely : ThreadName -> Relt :=
  fun i s ρ t σ =>
    (exists j,
      i <> j /\
      InvokeAny atomicCounterImpl j s ρ t σ) \/
    (exists j,
      i <> j /\
      ReturnAny atomicCounterImpl j s ρ t σ) \/
    (lockState s = LockOwned i ->
      countState s = countState t /\
      ρ.(PState) = σ.(PState)).

Definition guar : ThreadName -> Relt :=
  fun i s ρ t σ =>
    lockState s <> LockOwned i ->
      countState s = countState t /\
      ρ.(PState) = σ.(PState).

Definition precs : ThreadName -> forall Ret, CounterSig Ret -> Prec :=
  fun i Ret m s ρ =>
    TIdle i s ρ /\
    invariant s ρ /\
    lockState s <> LockOwned i.

Definition posts : ThreadName -> forall Ret, CounterSig Ret -> Post Ret :=
  fun i Ret m v _ _ t σ =>
    invariant t σ /\
    lockState t <> LockOwned i.

Ltac rw_all :=
repeat lazymatch goal with
| [ H : ?x = ?y |- ?G ] => try (rewrite H in *; clear H)
end.

Lemma eqbNeq : forall i j, i <> j -> i =? j = false.
fix rec 1.
intros.
destruct i, j.
all: congruence || (try easy).
simpl.
apply rec.
congruence.
Qed.

Lemma precsStable i A m : Stable (rely i) (precs i A m).
unfold Stable, stablePrec, sub, subPrec, rely.
intros.
psimpl.
destruct H0;
unfold InvokeAny, ReturnAny, TInvoke, TReturn in *;
psimpl; steps.
unfold precs.
split.
{
  split.
  unfold updThs.
  simpl.
  rewrite eqbNeq.
  do 2 destruct H.
  all: easy.
}
split.
{
  unfold precs, invariant, countState, lockState in *.
  psimpl.
  exists x.
  split.
  easy.
  intros.
  apply H8 in H9.
  congruence.
}
unfold lockState.
simpl.
destruct H.
easy.
destruct H0.
psimpl.
{
  unfold precs, invariant, TIdle in *.
  psimpl.
  steps.
  split.
  split.
  unfold updThs.
  simpl in *.
  rewrite eqbNeq.
  easy.
  easy.
  easy.
  split.
  exists x5.
  split.
  easy.
  intros.
  all: unfold lockState in *.
  all: simpl in *.
  apply H6 in H7.
  easy.
  easy.
}
unfold precs, invariant, TIdle in *.
psimpl.
split.
split.
Admitted.

Lemma postsStable i A m : Stable (rely i) (posts i A m).
Admitted.

Theorem atomicCounterCorrect :
  VerifyImpl VE VF rely guar precs atomicCounterImpl posts.
unfold VerifyImpl.
split.
{
  admit.
}
split.
{
  intros.
  unfold precs, invariant, TIdle.
  split.
  repeat split.
  exists (CounterIdle 0).
  easy.
  easy.
  split.
  easy.
  split.
  eapply precsStable.
  apply postsStable.
}
split.
admit.
intros.
destruct m.
simpl.
unfold inc.
eapply SafeBind with
  (QI:= fun s ρ t σ =>
    True)
  (QR:=fun _ s (ρ : Poss VF) t (σ : Poss VF) =>
    lockState t = LockOwned i /\
    σ.(PCalls) i = Some (existT _ _ Inc) /\
    σ.(PRets) i = None /\
    countState t = countState s /\
    σ = ρ /\
    exists k,
      countState s = CounterDSt (CounterIdle k) /\
      ρ.(PState) = CounterIdle k).
admit.
admit.
admit.
split.
admit.
eapply SafeBind with
  (QI:=fun s ρ t (σ : Poss VF) =>
    lockState t = LockOwned i /\
    σ.(PCalls) i = Some (existT _ _ Inc) /\
    σ.(PRets) i = None /\
    countState t = countState s /\
    σ = ρ /\
    exists k,
      countState s = CounterDSt (CounterIdle k) /\
      ρ.(PState) = CounterIdle k)
  (QR:=fun _ s (ρ : Poss VF) t (σ : Poss VF) =>
    lockState t = LockOwned i /\
    σ.(PCalls) i = None /\
    σ.(PRets) i = None /\
    exists k,
      ρ.(PState) = CounterIdle k /\
      countState s = CounterDSt (CounterIdle k) /\
      σ.(PState) = CounterIdle (S k) /\
      countState s = CounterDSt (CounterIdle (S k))).
admit.
admit.
admit.
split.
{
  unfold Commit, id.
  intros.
  psimpl.
  steps.
  dependent destruction H9.
}
eapply SafeBind with
  (QI:=fun s ρ t σ =>
    True)
  (QR:=fun _ s (ρ : Poss VF) t (σ : Poss VF) =>
    lockState t <> LockOwned i /\
    σ.(PCalls) i = None /\
    σ.(PRets) i = None /\
    σ = ρ /\
    countState t = countState s).
admit.
admit.
admit.
split.
admit.
eapply SafeReturn.
{
  unfold sub, subRelt.
  intros.
  psimpl.
}