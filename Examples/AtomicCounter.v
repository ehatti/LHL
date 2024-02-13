From LHL.Core Require Import
  Program
  Specs
  Logic
  LogicFacts
  Tensor
  Traces
  Linearizability.

From LHL.Examples Require Import
  RacyCounter
  CounterSpecs
  Lock.

From Coq Require Import
  Program.Equality
  Lists.List
  Relations.Relation_Operators.

Import ListNotations.
Open Scope list_scope.

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

Definition Relt := Relt E VE F.
Definition Prec := Prec E VE F.

Definition countState (s : @InterState E F VE) : RacyCounterState :=
  snd (snd s).

Definition lockState (s : @InterState E F VE) : LockState :=
  fst (snd s).

Definition int i : Relt :=
  fun s ρ t σ =>
    InvokeAny atomicCounterImpl i s ρ t σ \/
    ReturnAny atomicCounterImpl i s ρ t σ.

Definition rely : ThreadName -> Relt :=
  fun i s ρ t σ =>
      RTC
        (fun s ρ t σ => exists j, i <> j /\ int j s ρ t σ)
        s ρ t σ \/
      (lockState s = LockOwned i ->
        countState s = countState t /\
        lin VF ρ = lin VF σ /\
        lockState t = LockOwned i).

Definition guar : ThreadName -> Relt :=
  fun i s ρ t σ =>
      RTC (int i) s ρ t σ \/
      (lockState s <> LockOwned i ->
        countState s = countState t /\
        lin VF ρ = lin VF σ).

Definition precs : ThreadName -> forall Ret, CounterSig Ret -> Prec :=
  fun i Ret m s ρ =>
    TIdle i s ρ /\
    countState s <> CounterUB /\
    lockState s <> LockOwned i.

Definition posts : ThreadName -> forall Ret, CounterSig Ret -> Relt :=
  fun i Ret m s ρ t σ =>
    lockState s <> LockOwned i /\
    exists n,
    countState s = CounterDSt (CounterIdle n) /\
    match m with
    | Get => True
    | Inc => countState t = CounterDSt (CounterIdle (S n))
    end.

Theorem atomicCounterCorrect :
  VerifyImpl VE VF rely guar precs atomicCounterImpl posts.
unfold VerifyImpl.
split.
intros.
{
  unfold sub, subRelt.
  intros.
  pdestruct H.
  destruct H, H0.
  left.
  apply rtcTrans.
  psplit.
  exact H.
  easy.
  left.
  admit.
  right.
  intros.
  apply H in H1.
  clear H.
  do 2 destruct H1.
  apply H0 in H2.
  clear H0.
  do 2 destruct H2.
  split.
  etransitivity.
  exact H.
  easy.
  split.
  etransitivity.
  exact H1.
  easy.
  easy.
}
split.
admit.
split.
admit.
split.
admit.
split.
admit.
split.
admit.
intros.
destruct m.
{
  simpl.
  unfold inc.
  eapply weakenPost.
  eapply safeBindUnit with
    (QI:= fun s ρ t σ =>
      countState t <> CounterUB /\
      lockState t <> LockOwned i)
    (QR:= fun s ρ t σ =>
      countState t <> CounterUB /\
      lockState t = LockOwned i).
  {
    stable.
    unfold Stable, stablePrec, sub, subPrec, precs, rely.
    intros.
    pdestruct H.
  }
  {
    unfold Stable
  }
}