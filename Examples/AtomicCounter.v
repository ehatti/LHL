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
Definition Post := Post E VE F.

Inductive Atomic : Trace (ThreadEvent F) -> Prop :=
| NilAtomic : Atomic []
| ConsAtomic {i ρ A} {m : F A} {v : A} :
  Atomic ρ ->
  Atomic ((i, CallEv m) :: (i, RetEv m v) :: ρ).

Lemma decideEqNat : forall (n m : nat), {n = m} + {n <> m}.
fix rec 2.
intros.
destruct n, m.
left.
congruence.
right.
congruence.
right.
congruence.
assert ({n = m} + {n <> m}) by apply rec.
destruct H.
left.
congruence.
right.
congruence.
Qed.

Lemma decideAtomic : forall ρ, {Atomic ρ} + {~(Atomic ρ)}.
fix rec 1.
intros.
destruct ρ.
left.
constructor.
destruct ρ.
right.
unfold not.
intros.
inversion H.
destruct t, t0.
assert ({t = t0} + {t <> t0}) by apply decideEqNat.
destruct H.
subst.
{
  destruct e, e0.
  right.
  unfold not.
  intros.
  inversion H.
  {
    destruct m, m0.
    assert ({Atomic ρ} + {~Atomic ρ}) by apply rec.
    destruct H.
    left.
    constructor.
    easy.
    right.
    unfold not.
    intros.
    apply n0.
    inversion H.
    easy.
    right.
    unfold not.
    intros.
    dependent destruction H.
    right.
    unfold not.
    intros.
    dependent destruction H.
    assert ({Atomic ρ} + {~Atomic ρ}) by apply rec.
    destruct H.
    left.
    constructor.
    easy.
    right.
    unfold not.
    intros.
    dependent destruction H.
    apply n0.
    easy.
  }
  right.
  unfold not.
  intros.
  inversion H.
  right.
  unfold not.
  intros.
  inversion H.
}
right.
unfold not.
intros.
inversion H.
congruence.
Qed.

Definition AtomicPrefix (ρ σ : Trace (ThreadEvent F)) : Prop :=
  exists τ,
    σ = ρ ++ τ /\
    Atomic ρ /\
    ~(Atomic τ).

(*
left = atomic   right = nonatomic
acc should always be atomic
*)
Fixpoint linAux (acc ρ : Trace (ThreadEvent F)) : Trace (ThreadEvent F) :=
  match ρ with
  | [] | [_] => acc
  | e1 :: e2 :: σ =>
    match decideAtomic (acc ++ [e1; e2]) with
    | left _ => linAux (acc ++ [e1; e2]) σ
    | right _ => acc
    end
  end.

Definition lin ρ := linAux [] ρ.

Lemma linSplit ρ σ :
  ~Atomic σ ->
  lin (ρ ++ σ) = lin ρ.
Admitted.

Lemma linSat ρ :
  lin (lin ρ) = lin ρ.
Admitted.

Lemma linAtomic ρ :
  Atomic ρ ->
  lin ρ = ρ.
Admitted.

Definition countState (s : @InterState E F VE) : RacyCounterState :=
  snd (snd s).

Definition lockState (s : @InterState E F VE) : LockState :=
  fst (snd s).

Definition AtomicCounterSteps :
  AtomicCounterState -> Trace (ThreadEvent CounterSig) -> AtomicCounterState -> Prop :=
  Steps AtomicCounterStep.

Lemma atomicTrans m :
  forall ρ n,
  AtomicCounterSteps (CounterIdle n) ρ (CounterIdle m) ->
  Atomic ρ.
fix rec 1.
intros.
destruct ρ.
constructor.
destruct ρ.
dependent destruction H.
dependent destruction H.
dependent destruction H0.
dependent destruction H0.
do 2 dependent destruction H.
dependent destruction H0.
dependent destruction H.
constructor.
eapply rec.
exact H0.
dependent destruction H0.
dependent destruction H.
constructor.
eapply rec.
exact H0.
Qed.

Definition inter i : Relt :=
  fun s ρ t σ =>
    exists j,
      j <> i /\
      ((InvokeAny atomicCounterImpl j s ρ t σ) \/
        ReturnAny atomicCounterImpl j s ρ t σ).


Definition rely : ThreadName -> Relt :=
  fun i s ρ t σ =>
      inter i s ρ t σ \/
      (lockState s = LockOwned i ->
        countState s = countState t /\
        lin ρ = lin σ).

Lemma relyTrans i :
  rely i >> rely i ==> rely i.
unfold rely, inter, sub, subRelt, InvokeAny, TInvoke, ReturnAny, TReturn.
intros.
psimpl.
destruct H, H0.
psimpl.
destruct H2, H1.
{
  psimpl.
}
Admitted.

Definition guar : ThreadName -> Relt :=
  fun i s ρ t σ =>
      lockState s <> LockOwned i ->
        countState s = countState t /\
        lin ρ = lin σ.

Definition invariant i (f : nat -> AtomicCounterState) : Prec :=
  fun s ρ =>
    exists k (b : bool),
      countState s = CounterDSt (f k) /\
      AtomicCounterSteps
        (CounterIdle 0)
        (lin ρ ++
          if b then
            [(i, CallEv Inc)]
          else
            [])
        (f k).

Definition precs : ThreadName -> forall Ret, CounterSig Ret -> Prec :=
  fun i Ret m s ρ =>
    TIdle i s ρ /\
    invariant i CounterIdle s ρ /\
    lockState s <> LockOwned i.

Definition posts : ThreadName -> forall Ret, CounterSig Ret -> Post Ret :=
  fun i Ret m v _ _ t σ =>
    invariant i CounterIdle t σ /\
    lockState t <> LockOwned i.

Ltac rw_all :=
repeat match goal with
| [ H : ?x = ?y |- ?G ] => try (rewrite H in *); clear H
end.

Ltac commit :=
unfold Commit, precs, guar, invariant, countState, lockState;
intros;
psimpl.

Lemma listHelpAbsurd {A} {xs ys : list A} {x : A} :
  [] <> xs ++ x :: ys.
Admitted.

Theorem atomicCounterCorrect :
  VerifyImpl VE VF rely guar precs atomicCounterImpl posts.
unfold VerifyImpl.
split.
{
  unfold guar, rely, sub, subRelt.
  intros.
  right.
  intros.
  apply H0.
  congruence.
}
split.
admit.
split.
admit.
intros.
destruct m.
simpl.
unfold inc.
{
  eapply safeBind with
    (QI:= fun s ρ t σ =>
      invariant i CounterIdle t σ /\
      lockState t <> LockOwned i)
    (QR:= fun s ρ t σ =>
      lockState s <> LockOwned i /\
      lockState t = LockOwned i /\
      countState s = countState t /\
      ρ = σ /\
      invariant i CounterIdle t σ).
  {
    admit.
  }
  {
    commit.
    dependent destruction H11.
    destruct x2.
    admit.
    eexists.
    split.
    split.
    exists x1, false.
    split.
    congruence.
    exact H5.
    congruence.
    split.
    intros.
    split.
    easy.
    rewrite linSplit.
    easy.
    unfold not.
    intros.
    dependent destruction H11.
    exists [].
    split.
    constructor.
    exists [(i, CallEv Inc)], [].
    constructor.
    constructor.
    constructor.
    split.
    constructor.
    do 2 rewrite app_nil_r.
    apply rt_refl.
  }
  admit.
  split.
  {
    commit.
    dependent destruction H6.
    eexists.
    split.
    split.
    congruence.
    split.
    congruence.
    split.
    easy.
    split.
    easy.
    exists x2, false.
  }
  eapply safeBind with
    (QI:= fun s ρ t σ =>
      invariant (fun k => CounterIncRunning k i) t σ /\
      lockState t = LockOwned i)
    (QR:= fun s ρ t σ =>
      lockState s = LockOwned i /\
      invariant CounterIdle t σ).
  admit.
  {
    commit.
    dependent destruction H5.
    congruence.
    dependent destruction H5.
    eexists.
    split.
    split.
    exists x2.
    split.
    congruence.
  }
  admit.
  split.
  {
    commit.
    do 2 dependent destruction H6.
    eexists.
    split.
    split.
    congruence.
    exists (S n).
    split.
    congruence.

  }
}