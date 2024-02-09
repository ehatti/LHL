From LHL.Core Require Import
  Program
  Specs
  Logic
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

Module AtomicCounterObj <: OBJECT.
  Definition E := Underlay.
  Definition F := CounterSig.
  Definition VE := tensorSpec lockSpec racyCounterSpec.
  Definition VF := atomicCounterSpec.
End AtomicCounterObj.

Module Logic := Logic(AtomicCounterObj).
Import AtomicCounterObj.
Import Logic.
Import Ps.

Definition countState (s : @InterState E F VE) : RacyCounterState :=
  snd (snd s).

Definition lockState (s : @InterState E F VE) : LockState :=
  fst (snd s).

Definition int : Relt :=
  fun s ρ t σ =>
    exists i,
    (exists A (m : F A),
      InterStep (impl:=atomicCounterImpl) i s (i, OCallEv m) t) \/
    (exists A (m : F A) v,
      InterStep (impl:=atomicCounterImpl) i s (i, ORetEv m v) t).

Definition rely : ThreadName -> Relt :=
  fun i s ρ t σ =>
    int s ρ t σ \/
    (lockState t = LockOwned i ->
      countState s = countState t /\
      lin VF ρ = lin VF σ).

Definition guar : ThreadName -> Relt :=
  fun i s ρ t σ =>
    int s ρ t σ \/
    (lockState t <> LockOwned i ->
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

Ltac psimpl :=
repeat repeat match goal with
| [ H : ReltCompose ?P ?Q ?s ?ρ ?t ?σ |- ?G] => destruct H
| [ H : ?P /\ ?Q |- ?G ] => destruct H
| [ H : exists x, ?P |- ?G ] => destruct H
| [ H : ReltToPrec ?R ?s ?ρ |- ?G ] => destruct H
| [ H : PrecToRelt ?P ?s ?ρ ?t ?σ |- ?G ] => destruct H
| [ H : Invoke ?impl ?i ?A ?l ?s ?ρ ?t ?σ |- ?G ] => destruct H
end;
repeat match goal with
| [ H : InterStep ?i ?st ?ev ?st' |- ?G ] => dependent destruction H
| [ H : Step ?impl ?st ?ev ?st' |- ?G ] => idtac ev; simpl in H; dependent destruction H
end;
simpl in *;
subst.

Ltac commit :=
unfold Commit;
intros;
repeat psimpl.

Lemma new_poss_refl : forall (ρ : Trace (ThreadEvent F)), ρ --> ρ.
intros.
exists nil.
split.
constructor.
rewrite app_nil_r.
exists nil, nil.
split.
constructor.
split.
constructor.
apply rt_refl.
Qed.

Theorem atomicCounterCorrect :
    VerifyImpl rely guar precs atomicCounterImpl posts.
unfold VerifyImpl.
split.
intros.
dependent destruction m; simpl.
unfold inc.
eapply SafeWeakenPost.
eapply SafeBind with
  (QI:= fun s ρ t σ =>
    lockState t = LockAcqRunning i /\
    σ = ρ)
  (QR:= fun s ρ t σ =>
    lockState t = LockOwned i /\
    σ = app ρ (cons (i, RetEv Inc tt) nil)).
{
  unfold VerifyPrim.
  split.
  {
    unfold Stable, stablePrec, impl, implPrec.
    intros.
    do 10 destruct H.
  }
  split.
  admit.
  commit.
  dependent destruction H7.
  destruct st, st'.
  simpl in *.
  subst.
  eexists.
  split.
  easy.
  unfold guar.
  split.
  right.
  unfold lockState.
  simpl.
  intros.
  easy.
  apply new_poss_refl.
}
intros.
split.
{
  unfold VerifyPrim.
  split.
  admit.
  split.
  admit.
  commit.
  dependent destruction H6.
  destruct st, st'.
  simpl in *.
  subst.
  eexists.
  split.
  easy.
  unfold guar.
  split.
  right.
  unfold lockState.
  simpl.
  intros.
  easy.
  exists nil.
  split.
  constructor.
  exists nil, (cons (i, RetEv Inc tt) nil).
  split.
  constructor.
  constructor.
  constructor.
  constructor.
  do 2 rewrite app_nil_r.
  apply rt_refl.
}
eapply SafeBind with
  (QI:= fun s ρ t σ =>
    lockState t = LockOwned i /\
    σ = ρ /\
    exists n,
    countState t = CounterDSt (CounterIncRunning n i))
  (QR:= fun s ρ t σ =>
    lockState t = LockOwned i /\
    σ = ρ /\
    exists n,
    countState s = CounterDSt (CounterIncRunning n i) /\
    countState t = CounterDSt (CounterIdle (S n))).
{
  unfold VerifyPrim.
  split.
  admit.
  split.
  admit.
  commit.
  
}
intros.
split.
admit.
eapply SafeBind with
  (QI:= fun s ρ t σ =>
    lockState t = LockRelRunning i /\
    σ = ρ)
  (QR:= fun s ρ t σ =>
    lockState t = LockUnowned /\
    σ = ρ).
admit.
intros.
split.
admit.
eapply SafeWeaken.
apply SafeReturn.