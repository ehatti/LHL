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
  ReltRTC (fun s ρ t σ =>
    InvokeAny atomicCounterImpl s ρ t σ \/
    ReturnAny atomicCounterImpl s ρ t σ).

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
repeat lazymatch goal with
| [ H : ReltCompose ?P ?Q ?s ?ρ ?t ?σ |- ?G] => destruct H
| [ H : PrecCompose ?P ?Q ?s ?ρ |- ?G] => destruct H
| [ H : ?P /\ ?Q |- ?G ] => destruct H
| [ H : exists x, ?P |- ?G ] => destruct H
| [ H : Invoke ?impl ?i ?A ?l ?s ?ρ ?t ?σ |- ?G ] => destruct H
| [ H : LinRw ?ρ ?σ |- ?G ] => destruct H
end;
repeat lazymatch goal with
| [ H : InterStep ?i ?st ?ev ?st' |- ?G ] => dependent destruction H
| [ H : Step ?impl ?st ?ev ?st' |- ?G ] => idtac ev; simpl in H; dependent destruction H
end;
simpl in *;
subst;
repeat lazymatch goal with
| [ H : ?A, H' : ?A |- ?G] => clear H'
end.

Ltac commit :=
unfold Commit;
intros;
repeat psimpl.

Ltac stable :=
unfold Stable, stablePrec, stableRelt, impl, implPrec, implRelt;
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

Lemma safeBind {impl i R G P A B} {m : E A} {k : A -> Prog E B} :
  forall (QI QR S : Relt),
  Stable R P ->
  Stable R QI ->
  Stable R QR ->
  Stable R S ->
  Commit i impl R G P (CallEv m) QI ->
  (forall v,
    Commit i impl R G (P;; QI) (RetEv m v) QR /\
    VerifyProg i impl R G (P;; QI;; QR) (k v) S) ->
  VerifyProg i impl R G P (Bind m k) (QI; QR; S).
intros.
constructor.
easy.
intros.
specialize (H4 v).
split.
split.
apply precCompStable; easy.
split.
easy.
easy.
easy.
Qed.

Lemma safeBindUnit {impl i R G P A} {m : E unit} {k : unit -> Prog E A} :
  forall (QI QR S : Relt),
  Stable R P ->
  Stable R QI ->
  Stable R QR ->
  Stable R S ->
  Commit i impl R G P (CallEv m) QI ->
  Commit i impl R G (P;; QI) (RetEv m tt) QR /\
  VerifyProg i impl R G (P;; QI;; QR) (k tt) S ->
  VerifyProg i impl R G P (Bind m k) (QI; QR; S).
intros.
apply safeBind.
easy.
easy.
easy.
easy.
easy.
intros.
destruct v.
easy.
Qed.

Lemma precStabilizedStable {R P} :
  All (R; R ==> R) ->
  Stable R (P;; R).
intros.
unfold Stable, stablePrec, impl, implPrec.
intros.
do 6 destruct H0.
do 2 eexists.
split.
exact H0.
apply H.
do 2 eexists.
split.
exact H2.
easy.
Qed.

Theorem atomicCounterCorrect :
  VerifyImpl rely guar precs atomicCounterImpl posts.
unfold VerifyImpl.
split.
{
  intros.
  dependent destruction m; simpl.
  unfold inc.
  eapply SafeWeakenPost.
  apply safeBindUnit.
  {
    unfold precs, rely.
    stable.
    do 2 eexists.
    split.
    split.
    exact H.
    easy.
    unfold Invoke.
  }
}