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
        snd s = snd t /\
        lin ρ = lin σ).

Lemma relyOwned i s ρ t σ :
  lockState s = LockOwned i ->
  rely i s ρ t σ ->
  snd s = snd t /\
  lin ρ = lin σ.
unfold countState, lockState.
destruct s, t, s, s0.
simpl.
intros.
subst.
destruct H0.
destruct H.
destruct H.
destruct H0.
do 4 destruct H0.
destruct H1.
dependent destruction H3.
split.
easy.
rewrite linSplit.
easy.
unfold not.
intros.
dependent destruction H1.
do 4 destruct H0.
do 4 destruct H1.
dependent destruction H2.
easy.
unfold lockState, countState in H.
simpl in H.
apply H.
easy.
Qed.

Lemma relyTrans i :
  rely i ->> rely i ==> rely i.
unfold rely, inter, sub, subRelt, InvokeAny, TInvoke, ReturnAny, TReturn.
intros.
psimpl.
destruct H, H0.
psimpl.
destruct H2, H1.
Admitted.
Hint Resolve relyTrans : rely_lemmas.

Lemma relyId i :
  id ==> rely i.
unfold sub, subRelt.
intros.
destruct H.
subst.
right.
intros.
easy.
Qed.
Hint Resolve relyId : rely_lemmas.

Definition guar : ThreadName -> Relt :=
  fun i s ρ t σ =>
      lockState s <> LockOwned i ->
        snd s = snd t /\
        lin ρ = lin σ.

Definition invariant : Prec :=
  fun s ρ =>
    exists s',
      countState s = CounterDSt s'.

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

Ltac commit :=
unfold Commit, precs, guar, invariant, countState, lockState;
intros;
psimpl.

Lemma listHelpAbsurd {A} {xs ys : list A} {x : A} :
  [] <> xs ++ x :: ys.
Admitted.

Ltac cond := unfold sub, subRelt, sp, guar, precs, invariant, countState, lockState, TIdle, Util.differ_pointwise in *; intros; psimpl; steps.

Ltac decompose H :=
lazymatch type of H with
| InterStep ?i ?s ?ev ?t =>
  dependent destruction H
| ?P /\ ?Q  =>
  let H1 := fresh in
  let H2 := fresh in
  destruct H as [H1 H2];
  decompose H1;
  decompose H2
| TInvoke ?impl ?i ?A ?m ?s ?ρ ?t ?σ =>
  let HI := fresh in
  let P := fresh "P" in
  let step := fresh "step" in
  destruct H as [P HI];
  destruct HI as [HI step];
  subst
| (?P <<- ?Q) ?s ?ρ =>
  let HI := fresh in
  let is := fresh "is" in
  let iρ := fresh "iρ" in
  let P := fresh "P" in
  let Q := fresh "Q" in
  destruct H as [is HI];
  destruct HI as [iρ HI];
  destruct HI as [P Q];
  move is at top;
  move iρ at top;
  decompose P;
  decompose Q
| ReltToPrec ?P ?s ?ρ =>
  let HI := fresh in
  let is := fresh "is" in
  let iρ := fresh "iρ" in
  destruct H as [is HI];
  destruct HI as [iρ HI];
  move is at top;
  move iρ at top;
  decompose HI
| sp ?impl ?i ?VF ?rel ?prec ?ev ?s ?ρ ?t ?σ =>
  let HI := fresh in
  let rs := fresh "rs" in
  let rρ := fresh "rρ" in
  let BR := fresh "BR" in
  let P := fresh "P" in
  let ss := fresh "ss" in
  let sρ := fresh "sρ" in
  let step := fresh "step" in
  let trace := fresh "trace" in
  let rw := fresh "rw" in
  let AR := fresh "AR" in
  destruct H as [rs HI];
  destruct HI as [rρ HI];
  destruct HI as [BR HI];
  destruct HI as [P HI];
  destruct HI as [ss HI];
  destruct HI as [sρ HI];
  destruct HI as [step HI];
  destruct HI as [trace HI];
  destruct HI as [rw AR];
  move rs at top;
  move rρ at top;
  move ss at top;
  move sρ at top;
  move P before BR;
  move trace at bottom;
  move rw at bottom;
  dependent destruction step;
  decompose P
| _ => idtac
end.

Ltac prepare H :=
decompose H;
repeat lazymatch goal with
| [ H1 : ?P, H2 : ?P |- ?G] =>
  clear H1
end.

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
strongBind.
{
  unfold sub, subRelt, guar.
  intros.
  prepare H.
  simpl in *.
  destruct H0.
  dependent destruction H0.
  
}
admit.
intros.
strongBind.
{
  unfold sub, subRelt.
  intros.
  decompose H.
}