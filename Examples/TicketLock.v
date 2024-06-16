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
  Arith.PeanoNat.

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
      InvokeAny ticketLockImpl j s ρs t σs \/
      ReturnAny ticketLockImpl j s ρs t σs).

Definition Rely (i : ThreadName) : Relt :=
  fun s ρs t σs => forall ρ, ρs = eq ρ -> exists σ, σs = eq σ /\
    ManyInvokeReturn i s ρs t σs /\
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
      owner (PState σ) <> Some i).

Lemma Rely_refl :
  forall i s ρ, Rely i s ρ s ρ.
unfold Rely. intros. subst.
exists ρ0. split. easy.
repeat split.
constructor.
all: easy.
Qed.

Lemma Rely_trans :
  forall i, Rely i ->> Rely i ==> Rely i.
unfold sub, subRelt. intros. pdestruct H.
unfold Rely in H. unfold Rely. intros. subst.
specialize (H ρ0 eq_refl). destruct_all. subst.
specialize (H0 x1 eq_refl). destruct_all. subst.
exists x0. split. easy.
repeat split.
{
  eapply rtcTrans. repeat eexists.
  exact H1. easy.
}
all: (intros; auto).
assert (H' := H). apply H8 in H. destruct_all. rewrite H in H'.
apply H16 in H'. destruct_all. congruence.
assert (H' := H). apply H8 in H. destruct_all. rewrite H in H'.
apply H16 in H'. destruct_all. congruence.
Qed.


Lemma Inv_stable :
  forall i, Stable (Rely i) (Inv i).
unfold Stable, stablePrec, sub, subPrec, Rely, Inv. intros.
psimpl. exists x2. split. easy.
destruct H2.
{
  unfold ManyInvokeRetu
}

Definition Guar (i : ThreadName) : Relt :=
  fun s ρs t σs =>
    countState t <> CounterUB /\
    (forall j tkt tkt',
      i <> j ->
      mytkt j s = Some tkt ->
      mytkt j t = Some tkt' ->
      ctrval s <= tkt ->
      ctrval t <= tkt') /\
    ctrval t <= newtkt t /\
    (forall j σ, σs σ ->
      i <> j ->
      mytkt j s = Some (ctrval s) ->
      owner (PState ρ) = Some j \/ owner (PState ρ) = None ->
      mytkt j t = Some (ctrval t) ->
      owner (PState ρ) = Some j \/ owner (PState ρ) = None) /\
    (forall ρ,
      ρs ρ ->
      newtkt t = ctrval t ->
      PState ρ = LockUnowned) /\
    (forall ρ σ,
      ρs ρ ->
      σs σ ->
      owner (PState ρ) <> Some i /\ owner (PState ρ) <> None ->
      PState ρ = PState σ) /\
    (forall ρ,
      ρs ρ ->
      ~OwnsLock i (PState ρ) ->
      ctrval s = ctrval t) /\
    (forall ρ σ, σs σ ->
      exists ρ, ρs ρ /\
      (owner (PState ρ) <> Some i ->
       owner (PState σ) <> Some i)).

Theorem ticketLockCorrect :
  VerifyImpl VE VF Rely Guar Precs ticketLockImpl Posts.