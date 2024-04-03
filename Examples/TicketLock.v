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

From Coq Require Import
  Arith.PeanoNat.

Definition Underlay := FAISig |+| CounterSig |+| YieldSig |+| VarSig nat.

Definition acq : Prog Underlay unit :=
  my_tick <- call FAI;
  _ <- call (SetVar my_tick);
  while
    (cur_tick <- call Get; ret (negb (cur_tick =? my_tick)))
    (call Yield).

Definition rel : Prog Underlay unit :=
  call Inc.

Definition ticketLockImpl : Impl Underlay LockSig :=
  fun _ m => match m with
  | Acq => acq
  | Rel => rel
  end.

Definition E := Underlay.
Definition F := LockSig.
Definition VE := tensorSpec faiSpec (tensorSpec counterSpec (tensorSpec yieldSpec (varSpec nat))).
Definition VF := lockSpec.

Definition Relt := Relt VE VF.
Definition Prec := Prec VE VF.
Definition Post := Post VE VF.

Definition countState (s : @InterState E F VE) : State counterSpec :=
  fst (snd (snd s)).
Definition varState (s : @InterState E F VE) : State (varSpec nat) :=
  snd (snd (snd (snd s))).

Definition newtkt (s : @InterState E F VE) : nat :=
  match fst (snd s) with
  | FAICalled _ n => n
  | FAIIdle n => n
  end.
Definition ctrval (s : @InterState E F VE) : nat :=
  match countState s with
  | CounterIdle n => n
  | CounterGetCalled _ n => n
  | CounterIncCalled _ n => n
  | CounterUB => 0
  end.
Definition mytkt i (s : @InterState E F VE) : option nat :=
  match snd (snd (snd (snd s))) i with
  | VarUnset => None
  | VarIdle n => Some n
  | VarSetCalled n => Some n
  | VarGetCalled n => Some n
  end.

Definition Inv (i : ThreadName) : Prec :=
  fun s ρs =>
    countState s <> CounterUB /\
    (forall tkt,
      Some tkt = mytkt i s ->
      ctrval s <= tkt) /\
    ctrval s <= newtkt s /\
    (forall ρ,
      Some (ctrval s) = mytkt i s ->
      ρs ρ ->
      owner (PState ρ) = Some i \/ owner (PState ρ) = None) /\
    (newtkt s = ctrval s ->
      forall ρ,
        ρs ρ ->
        PState ρ = LockIdle) /\
    (forall ρ,
      ρs ρ ->
      owner (PState ρ) = Some i ->
      mytkt i s = Some (ctrval s)).

Definition Acqed (i : ThreadName) : Prec :=
  fun s ρs =>
    Inv i s ρs /\
    (forall ρ,
      ρs ρ ->
      owner (PState ρ) = Some i).

Definition Reled (i : ThreadName) : Prec :=
  fun s ρs =>
    Inv i s ρs /\
    (forall ρ,
      ρs ρ ->
      owner (PState ρ) <> Some i).

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

Definition Rely (i : ThreadName) : Relt :=
  fun s ρs t σs =>
    InvokeAny ticketLockImpl i s ρs t σs \/
    ReturnAny ticketLockImpl i s ρs t σs \/
    countState t <> CounterUB /\
    (forall tkt tkt',
      mytkt i s = Some tkt ->
      mytkt i t = Some tkt' ->
      ctrval s <= tkt ->
      ctrval t <= tkt') /\
    ctrval t <= newtkt t /\
    (forall ρ σ,
      ρs ρ ->
      σs σ ->
      mytkt i s = Some (ctrval s) ->
      mytkt i t = Some (ctrval t) ->
      owner (PState ρ) = Some i \/ owner (PState ρ) = None ->
      owner (PState σ) = Some i \/ owner (PState σ) = None) /\
    (forall σ,
      σs σ ->
      newtkt t = ctrval t ->
      PState σ = LockIdle) /\
    (forall ρ σ,
      ρs ρ ->
      σs σ ->
      owner (PState ρ) = Some i ->
      PState ρ = PState σ /\
      ctrval s = ctrval t) /\
    (forall ρ σ,
      ρs ρ ->
      σs σ ->
      owner (PState ρ) <> Some i ->
      owner (PState σ) <> Some i).

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
    (forall j ρ σ,
      ρs ρ ->
      σs σ ->
      i <> j ->
      mytkt j s = Some (ctrval s) ->
      owner (PState ρ) = Some j \/ owner (PState ρ) = None ->
      mytkt j t = Some (ctrval t) ->
      owner (PState ρ) = Some j \/ owner (PState ρ) = None) /\
    (forall ρ,
      ρs ρ ->
      newtkt t = ctrval t ->
      PState ρ = LockIdle) /\
    (forall ρ σ,
      ρs ρ ->
      σs σ ->
      owner (PState ρ) <> Some i /\ owner (PState ρ) <> None ->
      PState ρ = PState σ) /\
    (forall ρ,
      ρs ρ ->
      ~OwnsLock i (PState ρ) ->
      ctrval s = ctrval t) /\
    (forall ρ σ,
      ρs ρ ->
      σs σ ->
      owner (PState ρ) <> Some i ->
      owner (PState σ) <> Some i).

Theorem ticketLockCorrect :
  VerifyImpl VE VF Rely Guar Precs ticketLockImpl Posts.
split.
admit.
split.
admit.
split.
admit.
intros.
destruct m.
simpl.
unfold acq.
{
  
}