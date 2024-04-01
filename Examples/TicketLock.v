From LHL.Core Require Import
  Program
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
  CounterSpec.

From Coq Require Import
  Arith.PeanoNat.

Definition Underlay := FAISig |+| CounterSig |+| YieldSig.

Definition acq : Prog Underlay unit :=
  my_tick <- call FAI;
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
Definition VE := tensorSpec faiSpec (tensorSpec counterSpec yieldSpec).
Definition VF := lockSpec.

Definition Relt := Relt VE VF.
Definition Prec := Prec VE VF.
Definition Post := Post VE VF.

Definition Rely (i : ThreadName) : Relt :=
  fun s ρ t σ => True.

Definition Guar (i : ThreadName) : Relt :=
  fun s ρ t σ => True.

Definition Precs (i : ThreadName) {A} (m : LockSig A) : Prec :=
  fun s ρ =>
    True.

Definition Posts (i : ThreadName) {A} (m : LockSig A) : Post A :=
  fun _ s ρ t σ =>
    True.

Theorem ticketLockCorrect :
  VerifyImpl VE VF Rely Guar Precs ticketLockImpl Posts.
