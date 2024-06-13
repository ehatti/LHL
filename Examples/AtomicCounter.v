From LHL.Core Require Import
  Program
  ProgramRules
  Specs
  Logic
  LogicFacts
  Tensor
  Traces
  Linearizability.

From LHL.Util Require Import
  Tactics.

From LHL.Examples Require Import
  CounterSpec
  LockSpec.

From Coq Require Import
  Arith.PeanoNat.

Definition impl : Impl LockSig CounterSig :=
  fun _ _ =>
    .