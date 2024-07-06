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
  OMemSpec
  WriteSnapshotSpec.

From LHL.Util Require Import
  Tactics
  TransUtil
  Util.

Definition Underlay := OMemSig nat.

Definition write_snapshot : nat 