From LHL.Core Require Import
  ProgramRules
  LogicFacts
  SingConds
  Program
  ProgramFacts
  Traces
  Tensor
  Logic
  Specs.

From LHL.Util Require Import
  TransUtil
  Tactics
  Util.

From LHL.Examples Require Import
  ExchangerSpec
  RandomSpec
  ThreadLocal.

Definition E T A :=
  RandSig |+| ESigN T (ExchSig A).

Definition VE T A : Spec T (E T A) :=
  tensorSpec randSpec (tensorNSpec T (@exchSpec T A)).

Definition F A := ExchSig A.

Definition VF T A : Spec T (F A) :=
  exchSpec.

Definition exch {T A} (i : Name T) (v : A) : Prog (E T A) (option A)