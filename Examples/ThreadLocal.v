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

Fixpoint ESigN n E : ESig :=
  match n with
  | 0 => E
  | S n => E |+| ESigN n E
  end.

Fixpoint tensorNSpec {E} n (V : Spec E) : Spec (ESigN n E) :=
  match n with
  | 0 => V
  | S n => tensorSpec V (tensorNSpec n V)
  end.

Variant LocalSig {E : ESig} : ESig :=
| At {A} (i : ThreadName) (m : E A) : LocalSig A.
Arguments LocalSig : clear implicits.

Variant LocalStep {E} {V : Spec E} : (ThreadName -> State V) -> ThreadEvent (LocalSig E) -> (ThreadName -> State V) -> Prop :=
| LocalCall i A (m : E A) s x t y :
    s i = x ->
    t i = y ->
    differ_pointwise s t i ->
    V.(Step) x (i, CallEv m) y ->
    LocalStep s (i, CallEv (At i m)) t
| LocalRet i A (m : E A) v s x t y :
    s i = x ->
    t i = y ->
    differ_pointwise s t i ->
    V.(Step) x (i, RetEv m v) y ->
    LocalStep s (i, RetEv (At i m) v) t.
Arguments LocalStep {E} V.

Program Definition localSpec {E} (V : Spec E) : Spec (LocalSig E) := {|
  State := ThreadName -> State V;
  Step := LocalStep V;
  Init _ := Init V
|}.

Admit Obligations.