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
  Tactics
  TransUtil
  Util.

Fixpoint ESigN n E : ESig :=
  match n with
  | 0 => E
  | S n => E |+| ESigN n E
  end.

Fixpoint tensorNSpec {T E} n (V : Spec T E) : Spec T (ESigN n E) :=
  match n with
  | 0 => V
  | S n => tensorSpec V (tensorNSpec n V)
  end.

Variant LocalSig {E} : ESig :=
| At {A} (i : nat) (m : E A) : LocalSig A.
Arguments LocalSig : clear implicits.

Variant LocalStep {T E} {V : Spec T E} : (nat -> State V) -> ThreadEvent T (LocalSig E) -> (nat -> State V) -> Prop :=
| LocalCall i A (m : E A) s x t y :
    forall p : i < T,
    s i = x ->
    t i = y ->
    differ_pointwise s t i ->
    V.(Step) x (exist _ i p, CallEv m) y ->
    LocalStep s (exist _ i p, CallEv (At i m)) t
| LocalRet i A (m : E A) v s x t y :
    forall p : i < T,
    s i = x ->
    t i = y ->
    differ_pointwise s t i ->
    V.(Step) x (exist _ i p, RetEv m v) y ->
    LocalStep s (exist _ i p, RetEv (At i m) v) t.
Arguments LocalStep {T E} V.

Program Definition localSpec {T E} (V : Spec T E) : Spec T (LocalSig E) := {|
  State := Name T -> State V;
  Step := LocalStep V;
  Init _ := Init V
|}.

Admit Obligations.