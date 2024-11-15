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

Definition Index N := {i | i < N}.

Variant ArraySig {E} {N : nat} : ESig :=
| At {A} (i : Index N) (m : E A) : ArraySig A.
Arguments ArraySig : clear implicits.

Variant ArrayStep {T E N} {V : Spec T E} :
  (Index N -> State V) ->
  ThreadEvent T (ArraySig E N) ->
  (Index N -> State V) ->
  Prop :=
| ArrayCall i A (m : E A) s t x y n :
    (* n < N -> *)
    True ->
    s n = x ->
    t n = y ->
    differ_pointwise s t n ->
    V.(Step) x (i, CallEv m) y ->
    ArrayStep s (i, CallEv (At n m)) t
| ArrayRet i A (m : E A) v s t x y n :
    (* n < N -> *)
    True ->
    s n = x ->
    t n = y ->
    differ_pointwise s t n ->
    V.(Step) x (i, RetEv m v) y ->
    ArrayStep s (i, RetEv (At n m) v) t.
Arguments ArrayStep {T E N} V.

Program Definition arraySpec {T E} N (V : Spec T E) : Spec T (ArraySig E N) := {|
  State := Index N -> State V;
  Step := ArrayStep V;
  Init _ := Init V
|}.

Next Obligation.
Admitted.