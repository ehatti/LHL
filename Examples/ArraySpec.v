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


Variant ArraySig {E} {N : nat} : ESig :=
| At {A} (i : nat) (m : E A) : ArraySig A.
Arguments ArraySig : clear implicits.

Variant ArrayStep {T E N} {V : Spec T E} :
  (nat -> State V) ->
  ThreadEvent T (ArraySig E N) ->
  (nat -> State V) ->
  Prop :=
| ArrayCall i A (m : E A) s x y n :
    n < N ->
    V.(Step) x (i, CallEv m) y ->
    ArrayStep
      (fun k => if n =? k then x else s k)
      (i, CallEv (At n m))
      (fun k => if n =? k then y else s k)
| ArrayRet i A (m : E A) v s x y n :
    n < N ->
    V.(Step) x (i, RetEv m v) y ->
    ArrayStep
      (fun k => if n =? k then x else s k)
      (i, RetEv (At n m) v)
      (fun k => if n =? k then y else s k).
Arguments ArrayStep {T E N} V.

Program Definition arraySpec {T E} N (V : Spec T E) : Spec T (ArraySig E N) := {|
  State := nat -> State V;
  Step := ArrayStep V;
  Init _ := Init V
|}.

Admit Obligations.