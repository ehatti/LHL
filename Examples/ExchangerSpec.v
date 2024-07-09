From LHL.Core Require Import
  Program
  Specs.

From LHL.Util Require Import
  Util.

Variant ExchSig {A} : ESig :=
| Exch (v : A) : ExchSig (option A).
Arguments ExchSig : clear implicits.

Variant ExchState {T A} :=
| ExchDef (p d : set (Name T * A)).
Arguments ExchState : clear implicits.

Notation "{}" := emp.
Notation "{ i => x }" := (insert (i, x) emp).
Notation "{ i => x , j => y }" := (insert (i, x) (insert (j, y) emp)).

Variant ExchStep {T A} : ExchState T A -> ThreadEvent T (ExchSig A) -> ExchState T A -> Prop :=
| ExchCall1 i x : ExchStep
    (ExchDef {} {})
    (i, CallEv (Exch x))
    (ExchDef {i => x} {})
| ExchCall2 i x j y : i <> j -> ExchStep
    (ExchDef {i => x} {})
    (j, CallEv (Exch y))
    (ExchDef {i => x, j => y} {})
| ExchRet1 i x j y : i <> j -> ExchStep
    (ExchDef {i => x, j => y} {})
    (i, RetEv (Exch x) (Some y))
    (ExchDef {i => x} {j => y})
| ExchRet2 i x j y : i <> j -> ExchStep
    (ExchDef {i => x} {j => y})
    (j, RetEv (Exch y) (Some x))
    (ExchDef {} {})
| ExchFail i x : ExchStep
    (ExchDef {i => x} {})
    (i, RetEv (Exch x) None)
    (ExchDef {} {}).

Program Definition exchSpec {T A} : Spec T (ExchSig A) := {|
  State := ExchState T A;
  Step := ExchStep;
  Init := ExchDef {} {}
|}.

Admit Obligations.