From LHL.Core Require Import
  Program
  Specs.

Variant CellSig {A} : ESig :=
| Write (x : A) : CellSig unit
| Read : CellSig A.
Arguments CellSig : clear implicits.

Record CellPend {A} := MkCellPend {
  CellThread : ThreadName;
  CellRetTy : Type;
  CellName : CellSig A CellRetTy
}.
Arguments CellPend : clear implicits.
Arguments MkCellPend {A}.

Variant CellState {A} :=
| CellUB (* todo: make sequentially consistent *)
| CellDef (v : option A) (m : option (CellPend A)).
Arguments CellState : clear implicits.

Definition CellUndef {A} := @CellDef A None None.
Definition CellIdle {A} (v : option A) := CellDef v None.
Definition CellWriteRan {A} i v (v' : A) :=
  CellDef v (Some (MkCellPend i _ (Write v'))).
Definition CellReadRan {A} i (v : A) :=
  CellDef (Some v) (Some (MkCellPend i _ Read)).

Variant CellStep {A} : CellState A -> ThreadEvent (CellSig A) -> CellState A -> Prop :=
| CellCallWrite i v v' :
    CellStep (CellIdle v) (i, CallEv (Write v')) (CellWriteRan i v v')
| CellRetWrite i v v' :
    CellStep (CellWriteRan i v v') (i, RetEv (Write v') tt) (CellIdle (Some v'))
| CellCallRead i v :
    CellStep (CellIdle (Some v)) (i, CallEv Read) (CellReadRan i v)
| CellRetRead i v :
    CellStep (CellReadRan i v) (i, RetEv Read v) (CellIdle (Some v))
| CellDoubleWrite i j v v' v'' :
    i <> j ->
    CellStep (CellWriteRan i v v') (j, CallEv (Write v'')) CellUB
| CellDoubleRead i j v :
    i <> j ->
    CellStep (CellReadRan i v) (j, CallEv Read) CellUB
| CellReadUndef i :
    CellStep (CellIdle None) (i, CallEv Read) CellUB
| CellStepUB e :
    CellStep CellUB e CellUB.

Program Definition cellSpec A : Spec (CellSig A) := {|
  State := CellState A;
  Step := CellStep;
  Init := CellUndef
|}.

Admit Obligations.