From LHL.Core Require Import
  Program
  Specs.

Variant CellSig {A} : ESig :=
| Write (x : A) : CellSig unit
| Read : CellSig A.
Arguments CellSig : clear implicits.

Record CellPend {T A} := MkCellPend {
  CellThread : Name T;
  CellRetTy : Type;
  CellName : CellSig A CellRetTy
}.
Arguments CellPend : clear implicits.
Arguments MkCellPend {T A}.

Variant CellState {T A} :=
| CellUB (* todo: make sequentially consistent *)
| CellDef (v : option A) (m : option (CellPend T A)).
Arguments CellState : clear implicits.

Definition CellUndef {T A} := @CellDef T A None None.
Definition CellIdle {T A} (v : option A) := CellDef (T:=T) v None.
Definition CellWriteRan {T A} i v (v' : A) :=
  CellDef (T:=T) v (Some (MkCellPend i _ (Write v'))).
Definition CellReadRan {T A} i (v : A) :=
  CellDef (T:=T) (Some v) (Some (MkCellPend i _ Read)).

Variant CellStep {T A} : CellState T A -> ThreadEvent T (CellSig A) -> CellState T A -> Prop :=
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
| CellReadUndef i :
    CellStep (CellIdle None) (i, CallEv Read) CellUB
| CellStepUB e :
    CellStep CellUB e CellUB.

Program Definition cellSpec {T A} : Spec T (CellSig A) := {|
  State := CellState T A;
  Step := CellStep;
  Init := CellUndef
|}.

Admit Obligations.