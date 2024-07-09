From LHL.Core Require Import
  Program
  Specs.

Variant VarSig {A} : ESig :=
| Put (x : A) : VarSig unit
| Get : VarSig A.
Arguments VarSig : clear implicits.

Record VarPend {T A} := MkVarPend {
  VarThreadName : Name T;
  VarRetTy : Type;
  VarName : VarSig A VarRetTy
}.
Arguments VarPend : clear implicits.
Arguments MkVarPend {T A}.

Variant VarState {T A} :=
| VarUB (* todo: make sequentially consistent *)
| VarDef (v : option A) (m : option (VarPend T A)).
Arguments VarState : clear implicits.

Definition VarUndef {T A} := @VarDef T A None None.
Definition VarIdle {T A} (v : option A) := VarDef (T:=T) v None.
Definition VarPutRan {T A} i v (v' : A) :=
  VarDef (T:=T) v (Some (MkVarPend i _ (Put v'))).
Definition VarGetRan {T A} i (v : A) :=
  VarDef (T:=T) (Some v) (Some (MkVarPend i _ Get)).

Variant VarStep {T A} : VarState T A -> ThreadEvent  T(VarSig A) -> VarState T A -> Prop :=
| VarCallPut i v v' :
    VarStep (VarIdle v) (i, CallEv (Put v')) (VarPutRan i v v')
| VarRetPut i v v' :
    VarStep (VarPutRan i v v') (i, RetEv (Put v') tt) (VarIdle (Some v'))
| VarCallGet i v :
    VarStep (VarIdle (Some v)) (i, CallEv Get) (VarGetRan i v)
| VarRetGet i v :
    VarStep (VarGetRan i v) (i, RetEv Get v) (VarIdle (Some v))
| VarDoublePut i j v v' v'' :
    i <> j ->
    VarStep (VarPutRan i v v') (j, CallEv (Put v'')) VarUB
| VarDoubleGet i j v :
    i <> j ->
    VarStep (VarGetRan i v) (j, CallEv Get) VarUB
| VarGetUndef i :
    VarStep (VarIdle None) (i, CallEv Get) VarUB
| VarStepUB e :
    VarStep VarUB e VarUB.

Program Definition varSpec {T A} : Spec T (VarSig A) := {|
  State := VarState T A;
  Step := VarStep;
  Init := VarUndef
|}.

Admit Obligations.