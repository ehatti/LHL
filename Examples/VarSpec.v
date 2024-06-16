From LHL.Core Require Import
  Specs
  Traces
  Program.

From LHL.Util Require Import
  Util.

Variant VarSig {S} : ESig :=
| SetVar : S -> VarSig unit
| GetVar : VarSig S
| ClrVar : VarSig unit.
Arguments VarSig : clear implicits.

Record VarPend {S} := MkVarPend {
  VarRetTy : Type;
  VarCall : VarSig S VarRetTy
}.
Arguments VarPend : clear implicits.
Arguments MkVarPend {S}.

Variant VarValue {S} :=
| VarUnset
| VarSet (s : S) (m : option (VarPend S)).
Arguments VarValue : clear implicits.

Definition VarIdle {S} (s : S) := VarSet s None.
Definition VarSetRan {S} (s t : S) :=
  VarSet s (Some (MkVarPend _ (SetVar t))).
Definition VarGetRan {S} (s : S) :=
  VarSet s (Some (MkVarPend _ GetVar)).
Definition VarClrRan {S} (s : S) :=
  VarSet s (Some (MkVarPend _ ClrVar)).

Definition VarState S := ThreadName -> VarValue S.

Variant VarStep {S} : VarState S -> ThreadEvent (VarSig S) -> VarState S -> Prop :=
| VarCallSet i m m' s t :
    m i = VarIdle s ->
    m' i = VarSetRan s t ->
    differ_pointwise m m' i ->
    VarStep m (i, CallEv (SetVar t)) m'
| VarRetSet i m m' s t :
    m i = VarSetRan s t ->
    m' i = VarIdle t ->
    differ_pointwise m m' i ->
    VarStep m (i, RetEv (SetVar t) tt) m'
| VarCallGet i m m' s :
    m i = VarIdle s ->
    m' i = VarGetRan s ->
    differ_pointwise m m' i ->
    VarStep m (i, CallEv GetVar) m'
| VarRetGet i m m' s :
    m i = VarGetRan s ->
    m' i = VarIdle s ->
    differ_pointwise m m' i ->
    VarStep m (i, RetEv GetVar s) m'
| VarInvClr i m m' s :
    m i = VarIdle s ->
    m' i = VarClrRan s ->
    differ_pointwise m m' i ->
    VarStep m (i, CallEv ClrVar) m'
| VarRetClr i m m' s :
    m i = VarClrRan s ->
    m' i = VarUnset ->
    differ_pointwise m m' i ->
    VarStep m (i, RetEv ClrVar tt) m'.

Definition varSpec S : Spec (VarSig S) := {|
  State := VarState S;
  Step := VarStep;
  Init _ := VarUnset
|}.