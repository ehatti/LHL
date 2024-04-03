From LHL.Core Require Import
  Specs
  Traces
  Program.

From LHL.Util Require Import
  Util.

Variant VarSig {S} : ESig :=
| SetVar : S -> VarSig unit
| GetVar : VarSig S.
Arguments VarSig : clear implicits.

Variant VarValue {S} :=
| VarUnset
| VarIdle (s : S)
| VarSetCalled (s : S)
| VarGetCalled (s : S).
Arguments VarValue : clear implicits.

Definition VarState S :=
  ThreadName -> VarValue S.

Variant VarStep {S} : VarState S -> ThreadEvent (VarSig S) -> VarState S -> Prop :=
| VarCallSet i (m m' : VarState S) s t :
  m i = VarIdle s ->
  m' i = VarSetCalled t ->
  differ_pointwise m m' i ->
  VarStep m (i, CallEv (SetVar t)) m'
| VarRetSet i (m m' : VarState S) s :
  m i = VarSetCalled s ->
  m' i = VarIdle s ->
  differ_pointwise m m' i ->
  VarStep m (i, RetEv (SetVar s) tt) m'
| VarCallGet i m m' s :
  m i = VarIdle s ->
  m' i = VarGetCalled s ->
  differ_pointwise m m' i ->
  VarStep m (i, CallEv GetVar) m'
| VarRetGet i m m' s :
  m i = VarGetCalled s ->
  m' i = VarIdle s ->
  differ_pointwise m m' i ->
  VarStep m (i, RetEv GetVar s) m'.

Definition varSpec S : Spec (VarSig S) := {|
  State := VarState S;
  Step := VarStep;
  Init := fun _ => VarUnset
|}.