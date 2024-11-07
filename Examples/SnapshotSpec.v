From LHL.Core Require Import
  Program
  Specs.

From LHL.Util Require Import
  Util.

Variant SnapshotSig {A} : ESig :=
| Update (v : A) : SnapshotSig (set A).
Arguments SnapshotSig : clear implicits.

Variant SnapshotState {T A} :=
| SnapUB
| SnapDef (vs : set A) (m : Name T -> bool).
Arguments SnapshotState : clear implicits.

Variant SnapshotStep {T A} : SnapshotState T A -> ThreadEvent T (SnapshotSig A) -> SnapshotState T A -> Prop :=
| SnapCallUpdate i v vs m m' :
    m i = false ->
    m' i = true ->
    differ_pointwise m m' i ->
    SnapshotStep (SnapDef vs m) (i, CallEv (Update v)) (SnapDef (insert v vs) m')
| SnapRetUpdate i v vs m :
    m i = true ->
    SnapshotStep (SnapDef vs m) (i, RetEv (Update v) vs) (SnapDef vs m)
| SnapDoubleWrite i v vs m :
    m i = true ->
    SnapshotStep (SnapDef vs m) (i, CallEv (Update v)) SnapUB
| SnapStepUB e :
    SnapshotStep SnapUB e SnapUB.

Program Definition snapshotSpec {T A} : Spec T (SnapshotSig A) := {|
  State := SnapshotState T A;
  Step := SnapshotStep;
  Init := SnapDef emp (fun _ => false)
|}.

Next Obligation.
generalize dependent p.
