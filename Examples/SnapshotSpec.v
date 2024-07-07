From LHL.Core Require Import
  Program
  Specs.

From LHL.Examples Require Import
  OMemSpec.

From LHL.Util Require Import
  Util.

Definition set A := A -> bool.

Definition insert {A} (s : set A) (x : A) : set A :=
  fun y => if x =? y then true else s y.

Definition emp {A} : set A := fun _ => false.

Variant SnapshotSig {A} : ESig :=
| Update (v : A) : SnapshotSig unit
| Query : SnapshotSig (set A).
Arguments SnapshotSig : clear implicits.

Variant SnapshotState {A} :=
| SnapDef (vs : set A) (m : ThreadName -> option {B & SnapshotSig A B}).
Arguments SnapshotState : clear implicits.

Variant SnapshotStep {A} : SnapshotState A -> ThreadEvent (SnapshotSig A) -> SnapshotState A -> Prop :=
| SnapCallUpdate i v vs m m' :
    m i = None ->
    m' i = Some (existT _ _ (Update v)) ->
    differ_pointwise m m' i ->
    SnapshotStep (SnapDef vs m) (i, CallEv (Update v)) (SnapDef vs m')
| SnapRetUpdate i v vs m m' :
    m i = Some (existT _ _ (Update v)) ->
    m' i = None ->
    differ_pointwise m m' i ->
    SnapshotStep (SnapDef vs m) (i, RetEv (Update v) tt) (SnapDef (insert vs v) m')
| SnapCallQuery i vs m m' :
    m i = None ->
    m' i = Some (existT _ _ Query) ->
    differ_pointwise m m' i ->
    SnapshotStep (SnapDef vs m) (i, CallEv Query) (SnapDef vs m')
| SnapRetQuery i vs m m' :
    m i = Some (existT _ _ Query) ->
    m' i = None ->
    differ_pointwise m m' i ->
    SnapshotStep (SnapDef vs m) (i, RetEv Query vs) (SnapDef vs m').

Program Definition snapshotSpec A : Spec (SnapshotSig A) := {|
  State := SnapshotState A;
  Step := SnapshotStep;
  Init := SnapDef emp (fun _ => None)
|}.

Admit Obligations.