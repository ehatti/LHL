From LHL.Core Require Import
  Program
  Specs.

From LHL.Util Require Import
  Util.


Variant SnapshotSig {A} : ESig :=
| Update (v : A) : SnapshotSig (set A).
Arguments SnapshotSig : clear implicits.

Variant SnapshotState {T A} :=
| SnapDef (vs : set A) (m : Name T -> option {B & SnapshotSig A B}).
Arguments SnapshotState : clear implicits.

Variant SnapshotStep {T A} : SnapshotState T A -> ThreadEvent T (SnapshotSig A) -> SnapshotState T A -> Prop :=
| SnapCallUpdate i v vs m m' :
    m i = None ->
    m' i = Some (existT _ _ (Update v)) ->
    differ_pointwise m m' i ->
    SnapshotStep (SnapDef vs m) (i, CallEv (Update v)) (SnapDef (insert v vs) m')
| SnapRetUpdate i v vs m m' :
    m i = Some (existT _ _ (Update v)) ->
    m' i = None ->
    differ_pointwise m m' i ->
    SnapshotStep (SnapDef vs m) (i, RetEv (Update v) vs) (SnapDef vs m').

Program Definition snapshotSpec {T A} : Spec T (SnapshotSig A) := {|
  State := SnapshotState T A;
  Step := SnapshotStep;
  Init := SnapDef emp (fun _ => None)
|}.

Admit Obligations.