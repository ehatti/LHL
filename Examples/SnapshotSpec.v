From LHL.Core Require Import
  Program
  Specs.

From LHL.Util Require Import
  TransUtil
  Tactics
  Util.

Variant SnapSig {A} : ESig :=
| WriteSnap (v : A) : SnapSig (option (set A)).
Arguments SnapSig : clear implicits.

Variant SnapState {T A} :=
| SnapDef (vs : set A) (m : Name T -> option A) (c : Name T -> bool).
Arguments SnapState : clear implicits.

Variant SnapStep {T A} : SnapState T A -> ThreadEvent T (SnapSig A) -> SnapState T A -> Prop :=
| SnapCall i v vs m m' c :
    m i = None ->
    m' i = Some v ->
    differ_pointwise m m' i ->
    SnapStep
      (SnapDef vs m c)
      (i, CallEv (WriteSnap v))
      (SnapDef (insert v vs) m' c)
| SnapRetPass i v vs m m' c c' :
    c i = false ->
    c' i = true ->
    differ_pointwise c c' i ->
    m i = Some v ->
    m' i = None ->
    differ_pointwise m m' i ->
    SnapStep
      (SnapDef vs m c)
      (i, RetEv (WriteSnap v) (Some vs))
      (SnapDef vs m' c')
| SnapRetFail i v vs m m' c :
    c i = true ->
    m i = Some v ->
    m' i = None ->
    differ_pointwise m m' i ->
    SnapStep
      (SnapDef vs m c)
      (i, RetEv (WriteSnap v) None)
      (SnapDef vs m' c).

Program Definition snapSpec {T A} : Spec T (SnapSig A) := {|
  State := SnapState T A;
  Step := SnapStep;
  Init := SnapDef emp (fun _ => None) (fun _ => false)
|}.

Next Obligation.
Admitted.