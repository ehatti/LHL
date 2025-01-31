From LHL.Core Require Import
  Program
  Specs.

From LHL.Util Require Import
  TransUtil
  Tactics
  Util.

From LHL.Examples Require Import
  AtomicSpec.

Variant RegSig {A} : ESig :=
| Write (x : A) : RegSig unit
| Read : RegSig A.
Arguments RegSig : clear implicits.

Variant RegStep {T A} : A -> Name T * {R & prod (RegSig A R) R} -> A -> Prop :=
| RegRead i x : RegStep x (i, existT _ _ (Read, x)) x
| RegWrite i x y : RegStep x (i, existT _ _ (Write y, tt)) y.

Definition regSpec {T A} (init : A)
: AtomicSpec T (RegSig A) := {|
  AState := A;
  AStep := RegStep;
  AInit := init
|}.