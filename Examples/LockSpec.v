From LHL.Core Require Import
  Program
  Specs.

From Coq Require Import
  Program.Equality.

Variant LockSig : ESig :=
| Acq : LockSig unit
| Rel : LockSig unit.

Variant LockState :=
| LockDef (owner : option ThreadName) (m : option (LockSig unit))
| LockUB.

Definition LockUnowned := LockDef None None.
Definition LockAcqRan i := LockDef (Some i) (Some Acq).
Definition LockRelRan i := LockDef (Some i) (Some Rel).
Definition LockOwned i := LockDef (Some i) None.

Variant LockStep : LockState -> ThreadEvent LockSig -> LockState -> Prop :=
| LockCallAcq i : LockStep LockUnowned (i, CallEv Acq) (LockAcqRan i)
| LockRetAcq i : LockStep (LockAcqRan i) (i, RetEv Acq tt) (LockOwned i)
| LockCallRel i : LockStep (LockOwned i) (i, CallEv Rel) (LockRelRan i)
| LockRetRel i : LockStep (LockRelRan i) (i, RetEv Rel tt) LockUnowned
| LockRaceAcq i : LockStep (LockAcqRan i) (i, CallEv Acq) LockUB
| LockRaceRel i : LockStep (LockRelRan i) (i, CallEv Rel) LockUB
| LockStepUB e : LockStep LockUB e LockUB.

Definition lockSpec : Spec LockSig := {|
  State := LockState;
  Step := LockStep;
  Init := LockUnowned
|}.

Definition OwnsLock i s :=
  match s with
  | LockDef (Some j) _ => i = j
  | _ => False
  end.

Definition owner s :=
  match s with
  | LockDef o _ => o
  | LockUB => None
  end.

Lemma owner_correct :
  forall s i, owner s = Some i <-> OwnsLock i s.
unfold owner, OwnsLock. intros.
split; intros.
destruct s; subst; easy.
destruct s. destruct owner0; subst; easy.
contradiction.
Qed.