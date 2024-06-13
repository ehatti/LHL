From LHL.Core Require Import
  Program
  Specs.

From Coq Require Import
  Program.Equality.

Variant LockSig : ESig :=
| Acq : LockSig unit
| Rel : LockSig unit.

Variant LockState :=
| LockIdle
| LockAcqRunning (i : ThreadName)
| LockOwned (i : ThreadName)
| LockRelRunning (i : ThreadName)
| LockUB.

Variant LockStep : LockState -> ThreadEvent LockSig -> LockState -> Prop :=
| LockCallAcq i : LockStep LockIdle (i, CallEv Acq) (LockAcqRunning i)
| LockRetAcq i : LockStep (LockAcqRunning i) (i, RetEv Acq tt) (LockOwned i)
| LockCallRel i : LockStep (LockOwned i) (i, CallEv Rel) (LockRelRunning i)
| LockRetRel i : LockStep (LockRelRunning i) (i, RetEv Rel tt) LockIdle
| LockTwoAcq i : LockStep (LockAcqRunning i) (i, CallEv Acq) LockUB
| LockTwoRel i : LockStep (LockRelRunning i) (i, CallEv Rel) LockUB
| LockDoUB e : LockStep LockUB e LockUB.

Definition lockSpec : Spec LockSig := {|
  State := LockState;
  Step := LockStep;
  Init := LockIdle
|}.

Definition OwnsLock i s :=
  s = LockAcqRunning i \/
  s = LockOwned i \/
  s = LockRelRunning i.

Definition owner s :=
  match s with
  | LockAcqRunning i => Some i
  | LockOwned i => Some i
  | LockRelRunning i => Some i
  | _ => None
  end.

Lemma owner_correct :
  forall s i, owner s = Some i <-> OwnsLock i s.
intros.
split; intros.
destruct s; simpl in *; try congruence.
dependent destruction H. left. easy.
dependent destruction H. right. left. easy.
dependent destruction H. right. right. easy.
destruct H.
subst. easy.
destruct H.
subst. easy.
subst. easy.
Qed.