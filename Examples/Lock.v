From LHL.Core Require Import
    Program
    Specs.

Variant LockSig : ESig :=
| Acq : LockSig unit
| Rel : LockSig unit.

Variant LockState :=
| LockIdle
| LockAcqRunning (i : ThreadName)
| LockOwned (i : ThreadName)
| LockRelRunning (i : ThreadName).

Variant LockStep : LockState -> ThreadEvent LockSig -> LockState -> Prop :=
| LockCallAcq i : LockStep LockIdle (i, CallEv Acq) (LockAcqRunning i)
| LockRetAcq i : LockStep (LockAcqRunning i) (i, RetEv Acq tt) (LockOwned i)
| LockCallRel i : LockStep (LockOwned i) (i, CallEv Rel) (LockRelRunning i)
| LockRetRel i : LockStep (LockRelRunning i) (i, RetEv Rel tt) LockIdle.

Definition lockSpec : Spec LockSig := {|
    State := LockState;
    Step := LockStep;
    Init := LockIdle
|}.

Definition OwnsLock i s :=
    s = LockAcqRunning i \/
    s = LockOwned i \/
    s = LockRelRunning i.