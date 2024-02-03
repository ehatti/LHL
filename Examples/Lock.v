From LHL.Core Require Import
    Program
    Specs.

Variant LockSig : ESig :=
| Acq : LockSig unit
| Rel : LockSig unit.

Variant LockState :=
| LockIdle
| LockAcqRunning (i : ThreadName)
| LockWaitForRel (i : ThreadName)
| LockRelRunning (i : ThreadName).

Variant LockStep : LockState -> ThreadEvent LockSig -> LockState -> Prop :=
| LockCallAcq i : LockStep LockIdle (i, CallEv Acq) (LockAcqRunning i)
| LockRetAcq i : LockStep (LockAcqRunning i) (i, RetEv Acq) (LockWaitForRel i)
| LockCallRel i : LockStep (LockWaitForRel i) (i, CallEv Rel) (LockRelRunning i)
| LockRetRel i : LockStep (LockRelRunning i) (i, RetEv Rel) LockIdle.

Definition lockSpec : Spec LockSig := {|
    State := LockState;
    Step := LockStep;
    Init := LockIdle
|}.