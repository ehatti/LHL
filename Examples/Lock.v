From LHL.Core Require Import
    Program
    Specs.

Variant LockSig : ESig :=
| Acq : LockSig unit
| Rel : LockSig unit.

Variant LockState :=
| LockUnowned
| LockAcqRunning (i : ThreadName)
| LockOwned (i : ThreadName)
| LockRelRunning (i : ThreadName).

Variant LockStep : LockState -> ThreadEvent LockSig -> LockState -> Prop :=
| LockCallAcq i : LockStep LockUnowned (i, CallEv Acq) (LockAcqRunning i)
| LockRetAcq i : LockStep (LockAcqRunning i) (i, RetEv Acq tt) (LockOwned i)
| LockCallRel i : LockStep (LockOwned i) (i, CallEv Rel) (LockRelRunning i)
| LockRetRel i : LockStep (LockRelRunning i) (i, RetEv Rel tt) LockUnowned.

Definition lockSpec : Spec LockSig := {|
    State := LockState;
    Step := LockStep;
    Init := LockUnowned
|}.