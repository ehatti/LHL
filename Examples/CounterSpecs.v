From LHL.Core Require Import
    Program
    Specs.

Variant CounterSig : ESig :=
| Inc : CounterSig unit
| Get : CounterSig nat.

Variant AtomicCounterState :=
| CounterIdle (n : nat)
| CounterIncRunning (n : nat) (i : ThreadName)
| CounterGetRunning (n : nat) (i : ThreadName).

Variant AtomicCounterStep : AtomicCounterState -> ThreadEvent CounterSig -> AtomicCounterState -> Prop :=
| CounterCallInc n i : AtomicCounterStep (CounterIdle n) (i, CallEv Inc) (CounterIncRunning n i)
| CounterRetInc i n : AtomicCounterStep (CounterIncRunning n i) (i, RetEv Inc) (CounterIdle (S n))
| CounterCallGet n i : AtomicCounterStep (CounterIdle n) (i, CallEv Get) (CounterGetRunning n i)
| CounterRetGet i n : AtomicCounterStep (CounterGetRunning n i)  (i, RetEv (n, Get)) (CounterIdle n).

Variant RacyCounterState :=
| CounterUB
| CounterDSt (s : AtomicCounterState).

Variant RacyCounterStep : RacyCounterState -> ThreadEvent CounterSig -> RacyCounterState -> Prop :=
| CounterIncUB i j n : RacyCounterStep (CounterDSt (CounterIncRunning n i)) (j, CallEv Inc) CounterUB
| CounterDSp st e st' : AtomicCounterStep st e st' -> RacyCounterStep (CounterDSt st) e (CounterDSt st').