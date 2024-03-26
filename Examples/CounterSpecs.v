From LHL.Core Require Import
    Program
    Specs.

Variant CounterSig : ESig :=
| Inc : CounterSig unit
| Get : CounterSig nat.

Variant AtomicCounterState :=
| CounterIdle (n : nat)
| CounterIncRunning (i : ThreadName) (n : nat)
| CounterGetRunning (i : ThreadName) (n : nat).

Variant AtomicCounterStep : AtomicCounterState -> ThreadEvent CounterSig -> AtomicCounterState -> Prop :=
| CounterCallInc i n : AtomicCounterStep (CounterIdle n) (i, CallEv Inc) (CounterIncRunning i n)
| CounterRetInc i n : AtomicCounterStep (CounterIncRunning i n) (i, RetEv Inc tt) (CounterIdle (S n))
| CounterCallGet i n : AtomicCounterStep (CounterIdle n) (i, CallEv Get) (CounterGetRunning i n)
| CounterRetGet i n : AtomicCounterStep (CounterGetRunning i n)  (i, RetEv Get n) (CounterIdle n).

Variant RacyCounterState :=
| CounterUB
| CounterDSt (s : AtomicCounterState).

Variant RacyCounterStep : RacyCounterState -> ThreadEvent CounterSig -> RacyCounterState -> Prop :=
| CounterIncUB i j n : RacyCounterStep (CounterDSt (CounterIncRunning i n)) (j, CallEv Inc) CounterUB
| CounterStepUB e : RacyCounterStep CounterUB e CounterUB
| CounterDSp st e st' : AtomicCounterStep st e st' -> RacyCounterStep (CounterDSt st) e (CounterDSt st').