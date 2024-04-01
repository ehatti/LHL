From LHL.Core Require Import
  Program
  Specs.

Variant CounterSig : ESig :=
| Inc : CounterSig unit
| Get : CounterSig nat.

Variant CounterState :=
| CounterIdle (n : nat)
| CounterIncRunning (i : ThreadName) (n : nat)
| CounterGetRunning (i : ThreadName) (n : nat).

Variant CounterStep : CounterState -> ThreadEvent CounterSig -> CounterState -> Prop :=
| CounterCallInc i n : CounterStep (CounterIdle n) (i, CallEv Inc) (CounterIncRunning i n)
| CounterRetInc i n : CounterStep (CounterIncRunning i n) (i, RetEv Inc tt) (CounterIdle (S n))
| CounterCallGet i n : CounterStep (CounterIdle n) (i, CallEv Get) (CounterGetRunning i n)
| CounterRetGet i n : CounterStep (CounterGetRunning i n)  (i, RetEv Get n) (CounterIdle n).

Definition counterSpec : Spec CounterSig := {|
  State := CounterState;
  Step := CounterStep;
  Init := CounterIdle 0
|}.