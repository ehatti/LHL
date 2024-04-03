From LHL.Core Require Import
  Program
  Specs.

Variant CounterSig : ESig :=
| Inc : CounterSig unit
| Get : CounterSig nat.

Variant CounterState :=
| CounterIdle (n : nat)
| CounterGetCalled (i : ThreadName) (n : nat)
| CounterIncCalled (i : ThreadName) (n : nat)
| CounterUB.

Variant CounterStep : CounterState -> ThreadEvent CounterSig -> CounterState -> Prop :=
| CounterCallInc i n :
  CounterStep (CounterIdle n) (i, CallEv Inc) (CounterIncCalled i n)
| CounterRetInc i n :
  CounterStep (CounterIncCalled i n) (i, RetEv Inc tt) (CounterIdle (S n))
| CounterCallGet i n :
  CounterStep (CounterIdle n) (i, CallEv Get) (CounterGetCalled i n)
| CounterRetGet i n :
  CounterStep (CounterGetCalled i n) (i, RetEv Get n) (CounterIdle n)
| CounterRaceInc i j n :
  CounterStep (CounterIncCalled i n) (j, CallEv Inc) CounterUB
| CounterStepUB e :
  CounterStep CounterUB e CounterUB.

Definition counterSpec : Spec CounterSig := {|
  State := CounterState;
  Step := CounterStep;
  Init := CounterIdle 0
|}.