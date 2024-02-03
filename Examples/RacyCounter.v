From LHL.Core Require Import
    Program
    Specs.

From LHL.Examples Require Import
    CounterSpecs.

Definition racyCounterSpec : Spec CounterSig := {|
    State := RacyCounterState;
    Step := RacyCounterStep;
    Init := CounterDSt (CounterIdle 0)
|}.