From LHL.Core Require Import
    Program
    Specs.

From LHL.Examples Require Import
    RacyCounter
    CounterSpecs
    Lock.

Definition atomicCounterSpec : Spec CounterSig := {|
    State := AtomicCounterState;
    Step := AtomicCounterStep;
    Init := CounterIdle 0
|}.

Definition Underlay := LockSig |+| CounterSig.

Definition inc : Prog Underlay unit :=
    _ <- InL Acq;
    _ <- InR Inc;
    _ <- InL Rel;
    Return tt.

Definition get : Prog Underlay nat :=
    _ <- InL Acq;
    n <- InR Get;
    _ <- InL Rel;
    Return n.

Definition atomicCounterImpl : Impl (LockSig |+| CounterSig) CounterSig :=
    fun _ m => match m with
    | Inc => inc
    | Get => get
    end.

