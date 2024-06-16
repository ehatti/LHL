From LHL.Core Require Import
  Program
  Specs.

Variant CounterSig : ESig :=
| Inc : CounterSig unit
| Get : CounterSig nat.

Record CounterPend := MkCntPend {
  CntRetTy : Type;
  CntName : ThreadName;
  CntCall : CounterSig CntRetTy
}.

Variant CounterState :=
| CounterDef (n : nat) (m : option CounterPend)
| CounterUB.

Definition CounterIdle (n : nat) :=
  CounterDef n None.
Definition CounterIncRan (i n : nat) :=
  CounterDef n (Some (MkCntPend _ i Inc)).
Definition CounterGetRan (i n : nat) :=
  CounterDef n (Some (MkCntPend _ i Get)).

Variant CounterStep : CounterState -> ThreadEvent CounterSig -> CounterState -> Prop :=
| CntInvInc i n :
    CounterStep (CounterIdle n) (i, CallEv Inc) (CounterIncRan i n)
| CntRetInc i n :
    CounterStep (CounterIncRan i n) (i, RetEv Inc tt) (CounterIdle (S n))
| CntInvGet i n :
    CounterStep (CounterIdle n) (i, CallEv Get) (CounterGetRan i n)
| CntRetGet i n :
    CounterStep (CounterGetRan i n) (i, RetEv Get n) (CounterIdle n)
| CntRaceInc i n :
    CounterStep (CounterIncRan i n) (i, CallEv Inc) CounterUB
| CntStepUB e :
    CounterStep CounterUB e CounterUB.

Definition counterSpec : Spec CounterSig := {|
  State := CounterState;
  Step := CounterStep;
  Init := CounterIdle 0
|}.