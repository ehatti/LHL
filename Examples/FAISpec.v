From LHL.Core Require Import
  Specs
  Traces
  Program.

From LHL.Util Require Import
  Util.

Variant FAISig : ESig :=
| FAI : FAISig nat.

Variant FAIState :=
| FAICalled (i : ThreadName) (n : nat)
| FAIIdle (n : nat).

Variant FAIStep : FAIState -> ThreadEvent FAISig -> FAIState -> Prop :=
| FAICall i n : FAIStep (FAIIdle n) (i, CallEv FAI) (FAICalled i n)
| FAIRet i n : FAIStep (FAICalled i n) (i, RetEv FAI n) (FAIIdle (S n)).

Definition faiSpec : Spec FAISig := {|
  State := FAIState;
  Step := FAIStep;
  Init := FAIIdle 0
|}.