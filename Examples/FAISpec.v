From LHL.Core Require Import
  Specs
  Traces
  Program.

Variant FAISig : ESig :=
| FAI : FAISig nat.

Definition FAIState : Type := nat * option ThreadName.
Definition FAIIdle n : FAIState := (n, None).
Definition FAIRan i n : FAIState := (n, Some i).

Variant FAIStep : FAIState -> ThreadEvent FAISig -> FAIState -> Prop :=
| FAICall i n : FAIStep (FAIIdle n) (i, CallEv FAI) (FAIRan i n)
| FAIRet i n : FAIStep (FAIRan i n) (i, RetEv FAI n) (FAIIdle (S n)).

Program Definition faiSpec : Spec FAISig := {|
  State := FAIState;
  Step := FAIStep;
  Init := FAIIdle 0
|}.

Admit Obligations.