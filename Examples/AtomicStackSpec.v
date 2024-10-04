From LHL.Core Require Import
  Program
  Specs
  Logic.

From LHL.Util Require Import
  Tactics
  TransUtil
  Util.

Variant AtomicStackSig {A} : ESig :=
| Push (v : A) : AtomicStackSig unit
| Pop : AtomicStackSig (option A).
Arguments AtomicStackSig : clear implicits.

Record AtomicStackPend {T A} := MkStkPend {
  StkRetTy : Type;
  StkName : Name T;
  StkCall : AtomicStackSig A StkRetTy
}.
Arguments AtomicStackPend : clear implicits.
Arguments MkStkPend {T A StkRetTy}.

Variant AtomicStackState {T A} :=
| AtomicStackDef (vs : list A) (m : option (AtomicStackPend T A)).
Arguments AtomicStackState : clear implicits.

Variant AtomicStackStep {T A} : AtomicStackState T A -> ThreadEvent T (AtomicStackSig A) -> AtomicStackState T A -> Prop :=
| AtomicStackCall i R (m : _ R) vs : AtomicStackStep
  (AtomicStackDef vs None)
  (i, CallEv m)
  (AtomicStackDef vs (Some (MkStkPend i m)))
| RetPush i v vs : AtomicStackStep
    (AtomicStackDef vs (Some (MkStkPend i (Push v))))
    (i, RetEv (Push v) tt)
    (AtomicStackDef (v :: vs) None)
| RetPopPass i v vs : AtomicStackStep
    (AtomicStackDef (v :: vs) (Some (MkStkPend i Pop)))
    (i, RetEv Pop (Some v))
    (AtomicStackDef vs None)
| RetPopFail i : AtomicStackStep
    (AtomicStackDef nil (Some (MkStkPend i Pop)))
    (i, RetEv Pop None)
    (AtomicStackDef nil None).

Program Definition atomicStackSpec {T A} : Spec T (AtomicStackSig A) := {|
  State := AtomicStackState T A;
  Step := AtomicStackStep;
  Init := AtomicStackDef nil None
|}.

Admit Obligations.