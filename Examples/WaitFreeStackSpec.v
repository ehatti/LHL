From LHL.Core Require Import
  Program
  Specs
  Logic.

From LHL.Util Require Import
  Tactics
  TransUtil
  Util.

Variant StkRet {A} :=
| PASS (v : A)
| FAIL.
Arguments StkRet : clear implicits.

Variant WaitFreeStackSig {A} : ESig :=
| WFPush (v : A) : WaitFreeStackSig (StkRet unit)
| WFPop : WaitFreeStackSig (StkRet (option A)).
Arguments WaitFreeStackSig : clear implicits.

Record WaitFreeStackPend {T A} := MkWFSPend {
  StkRetTy : Type;
  StkName : Name T;
  StkCall : WaitFreeStackSig A StkRetTy
}.
Arguments WaitFreeStackPend : clear implicits.
Arguments MkWFSPend {T A StkRetTy}.

Definition WFSPend T A:=
  option (option (WaitFreeStackPend T A) * WaitFreeStackPend T A).

Notation NoPend :=
  (None : WFSPend _ _).
Notation PassPend i m :=
  (Some (None, MkWFSPend i m) : WFSPend _ _).
Notation FailPend j mf i mp :=
  (Some (Some (MkWFSPend j mf), MkWFSPend i mp)).

Variant WaitFreeStackState {T A} :=
| WaitFreeStackDef (vs : list A) (m : WFSPend T A).
Arguments WaitFreeStackState : clear implicits.

Variant WaitFreeStackStep {T A} : WaitFreeStackState T A -> ThreadEvent T (WaitFreeStackSig A) -> WaitFreeStackState T A -> Prop :=
| StackCall i R (m : _ R) vs :
    WaitFreeStackStep
      (WaitFreeStackDef vs NoPend)
      (i, CallEv m)
      (WaitFreeStackDef vs (PassPend i m))
| StackContendCall i j vs RO (mo : _ RO) RN (mn : _ RN) :
    i <> j ->
    WaitFreeStackStep
      (WaitFreeStackDef vs (PassPend i mo))
      (j, CallEv mn)
      (WaitFreeStackDef vs (FailPend j mn i mo))
| StackContendRet i j vs RO (mo : _ RO) RN (mn : _ (StkRet RN)) :
    i <> j ->
    WaitFreeStackStep
      (WaitFreeStackDef vs (FailPend j mn i mo))
      (j, RetEv mn FAIL)
      (WaitFreeStackDef vs (PassPend i mo))
| RetPush i v vs :
    WaitFreeStackStep
      (WaitFreeStackDef vs (PassPend i (WFPush v)))
      (i, RetEv (WFPush v) (PASS tt))
      (WaitFreeStackDef (v :: vs) NoPend)
| RetPopPass i v vs :
    WaitFreeStackStep
      (WaitFreeStackDef (v :: vs) (PassPend i WFPop))
      (i, RetEv WFPop (PASS (Some v)))
      (WaitFreeStackDef vs NoPend)
| RetPopFail i :
    WaitFreeStackStep
      (WaitFreeStackDef nil (PassPend i WFPop))
      (i, RetEv WFPop (PASS None))
      (WaitFreeStackDef nil NoPend).

Program Definition wfStackSpec {T A} : Spec T (WaitFreeStackSig A) := {|
  State := WaitFreeStackState T A;
  Step := WaitFreeStackStep;
  Init := WaitFreeStackDef nil NoPend
|}.

Admit Obligations.