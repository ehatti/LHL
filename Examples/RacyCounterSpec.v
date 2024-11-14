From LHL.Core Require Import
  Program
  Specs.

From LHL.Examples Require Import
  AtomicCounterSpec.

Variant RacyCntState {T} :=
| RCntDef (s : CntState T)
| RCntUB (m : ActiveMap T CntSig).
Arguments RacyCntState : clear implicits.

Variant RacyCntStep {T} : RacyCntState T -> ThreadEvent T CntSig -> RacyCntState T -> Prop :=
| DefStep s e t :
  cntPend s = None ->
  CntStep s e t ->
  RacyCntStep (RCntDef s) e (RCntDef t)
| UBStep s i A (m : CntSig A) t :
  cntPend s <> None ->
  RacyCntStep (RCntDef s) (i, CallEv m) (RCntDef t).

Program Definition rcntSpec {T} : Spec T CntSig := {|
  State := RacyCntState T;
  Init := RCntDef acntSpec.(Init);
  Step := RacyCntStep
|}.

Next Obligation.
Admitted.