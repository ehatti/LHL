From LHL.Core Require Import
  Specs
  Traces
  Program.

From LHL.Util Require Import
  Util.

Variant YieldSig : ESig :=
| Yield : YieldSig unit.

Variant YieldStatus :=
| YieldIdle
| YieldGiving
| YieldReceiving.

Definition YieldState :=
  ThreadName -> YieldStatus.

Variant YieldStep : YieldState -> ThreadEvent YieldSig -> YieldState -> Prop :=
| YieldCall (s t : YieldState) i :
    s i = YieldIdle ->
    t i = YieldGiving ->
    (forall j, i <> j ->
      s j = YieldGiving ->
      t j = YieldReceiving) ->
    (forall j, i <> j ->
      s j = YieldReceiving \/ s j = YieldIdle ->
      s j = t j) ->
    YieldStep s (i, CallEv Yield) t
| YieldRet (s t : YieldState) i :
    s i = YieldReceiving ->
    t i = YieldIdle ->
    differ_pointwise s t i ->
    YieldStep s (i, RetEv Yield tt) t.

Program Definition yieldSpec : Spec YieldSig := {|
  State := YieldState;
  Step := YieldStep;
  Init := fun _ => YieldIdle
|}.

Admit Obligations.