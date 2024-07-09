From LHL.Core Require Import
  Specs
  Traces
  Program.

From LHL.Util Require Import
  TransUtil
  Util.

Variant WkState {T E A} :=
| UB (m : ActiveMap T E)
| Def (v : A).
Arguments WkState : clear implicits.

Variant WkStep {T E} {V : Spec T E} : WkState T E V.(State) -> ThreadEvent T E -> WkState T E V.(State) -> Prop :=
| DefStep s e t :
    V.(Step) s e t ->
    WkStep (Def s) e (Def t)
| TrigUB s e :
    (forall t, ~V.(Step) s e t) ->
    WkStep (Def s) e (UB (fun _ => None))
| CallUB a a' i A (m : E A) :
    a i = None ->
    a' i = Some (existT _ _ m) ->
    WkStep (UB a) (i, CallEv m) (UB a')
| RetUB a a' i A (m : E A) v :
    a i = Some (existT _ _ m) ->
    a' i = None ->
    WkStep (UB a) (i, RetEv m v) (UB a').
Arguments WkStep {T E} V.

Program Definition wkSpec {T E} (V : Spec T E) : Spec T E := {|
  State := WkState T E V.(State);
  Step := WkStep V;
  Init := Def V.(Init)
|}.

Next Obligation.
