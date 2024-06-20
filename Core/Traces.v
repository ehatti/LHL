From Coq Require Import
  List
  Relations
  Init.Nat
  Program.Equality
  Logic.FunctionalExtensionality.

From LHL.Util Require Import
  Util
  ListUtil
  TransUtil
  Tactics.

From LHL.Core Require Import
  Program
  Specs
  Eutt.

(* Traces *)

Definition Trace (T : Type) : Type := list T.

Definition PrefixOf {T} (ρ σ : Trace T) : Prop :=
  exists τ, σ = app ρ τ.

Definition projAgentEv {T A} i (ev : T * A) : option (T * A) :=
  if eqb (fst ev) i then
    Some ev
  else
    None.

Definition projOverEv {T E F} (ev : ThreadLEvent T E F) : option (ThreadEvent T F) := 
  match ev with
  | (i, OEvent ev) => Some (i, ev)
  | _ => None
  end.

Definition projUnderEv {T E F} (ev : ThreadLEvent T E F) : option (T * option (Event E)) := 
  match ev with
  | (i, UEvent ev) => Some (i, ev)
  | _ => None
  end.

Fixpoint projUnderThr {T E F} (p : Trace (ThreadLEvent T E F)) : Trace (ThreadEvent T E) :=
  match p with
  | nil => nil
  | cons (i, UEvent (Some ev)) q => cons (i, ev) (projUnderThr q)
  | cons _ q => projUnderThr q
  end.

Fixpoint projSilent {T E} (p : Trace (T * option (Event E))) : Trace (ThreadEvent T E) :=
  match p with
  | nil => nil
  | cons (i, None) q => projSilent q
  | cons (i, Some e) q => cons (i, e) (projSilent q)
  end.

Definition liftUEv {E F} (ev : @Event E) : @LEvent E F :=
  UEvent (Some ev).

Definition liftOEv {E F} (ev : @Event F) : @LEvent E F :=
  OEvent ev.

Notation projOver := (mapfilter projOverEv).
Notation projUnder := (mapfilter projUnderEv).
Definition projAgent {T A} i : 
  Trace (T * A) -> Trace (T * A) := 
    (mapfilter (projAgentEv i)).
Notation liftU := (map liftUEv).
Notation liftO := (map liftOEv).

(* Implementation Transition System *)

Inductive ThreadState {E F : ESig} : Type :=
| Idle
| Cont {A} (m : F A) (p : Prog E A) 
| UCall {A B} (om : F B) (um : E A) (k : A -> Prog E B).
Arguments ThreadState : clear implicits.

Definition ThreadsSt T E F : Type := T -> ThreadState E F.

Definition updt_thst T E F := 
  @updt_istate T (ThreadState E F) eqb.

Definition allIdle {T E F} : ThreadsSt T E F := fun n => Idle.

Variant OverThreadStep {E F : ESig} (M : Impl E F) :
  ThreadState E F -> Event F -> ThreadState E F -> Prop :=
| OCallThreadStep th th' A (m : F A) :
  th = Idle ->
  th' = Cont m (M _ m) ->
  OverThreadStep M th (CallEv m) th'
| ORetThreadStep th th' A (m : F A) v :
  th = Cont m (Return v) ->
  th' = Idle ->
  OverThreadStep M th (RetEv m v) th'.

Variant UnderThreadStep {E F : ESig} :
  ThreadState E F -> option (Event E) -> ThreadState E F -> Prop :=
| UCallThreadStep A B th th' (um : E A) (om : F B) k :
  th = Cont om (Bind um k) ->
  th' = UCall om um k ->
  UnderThreadStep th (Some (CallEv um)) th'
| URetThreadStep A B th th' (um : E A) (om : F B) k v :
  th = UCall om um k ->
  th' = Cont om (k v) ->
  UnderThreadStep th (Some (RetEv um v)) th'
| USilentThreadStep A th th' om (p : Prog E A) :
  th = Cont om (NoOp p) ->
  th' = Cont om p ->
  UnderThreadStep th None th'.

Definition ThreadStep {E F : ESig} (M : Impl E F) (s : ThreadState E F) (e : LEvent E F) (t : ThreadState E F) :=
  match e with
  | UEvent e => UnderThreadStep s e t
  | OEvent e => OverThreadStep M s e t
  end.

Definition ThreadsStep {T E F} (M : Impl E F)
  : ThreadsSt T E F -> ThreadLEvent T E F -> ThreadsSt T E F -> Prop :=
  PointStep (ThreadStep (E := E) M).

(* Trace Semantics *)

Definition IsTraceOfImpl {T E F} (t : Trace (ThreadLEvent T E F)) (M : Impl E F) : Prop :=
  exists thst, Steps (ThreadsStep M) allIdle t thst.
  
Definition IsTraceOfSpec {T E} (t : Trace (ThreadEvent T E)) (spec : Spec T E) : Prop :=
  exists st, Steps spec.(Step) spec.(Init) t st.

Definition IsTraceOfSpecBwd {T E} (t : bwd_list (ThreadEvent T E)) (spec : Spec T E) : Prop :=
  exists st, BwdSteps spec.(Step) spec.(Init) t st.

(* Interactions *)

Definition InterState {T E} F (spec : Spec T E) : Type :=
  ThreadsSt T E F * spec.(State).

Definition StateStep {T E F} {spec : Spec T E} (s : State spec) (ev : ThreadLEvent T E F) (t : State spec) :=
  match snd ev with
  | UEvent (Some e) => spec.(Step) s (fst ev, e) t
  | _ => s = t
  end.

Definition InterStep {T E F} {spec : Spec T E} (impl : Impl E F)
  (s : InterState F spec)
  (ev : ThreadLEvent T E F)
  (t : InterState F spec) :=
  ThreadsStep impl (fst s) ev (fst t) /\
  StateStep (snd s) ev (snd t).

Definition InterUStep {T E F} {spec : Spec T E} (i : T)
  (s : InterState F spec)
  (ev : option (Event E))
  (t : InterState F spec) :=
  PointStep UnderThreadStep (fst s) (i, ev) (fst t) /\
  match ev with
  | Some ev => spec.(Step) (snd s) (i, ev) (snd t)
  | None => snd s = snd t
  end.

Definition InterOStep {T E F} (impl : Impl E F) (i : T)
  (s : ThreadsSt T E F)
  (ev : Event F)
  (t : ThreadsSt T E F) :=
  PointStep (OverThreadStep impl) s (i, ev) t.

Definition InterUSteps {T E} F (spec : Spec T E) :
  InterState F spec -> Trace (T * option (Event E)) -> InterState F spec -> Prop := 
  Steps (fun s ev t => InterUStep (fst ev) s (snd ev) t).

Definition InterOSteps {T E} F (impl : Impl E F) : 
  ThreadsSt T E F -> Trace (ThreadEvent T F) -> ThreadsSt T E F -> Prop := 
  Steps (fun s ev t => InterOStep impl (fst ev) s (snd ev) t).

Definition InterSteps {T E F} {spec : Spec T E} (impl : Impl E F) :=
  Steps (InterStep (spec:=spec) impl).

Definition overObj {T E F} (lay : Layer T E F) : Spec T F := 
  {|
    State := InterState F lay.(USpec);
    Step thst ev thst'' :=
      exists ths',
        InterOStep lay.(LImpl) (fst ev) (fst thst) (snd ev) ths' /\
        exists p,
          InterUSteps F lay.(USpec) (ths', snd thst) p thst'';
    Init := (allIdle, lay.(USpec).(Init))
  |}.

(* Refinement *)

Definition specRefines {T E} (spec : Spec T E) (spec': Spec T E) : Prop := 
  Incl (fun t => IsTraceOfSpec t spec) (fun t => IsTraceOfSpec t spec'). 

Definition layerRefines {T E E' F} (lay : Layer T E F) (lay': Layer T E' F)  := 
  specRefines (overObj lay) (overObj lay').