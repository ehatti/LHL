From Coq Require Import
    List
    Relations.

From LHL.Util Require Import
    ListUtil
    TransUtil.

From LHL.Core Require Import
    Program
    Specs.

Set Implicit Arguments.
Set Contextual Implicit.
Unset Strict Implicit.

(* Traces *)

Definition Trace (T : Type) : Type := list T.

Definition projOverEv {E F : ESig} (ev : @ThreadLEvent E F) : option (ThreadEvent F) := 
    match ev with
    | (i, OCallEv m) => Some (i, CallEv m)
    | (i, ORetEv n) => Some (i, RetEv n)
    | (_, UCallEv m) => None
    | (_, URetEv n) => None
    | (_, Silent) => None
    end.

Definition projUnderEv {E F : ESig} (ev : @ThreadLEvent E F) : option (ThreadEvent E) := 
    match ev with
    | (_, OCallEv m) => None
    | (_, ORetEv n) => None
    | (i, UCallEv m) => Some (i, CallEv m)
    | (i, URetEv n) => Some (i, RetEv n)
    | (_, Silent) => None
    end.

Notation projOver := (mapfilter projOverEv).
Notation projUnder := (mapfilter projUnderEv).

(* Implule Transition System *)

Inductive ThreadState {E : ESig} : Type :=
| Idle
| Cont {Ret} (p : Prog E Ret) 
| UCall {Ret A} (k : A -> Prog E Ret)
.

Definition ThreadsSt {E : ESig} : Type := ThreadName -> ThreadState (E := E).

Definition allIdle {E : ESig} : ThreadsSt (E := E) := fun n => Idle.

Definition ThreadStep {E F : ESig} 
    (M : Impl E F) (th : ThreadState) (e : LEvent) (th' : ThreadState) : Prop :=
        match e with 
        | @OCallEv _ _ R m => th = Idle /\ th' = Cont (M R m)
        | @ORetEv _ _ R n => th = Cont (Return n) /\ th' = Idle
        | @UCallEv _ _ A m => exists R (k : _ -> _ R), th = Cont (Bind m k) /\ th' = UCall (A := A) k
        | @URetEv _ _ A n =>  exists R (k : _ -> _ R), th = UCall k /\ th' = Cont (k n)
        | Silent => exists R (p : _ R), th = Cont (NoOp p) /\ th' = Cont p
        end.

Definition ThreadsStep E F (M : Impl E F)
  : ThreadsSt -> ThreadLEvent -> ThreadsSt -> Prop :=
  PointStep (ThreadStep (E := E) M).

Definition ThreadsSteps {E F} (M : Impl E F)
  : ThreadsSt -> Trace ThreadLEvent -> ThreadsSt -> Prop :=
  Steps (ThreadsStep M).

(* Trace Semantics *)

Definition IsTraceOfImpl {E F : ESig} (t : Trace ThreadLEvent) (M : Impl E F) : Prop :=
    exists thst, IsPathOf allIdle t thst (ThreadsSteps M).
    
Definition IsTraceOfSpec {E : ESig} (t : Trace (ThreadEvent E)) (spec : Spec E) : Prop := 
    exists st, IsPathOf spec.(Init) t st (Steps spec.(Step)).

Definition IsTraceOfLayer {E F : ESig} (t : Trace ThreadLEvent) (lay : @Layer E F) : Prop :=
    IsTraceOfSpec (projUnder t) lay.(USpec) /\ IsTraceOfImpl t lay.(LImpl).

Definition IsTraceOfOver {E F : ESig} (t : Trace (ThreadEvent F)) (lay : @Layer E F) : Prop :=
    exists t', t = projOver t' /\ IsTraceOfLayer t' lay.

(* Interactions *)

Definition InterState {E : ESig} {spec : Spec E} : Type := 
    (ThreadsSt (E := E)) * spec.(State).

Inductive InterStep {E F : ESig} {spec : Spec E} {impl : Impl E F} (i : ThreadName) :
    InterState -> ThreadLEvent -> InterState -> Prop  :=
    | IOCall ths st R m ths' :
        ths i = Idle -> 
        ths' i = Cont (impl R m) ->
        (forall j , j <> i -> ths' j = ths j) -> 
        InterStep i (ths, st) (i, OCallEv m) (ths', st)
    | IORet ths st R n ths' :
        ths i = Cont (Return n) ->
        ths' i = Idle -> 
        (forall j , j <> i -> ths' j = ths j) -> 
        InterStep i (ths, st) (i, ORetEv (Ret := R) n) (ths', st)
    | IUCall ths st A (m : E A) R k ths' st' : 
        ths i = Cont (Bind m k) ->
        ths' i = UCall (Ret := R) k ->
        spec.(Step) st (i, CallEv m) st' ->
        (forall j , j <> i -> ths' j = ths j) -> 
        InterStep i (ths, st) (i, UCallEv m) (ths', st')
    | IURet ths st A (n : A) R k ths' st' : 
        ths i = UCall (Ret := R) k ->
        ths' i = Cont (k n) -> 
        spec.(Step) st (i, RetEv n) st' -> 
        (forall j , j <> i -> ths' j = ths j) -> 
        InterStep i (ths, st) (i, URetEv n) (ths', st')
    | IUSilent ths st R (p : _ R) ths' :
        ths i = Cont (NoOp p) ->
        ths' i = Cont p -> 
        (forall j , j <> i -> ths' j = ths j) -> 
        InterStep i (ths, st) (i, Silent) (ths', st).

Definition InterSteps {E F : ESig} {spec : Spec E} {impl : Impl E F} : 
    InterState (spec := spec) -> Trace (ThreadLEvent (F := F)) -> InterState -> Prop := 
        Steps (fun thst ev thst' => exists i, InterStep (impl := impl) i thst ev thst').

Definition IsTraceOfInter {E F : ESig} (t : Trace (ThreadLEvent (F := F))) (lay : Layer E F) := 
    exists thst, IsPathOf (allIdle, lay.(USpec).(Init)) t thst (InterSteps (impl := lay.(LImpl))).

Definition IsTraceOfInterOv {E F : ESig} (t : Trace (ThreadEvent F)) (lay : @Layer E F) := 
    exists t', t = projOver t' /\ IsTraceOfInter t' lay.

Inductive InterUStep {E : ESig} {spec : Spec E} : 
    InterState -> InterState -> Prop :=
    | InterUCall ths st i A (m : E A) R k ths' st' : 
        ths i = Cont (Bind m k) ->
        ths' i = UCall (Ret := R) k ->
        spec.(Step) st (i, CallEv m) st' ->
        (forall j , j <> i -> ths' j = ths j) -> 
        InterUStep (ths, st) (ths', st')
    | InterURet ths st i A (n : A) R k ths' st' : 
        ths i = UCall (Ret := R) k ->
        ths' i = Cont (k n) -> 
        spec.(Step) st (i, RetEv n) st' -> 
        (forall j , j <> i -> ths' j = ths j) -> 
        InterUStep (ths, st) (ths', st')
    | InterUSilent ths st i R (p : _ R) ths' :
        ths i = Cont (NoOp p) ->
        ths' i = Cont p -> 
        (forall j , j <> i -> ths' j = ths j) -> 
        InterUStep (ths, st) (ths', st).

Definition InterUSteps {E : ESig} {spec : Spec E} : 
    InterState -> InterState -> Prop := 
    clos_refl_trans InterState (InterUStep (spec := spec)).

Inductive InterOStep {E F : ESig} {spec : Spec E} {impl : Impl E F} :
    InterState (spec := spec) -> ThreadLEvent (E := E) (F := F) -> InterState -> Prop  :=
    | InterOCall ths st i R m ths' :
        ths i = Idle -> 
        ths' i = Cont (impl R m) ->
        (forall j , j <> i -> ths' j = ths j) -> 
        InterOStep (ths, st) (i, OCallEv m) (ths', st)
    | InterORet ths st i R n ths' :
        ths i = Cont (Return n) ->
        ths' i = Idle -> 
        (forall j , j <> i -> ths' j = ths j) -> 
        InterOStep (ths, st) (i, ORetEv (Ret := R) n) (ths', st).

Definition overObj {E F : ESig} (lay : @Layer E F) : Spec F := 
    {|
        State := InterState (spec := lay.(USpec));
        Step thst ev thst'' := exists thst' ev', 
            InterUSteps thst thst' /\ projOverEv ev' = Some ev /\ InterOStep (impl := lay.(LImpl)) thst' ev' thst'';
        Init := (allIdle, lay.(USpec).(Init))
    |}.

(* Refinement *)

Definition specRefines {E : ESig} (spec : Spec E) (spec': Spec E) : Prop := 
    Incl (fun t => IsTraceOfSpec t spec) (fun t => IsTraceOfSpec t spec'). 

Definition layerRefines {E E' F} (lay : @Layer E F) (lay': @Layer E' F)  := 
   specRefines (overObj lay) (overObj lay').