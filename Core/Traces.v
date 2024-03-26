From Coq Require Import
    List
    Relations
    Init.Nat.

From LHL.Util Require Import
    Util
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

Definition PrefixOf {T} (ρ σ : Trace T) : Prop :=
    exists τ, σ = app ρ τ.

Definition projAgentEv {A} i (ev : nat * A) : option (nat * A) :=
    if eqb (fst ev) i then
        Some ev
    else
        None.

Definition projOverEv {E F : ESig} (ev : @ThreadLEvent E F) : option (ThreadEvent F) := 
    match ev with
    | (i, OCallEv m) => Some (i, CallEv m)
    | (i, ORetEv m n) => Some (i, RetEv m n)
    | (_, UCallEv _) => None
    | (_, URetEv _ _) => None
    | (_, Silent) => None
    end.

Definition projUnderEv {E F : ESig} (ev : @ThreadLEvent E F) : option (ThreadEvent E) := 
    match ev with
    | (_, OCallEv _) => None
    | (_, ORetEv _ _) => None
    | (i, UCallEv m) => Some (i, CallEv m)
    | (i, URetEv m n) => Some (i, RetEv m n)
    | (_, Silent) => None
    end.

Definition liftUEv {E F} (ev : @Event E) : @LEvent E F :=
    match ev with
    | CallEv m => UCallEv m
    | RetEv m v => URetEv m v
    end.

Definition liftOEv {E F} (ev : @Event F) : @LEvent E F :=
    match ev with
    | CallEv m => OCallEv m
    | RetEv m v => ORetEv m v
    end.

Notation projOver := (mapfilter projOverEv).
Notation projUnder := (mapfilter projUnderEv).
Definition projAgent {A} i : 
    Trace (ThreadName * A) -> Trace (ThreadName * A) := 
        (mapfilter (projAgentEv i)).
Notation liftU := (map liftUEv).
Notation liftO := (map liftOEv).

(* Implementation Transition System *)

Inductive ThreadState {E F : ESig} : Type :=
| Idle
| Cont {Ret} (m : F Ret) (p : Prog E Ret) 
| UCall {Ret A} (m : F Ret) (k : A -> Prog E Ret)
.

Definition ThreadsSt {E F : ESig} : Type := ThreadName -> ThreadState (E := E) (F := F).

Definition updt_thst {E F : ESig} := 
    updt_istate (A := ThreadName) (State :=ThreadState (E := E) (F := F))  (eqA := eqb).

Definition allIdle {E F : ESig} : ThreadsSt (E := E) (F := F) := fun n => Idle.

Definition ThreadStep {E F : ESig}
    (M : Impl E F) (th : ThreadState) (e : LEvent E F) (th' : ThreadState) : Prop :=
        match e with 
        | @OCallEv _ _ R m => th = Idle /\ th' = Cont m (M R m)
        | @ORetEv _ _ R m n => th = Cont m (Return n) /\ th' = Idle
        | @UCallEv _ _ A m => exists R m' (k : _ -> _ R), th = Cont m' (Bind m k) /\ th' = UCall m' (A := A) k
        | @URetEv _ _ A _ n =>  exists R m (k : _ -> _ R), th = UCall m k /\ th' = Cont m (k n)
        | Silent => exists R m (p : _ R), th = Cont m (NoOp p) /\ th' = Cont m p
        end.

Definition ThreadsStep E F (M : Impl E F)
  : ThreadsSt -> ThreadLEvent E F -> ThreadsSt -> Prop :=
  PointStep (ThreadStep (E := E) M).

Definition ThreadsSteps {E F} (M : Impl E F)
  : ThreadsSt -> Trace (ThreadLEvent E F) -> ThreadsSt -> Prop :=
  Steps (ThreadsStep M).

(* Trace Semantics *)

Definition IsTraceOfImpl {E F : ESig} (t : Trace (ThreadLEvent E F)) (M : Impl E F) : Prop :=
    exists thst, IsPathOf allIdle t thst (ThreadsSteps M).
    
Definition IsTraceOfSpec {E : ESig} (t : Trace (ThreadEvent E)) (spec : Spec E) : Prop := 
    exists st, IsPathOf spec.(Init) t st (Steps spec.(Step)).

Definition IsTraceOfLayer {E F : ESig} (t : Trace (ThreadLEvent E F)) (lay : @Layer E F) : Prop :=
    IsTraceOfSpec (projUnder t) lay.(USpec) /\ IsTraceOfImpl t lay.(LImpl).

Definition IsTraceOfOver {E F : ESig} (t : Trace (ThreadEvent F)) (lay : @Layer E F) : Prop :=
    exists t', t = projOver t' /\ IsTraceOfLayer t' lay.

(* Interactions *)

Definition InterState {E F : ESig} {spec : Spec E} : Type :=
    (ThreadsSt (E := E) (F := F)) * spec.(State).

Definition updThs {A} (ths : ThreadName -> A) i (st : A) : ThreadName -> A :=
    fun j =>
        if eqb i j then
            st
        else
            ths j.

Lemma eqbEql {i} : eqb i i = true.
induction i.
easy.
simpl.
easy.
Qed.

Lemma updThsEql {A ths i st} : @updThs A ths i st i = st.
unfold updThs.
rewrite eqbEql.
easy.
Qed.

Inductive InterStep {E F : ESig} {spec : Spec E} {impl : Impl E F} (i : ThreadName) :
    InterState -> ThreadLEvent E F -> InterState -> Prop :=
    | IOCall ths st R m :
        ths i = Idle ->
        InterStep i (ths, st) (i, OCallEv m) (updThs ths i (Cont m (impl R m)), st)
    | IORet ths st R m n :
        ths i = Cont m (Return n) ->
        InterStep i (ths, st) (i, ORetEv (Ret := R) m n) (updThs ths i Idle, st)
    | IUCall ths st A (m : E A) R (m' : F R) k st' :
        ths i = Cont m' (Bind m k) ->
        spec.(Step) st (i, CallEv m) st' ->
        InterStep i (ths, st) (i, UCallEv m) (updThs ths i (UCall m' k), st')
    | IURet ths st A m (n : A) R m' k st' : 
        ths i = UCall (Ret := R) m' k ->
        spec.(Step) st (i, RetEv m n) st' -> 
        InterStep i (ths, st) (i, URetEv m n) (updThs ths i (Cont m' (k n)), st')
    | IUSilent ths st R m (p : _ R) :
        ths i = Cont m (NoOp p) ->
        InterStep i (ths, st) (i, Silent) (updThs ths i (Cont m p), st).

Definition ImplSteps i {E F : ESig} {spec : Spec E} {impl : Impl E F} : 
    InterState (spec := spec) -> Trace (ThreadLEvent E F) -> InterState -> Prop := 
        Steps (fun thst ev thst' => InterStep (impl := impl) i thst ev thst').

Definition InterSteps {E F : ESig} {spec : Spec E} {impl : Impl E F} : 
    InterState (spec := spec) -> Trace (ThreadLEvent E F) -> InterState -> Prop := 
        Steps (fun thst ev thst' => exists i, InterStep (impl := impl) i thst ev thst').

Definition IsTraceOfInter {E F : ESig} (t : Trace (ThreadLEvent E F)) (lay : Layer E F) := 
    exists thst, IsPathOf (allIdle, lay.(USpec).(Init)) t thst (InterSteps (impl := lay.(LImpl))).

Definition IsTraceOfInterOv {E F : ESig} (t : Trace (ThreadEvent F)) (lay : @Layer E F) := 
    exists t', t = projOver t' /\ IsTraceOfInter t' lay.

Inductive InterUStep {E F : ESig} {spec : Spec E} : 
    InterState (F := F) -> InterState -> Prop :=
    | InterUCall ths st i A (m : E A) R m' k ths' st' : 
        ths i = Cont m' (Bind m k) ->
        ths' i = UCall m' (Ret := R) k ->
        spec.(Step) st (i, CallEv m) st' ->
        differ_pointwise ths ths' i -> 
        InterUStep (ths, st) (ths', st')
    | InterURet ths st i A m (n : A) R m' k ths' st' : 
        ths i = UCall (Ret := R) m' k ->
        ths' i = Cont m' (k n) -> 
        spec.(Step) st (i, RetEv m n) st' -> 
        differ_pointwise ths ths' i -> 
        InterUStep (ths, st) (ths', st')
    | InterUSilent ths st i R m (p : _ R) ths' :
        ths i = Cont m (NoOp p) ->
        ths' i = Cont m p -> 
        differ_pointwise ths ths' i -> 
        InterUStep (ths, st) (ths', st).

Definition InterUSteps {E F : ESig} {spec : Spec E} : 
    InterState (F := F) -> InterState -> Prop := 
    clos_refl_trans InterState (InterUStep (spec := spec)).

Inductive InterOStep {E F : ESig} {spec : Spec E} {impl : Impl E F} :
    InterState (spec := spec) -> ThreadLEvent E F -> InterState -> Prop  :=
    | InterOCall ths st i R m ths' :
        ths i = Idle -> 
        ths' i = Cont m (impl R m) ->
        differ_pointwise ths ths' i -> 
        InterOStep (ths, st) (i, OCallEv m) (ths', st)
    | InterORet ths st i R m n ths' :
        ths i = Cont m (Return n) ->
        ths' i = Idle -> 
        differ_pointwise ths ths' i -> 
        InterOStep (ths, st) (i, ORetEv (Ret := R) m n) (ths', st).

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