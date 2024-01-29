From Coq Require Import
    List.

From LHL.Util Require Import
    ListUtil
    TransUtil.

From LHL.Core Require Import
    Program.

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
    end.

Definition projUnderEv {E F : ESig} (ev : @ThreadLEvent E F) : option (ThreadEvent E) := 
    match ev with
    | (_, OCallEv m) => None
    | (_, ORetEv n) => None
    | (i, UCallEv m) => Some (i, CallEv m)
    | (i, URetEv n) => Some (i, RetEv n)
    end.

Notation projOver := (mapfilter projOverEv).
Notation projUnder := (mapfilter projUnderEv).

(* Module Transition System *)

Inductive ThreadState {E : ESig} : Type :=
| Idle
| Cont {Ret} (p : Prog E Ret) 
| UCall {Ret A} (k : A -> Prog E Ret)
.

Definition ThreadsSt {E : ESig} : Type := nat -> ThreadState (E := E).

Definition allIdle {E : ESig} : ThreadsSt (E := E) := fun n => Idle.

Definition ThreadStep {E F : ESig} 
    (mod : Mod E F) (th : ThreadState) (e : LEvent) (th' : ThreadState) : Prop :=
        match e with 
        | @OCallEv _ _ R m => th = Idle /\ th' = Cont (mod R m)
        | @ORetEv _ _ R n => th = Cont (Return n) /\ th' = Idle
        | @UCallEv _ _ A m => exists R (k : _ -> _ R), th = Cont (Bind m k) /\ th' = UCall (A := A) k
        | @URetEv _ _ A n =>  exists R (k : _ -> _ R), th = UCall k /\ th' = Cont (k n)
        end.

Definition ThreadsStep E F (mod : Mod E F)
  : ThreadsSt -> ThreadLEvent -> ThreadsSt -> Prop :=
  PointStep (ThreadStep (E := E) mod).

Definition ThreadsSteps {E F} (mod : Mod E F)
  : ThreadsSt -> Trace ThreadLEvent -> ThreadsSt -> Prop :=
  Steps (ThreadsStep mod).

(* Trace Semantics *)

Definition IsTraceOfMod {E F : ESig} (t : Trace ThreadLEvent) (mod : Mod E F) : Prop :=
    exists thst, IsPathOf allIdle t thst (ThreadsSteps mod).
    
Definition IsTraceOfSpec {E : ESig} (t : Trace (ThreadEvent E)) (spec : Spec E) : Prop := 
    exists st, IsPathOf spec.(Init) t st (Steps spec.(Step)).

Definition IsTraceOfLayer {E F : ESig} (t : Trace ThreadLEvent) (lay : @Layer E F) : Prop :=
    IsTraceOfSpec (projUnder t) lay.(Obj) /\ IsTraceOfMod t lay.(Impl).