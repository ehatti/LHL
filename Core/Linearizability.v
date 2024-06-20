From Coq Require Import
      Relations.

From LHL.Util Require Import
  TransUtil.

From LHL.Core Require Import
  Program
  Specs
  Traces.

From Coq Require Import
  Lists.List.
Import ListNotations.

Definition KConc {T E} (spec : Spec T E) : Spec T E := overObj (spec :> idImpl).

Definition Lin {T E} (spec' : Spec T E) (spec : Spec T E) :=
  specRefines spec' (KConc spec).

Definition HBRw_ {T E} (evs evs' : Trace (ThreadEvent T E)) : Prop :=
    exists h h' i i' m m',
      i <> i' /\
      evs = h ++ [(i, m); (i', m')] ++ h' /\
      ((exists Ret e, m = @CallEv E Ret e) \/
       (exists Ret e v, m' = @RetEv E Ret e v)) /\
      evs' = h ++ [(i', m'); (i, m)] ++ h'.

Definition HBRw {T E} : (Trace (ThreadEvent T E)) -> (Trace (ThreadEvent T E)) -> Prop :=
  clos_refl_trans (Trace (ThreadEvent T E)) HBRw_.

Inductive AllRetEv {T E} : Trace (ThreadEvent T E) -> Prop :=
| NilAllRet : AllRetEv nil
| ConsAllRet {Ret s i} {m : E Ret} {v : Ret} :
    AllRetEv s ->
    AllRetEv (cons (i, RetEv m v) s).

Inductive AllCallEv {T E} : Trace (ThreadEvent T E) -> Prop :=
| NilAllCall : AllCallEv nil
| ConsCall {Ret s i} {m : E Ret} :
    AllCallEv s ->
    AllCallEv (cons (i, CallEv m) s).

Definition LinRw {T E} : 
  (Trace (ThreadEvent T E)) -> (Trace (ThreadEvent T E)) -> Prop :=
  fun s t => exists sO sP, 
    AllRetEv sP /\ AllCallEv sO /\
    HBRw (s ++ sP) (t ++ sO).

Notation LinToSpec ρ V := (exists l, IsTraceOfSpec l V /\ LinRw ρ l). 