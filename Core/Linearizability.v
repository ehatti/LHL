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

Definition KConc {E} (spec : Spec E) : Spec E := overObj (spec :> idImpl).

Definition Lin {E} (spec' : Spec E) (spec : Spec E) :=
  specRefines spec' (KConc spec).

Definition HBRw_ {E} (evs evs' : Trace (ThreadEvent E)) : Prop :=
    exists h h' i i' m m',
      i <> i' ->
      evs = h ++ (cons (i, m) (cons (i', m') nil)) ++ h' ->
      ((exists Ret (e : E Ret), m = CallEv e) \/ (exists Ret (e : E Ret) (v : Ret), m' = RetEv e v)) ->
      evs' = h ++ (cons (i', m') (cons (i, m) nil)) ++ h'.

Definition HBRw {E} : (Trace (ThreadEvent E)) -> (Trace (ThreadEvent E)) -> Prop :=
  clos_refl_trans (Trace (ThreadEvent E)) HBRw_.

Inductive AllRetEv {E} : Trace (@ThreadEvent E) -> Prop :=
| NilAllRet : AllRetEv nil
| ConsAllRet {Ret s i} {m : E Ret} {v : Ret} :
    AllRetEv s ->
    AllRetEv (cons (i, RetEv m v) s).

Inductive AllCallEv {E} : Trace (@ThreadEvent E) -> Prop :=
| NilAllCall : AllCallEv nil
| ConsCall {Ret s i} {m : E Ret} :
    AllCallEv s ->
    AllCallEv (cons (i, CallEv m) s).

Definition LinRw {E} : 
  (Trace (ThreadEvent E)) -> (Trace (ThreadEvent E)) -> Prop :=
  fun s t => exists sO sP, 
    AllCallEv sO -> AllRetEv sP -> 
    HBRw (s ++ sP) (t ++ sO).

(*  
The correct invariant is this:
 Notation LinToVF ρ := (exists l, IsTraceOfSpec l VF /\ LinRw ρ l). 
 *)