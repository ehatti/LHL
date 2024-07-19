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

Definition Lin {T E} (spec' spec : Spec T E) :=
  specRefines spec' (KConc spec).

Variant HBRw_ {T E} : Trace (ThreadEvent T E) -> Trace (ThreadEvent T E) -> Prop :=
| SwapCalls l r i j A (m : E A) B (n : E B) :
    i <> j ->
    HBRw_ (l ++ [(i, CallEv m); (j, CallEv n)] ++ r)
          (l ++ [(j, CallEv n); (i, CallEv m)] ++ r)
| SwapRets l r i j A (m : E A) v B (n : E B) w :
    i <> j ->
    HBRw_ (l ++ [(i, RetEv m v); (j, RetEv n w)] ++ r)
          (l ++ [(j, RetEv n w); (i, RetEv m v)] ++ r)
| DelayCall l r i j A (m : E A) B (n : E B) w :
    i <> j ->
    HBRw_ (l ++ [(i, CallEv m); (j, RetEv n w)] ++ r)
          (l ++ [(j, RetEv n w); (i, CallEv m)] ++ r).

Definition HBRw {T E} : (Trace (ThreadEvent T E)) -> (Trace (ThreadEvent T E)) -> Prop :=
  clos_refl_trans_1n (Trace (ThreadEvent T E)) HBRw_.

Inductive AllRetEv {T E} : Trace (@ThreadEvent T E) -> Prop :=
| NilAllRet : AllRetEv nil
| ConsAllRet {Ret s i} {m : E Ret} {v : Ret} :
    AllRetEv s ->
    AllRetEv ((i, RetEv m v) :: s).

Inductive AllCallEv {T E} : Trace (ThreadEvent T E) -> Prop :=
| NilAllCall : AllCallEv nil
| ConsCall {Ret s i} {m : E Ret} :
    AllCallEv s ->
    AllCallEv ((i, CallEv m) :: s).

Definition LinRw {T E} :
  (Trace (ThreadEvent T E)) -> (Trace (ThreadEvent T E)) -> Prop :=
  fun s t => exists sC sR, 
    AllRetEv sR /\ AllCallEv sC /\
    HBRw (s ++ sR) (t ++ sC).

Infix "~~>" := LinRw (at level 40).