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

Definition LinRwSmall {F} (evs evs' : Trace (ThreadEvent F)) : Prop :=
    exists h h' i i' m m',
      i <> i' ->
      evs = h ++ (cons (i, m) (cons (i', m') nil)) ++ h' ->
      ((exists Ret (l : F Ret), m = CallEv l) \/ (exists Ret (v : Ret), m' = RetEv v)) ->
      evs' = h ++ (cons (i', m') (cons (i, m) nil)) ++ h'.

Inductive LinRw {F} : Trace (ThreadEvent F) -> Trace (ThreadEvent F) -> Prop :=
| LinRefl {s} : LinRw s s
| LinTrans {s t r} : LinRwSmall s t -> LinRw t r -> LinRw s r.