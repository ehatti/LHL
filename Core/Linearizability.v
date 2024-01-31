From LHL.Util Require Import
    TransUtil.

From LHL.Core Require Import
    Program
    Specs
    Traces.

Definition KConc {E} (spec : Spec E) : Spec E := overObj (idLayer spec).

Definition Lin {E} (spec' : Spec E) (spec : Spec E) :=
    specRefines spec' (KConc spec).

(* Definition LinRwSmall (evs1 evs2 : Trace ) *)