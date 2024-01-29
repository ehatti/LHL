From LHL.Util Require Import
    TransUtil.

From LHL.Core Require Import
    Program
    Traces.

Definition KConc {E} (spec : Spec E) : Spec E := overObj (idLayer spec).

Definition Linearizable {E} (spec' : Spec E) (spec : Spec E) :=
    specRefines spec' (KConc spec). 