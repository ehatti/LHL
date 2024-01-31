From LHL.Core Require Import
    Program
    Specs
    Traces
    Linearizability.

Theorem lin_obs_ref {E F} : 
    forall (spec' spec : Spec E) (impl : Impl E F) ,
        Lin spec' spec -> 
        layerRefines (mkLayer spec' impl) (mkLayer spec impl).
Proof.
    intros. intro. intro.
    unfold IsTraceOfSpec.
    destruct H0. destruct H0.