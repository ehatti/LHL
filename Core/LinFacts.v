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
    unfold Lin in H. 
    unfold IsTraceOfSpec.
    destruct H0. destruct H0.


(* 
show (overObj (spec :> impl)) :> impl' = overObj ((spec :> impl) |> impl').

step1: show specRefines spec' spec -> layerRefines (mkLayer spec' impl) (mkLayer spec impl)

(spec' :> impl) < overObj (spec :> idImpl) :> impl 

*)