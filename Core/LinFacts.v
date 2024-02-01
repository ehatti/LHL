From LHL.Core Require Import
    Program
    Specs
    Traces
    Linearizability.

From LHL.Core Require Import
    RefinesFacts.

Theorem lin_obs_ref {E F} : 
    forall (spec' spec : Spec E) (impl : Impl E F) ,
        Lin spec' spec -> 
        layerRefines (spec' :> impl) (spec :> impl).


(* 
show (overObj (spec :> impl)) :> impl' = overObj ((spec :> impl) |> impl').

step1: show specRefines spec' spec -> layerRefines (spec' :> impl) (spec :> impl)
step2: this gives that layerRefines (spec' :> impl) (overObj (spec :> idImpl)) :> impl)
step3: show that layerRefines ((overObj lay) :> impl) (lay |> impl)
step4: show layerRefines is transitive
step5: show that euttImpl impl impl' -> layerRefines (spec :> impl) (spec' :> impl)
step6: so we get
step7: we get (spec' :> impl) <= (overObj (spec :> idImpl)) :> impl) <= ((spec :> idImpl) :|> impl) = (spec :> idImpl |> impl) <= (spec :> impl)

as desired.

*)