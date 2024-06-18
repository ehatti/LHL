From LHL.Core Require Import
  Program
  ProgramFacts
  Specs
  Traces
  Tensor.

(* Note to Eashan: This is proven by C4 in Traces_Pair.v, see ConcTraceIncl_pairObject *)
Theorem tensor_monotonic {E F} :
  forall (specE specE' : Spec E) (specF specF' : Spec F) ,
  specRefines specE specE' ->
  specRefines specF specF' -> 
  specRefines (tensorSpec specE specF) (tensorSpec specE' specF').
Proof.
Admitted.

(* Note to Eashan: This is also seems to be proven by C4 in Traces_Pair.v *)
Theorem tensor_monotonic_inv {E F} : 
  forall (specE specE' : Spec E) (specF specF' : Spec F), 
    specRefines (tensorSpec specE specF) (tensorSpec specE' specF') ->
    specRefines specE specE' /\ specRefines specF specF'.
Proof.
Admitted.

Theorem tensor_neutral {E F} : 
  implEq (tensorImpl (@idImpl E) (@idImpl F)) (@idImpl (E |+| F)).
Proof.
  (* unfold implEq, tensorImpl, idImpl, idProg. intros. destruct f. progEqFrobL; simpl in *. *)
Admitted.

Theorem tensor_layer_funct_l {E F E' F'}:   
  forall (specE : Spec E) (specF : Spec F) (M : Impl E E') (N : Impl F F'),
  specRefines (tensorSpec (overObj (specE :> M)) (overObj (specF :> N))) (overObj (tensorLayer (specE :> M) (specF :> N))).
Proof.
Admitted.

Theorem tensor_layer_funct_r {E F E' F'}:   
  forall (specE : Spec E) (specF : Spec F) (M : Impl E E') (N : Impl F F'),
  specRefines (overObj (tensorLayer (specE :> M) (specF :> N))) (tensorSpec (overObj (specE :> M)) (overObj (specF :> N))).
Proof.
Admitted.