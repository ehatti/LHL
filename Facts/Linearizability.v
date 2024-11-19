From Core Require Import
  Linearizability
  Specification
  Composition
  Refinement
  Signature
  Program.

Theorem observational_refinement {T E F} : 
  forall (V' V : Spec T E) (M : Mod E F),
  V' ↝ V -> 
  V' :▷ M ⊑ V :▷ M.
Proof.
Admitted.

Theorem locality {T E F} :
  forall (VE VE' : Spec T E) (VF VF' : Spec T F),
  VE' ↝ VE /\ VF' ↝ VF <-> VE' :⊗: VF' ↝ VE :⊗: VF.
Proof.
Admitted.