From Core Require Import
  Specification
  Composition
  Refinement
  Program.

Definition Lin {T E} (V' V : Spec T E) :=
  V' ⊑ V :▷ idMod.
Infix "↝" := Lin (at level 47, no associativity).