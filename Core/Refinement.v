From Core Require Import
  Specification
  Interaction.

From Util Require Import
  Relation.

Definition Refines {T E} (V' V : Spec T E) :=
  forall t' p,
    Steps V'.(Step) V'.(Init) p t' ->
    exists t,
      Steps V.(Step) V.(Init) p t.
Infix "⊑" := Refines (at level 47, no associativity).