Require Import Utf8.
Require Import Setoid.

Axiom neg_conj : ∀ P Q, ¬(P /\ Q) <-> ¬P \/ ¬Q.
Axiom neg_disj : ∀ P Q, ¬(P \/ Q) <-> ¬P /\ ¬Q.
Axiom neg_forall : ∀ A (P : A -> Prop), ¬(∀ x, P x) <-> ∃ x, ¬P x.
Axiom neg_exists : ∀ A (P : A -> Prop), ¬(∃ x, P x) <-> ∀ x, ¬P x.
Axiom neg_neg : ∀ P : Prop, ¬¬P <-> P.
Axiom neg_impl : ∀ P Q : Prop, ¬(P -> Q) <-> (P /\ ¬Q).

Ltac negate H :=
  repeat (
    setoid_rewrite neg_neg in H ||
    setoid_rewrite neg_conj in H ||
    setoid_rewrite neg_disj in H ||
    setoid_rewrite neg_impl in H ||
    setoid_rewrite neg_forall in H ||
    setoid_rewrite neg_exists in H
  ).

Parameter P Q R : Prop.

Goal ¬(¬¬(¬P /\ (R -> ¬(P /\ Q))) /\ Q) → False.
Proof.
  intros.
  negate H.