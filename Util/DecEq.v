From Util Require Import
  Axioms.

Definition deceq {A} (x y : A) : bool :=
  if prop_decidable (x = y) then true else false.
Infix "=?" := deceq (at level 40).

Lemma deceq_true {A} :
  forall x : A,
  x =? x = true.
Proof.
  intros x. unfold deceq.
  now destruct (prop_decidable (x = x)).
Qed.

Lemma true_deceq {A} :
  forall x y : A,
  x =? y = true ->
  x = y.
Proof.
  unfold deceq. intros x y eq.
  now destruct (prop_decidable (x = y)).
Qed.

Lemma deceq_false {A} :
  forall x y : A,
  x <> y ->
  x =? y = false.
Proof.
  intros x y neq. unfold deceq.
  now destruct (prop_decidable (x = y)).
Qed.

Lemma false_deceq {A} :
  forall x y : A,
  x =? y = false ->
  x <> y.
Proof.
  unfold deceq. intros x y neq.
  now destruct (prop_decidable (x = y)).
Qed.

Global Opaque deceq.