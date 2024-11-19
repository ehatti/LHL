From Core Require Import
  Specification
  Refinement.

Lemma Refines_refl {T E} :
  forall V : Spec T E,
  V ⊑ V.
Proof.
  unfold Refines. intros V t' p H.
  now exists t'.
Qed.

Lemma Refines_trans {T E} :
  forall V V'' : Spec T E,
  (exists V', V ⊑ V' /\ V' ⊑ V'') ->
  V ⊑ V''.
Proof.
  unfold Refines.
  intros V V'' [V' [H1 H2]] t p H3.
  apply H1 in H3. destruct H3 as [t' H3].
  eapply H2. exact H3.
Qed.