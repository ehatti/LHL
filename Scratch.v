Definition eq {A} (x y : A) :=
  forall P : A -> Prop, P x -> P y.

Context {A : Type}.

Theorem eq_refl : forall x : A, eq x x.
Proof. easy. Qed.

Theorem eq_symm : forall x y : A, eq x y -> eq y x.
Proof.
  unfold eq. intros.
  specialize (H (fun z => P z -> P x) (fun x => x)).
  now apply H.
Qed.