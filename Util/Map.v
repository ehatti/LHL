From Util Require Import
  DecEq.

From Coq.Logic Require Import
  FunctionalExtensionality.

Definition Map A B := A -> B.

Declare Scope map_scope.
Delimit Scope map_scope with Map.
Bind Scope map_scope with Map.

Definition update {A B} (m : Map A B) (i : A) (v : B) :=
  fun j =>
    if i =? j then
      v
    else
      m j.
Notation "m [ i ↦ v ]" :=
  (update m i v)
  (at level 40, left associativity).

Lemma update_eq {A B} :
  forall (m : Map A B) (i : A) (v : B),
  m [i ↦ v] i = v.
Proof.
  unfold update. intros m i v.
  now rewrite deceq_true.
Qed.

Lemma update_neq {A B} :
  forall (m : Map A B) (i j : A) (v : B),
  i <> j ->
  m [i ↦ v] j = m j.
Proof.
  unfold update. intros m i j v neq.
  now rewrite deceq_false.
Qed.

Lemma map_ext {A B} :
  forall m1 m2 : Map A B,
  (forall i, m1 i = m2 i) ->
  m1 = m2.
Proof.
  intros m1 m2 eq.
  extensionality i.
  apply eq.
Qed.

Definition DiffPt {A B} (m m' : Map A B) (i : A) :=
  forall j, i <> j -> m j = m' j.

Lemma DiffPt_triv_right {A B} :
  forall (m : Map A B) i v,
  DiffPt m (m [i ↦ v]) i.
Proof.
  unfold DiffPt, update.
  intros m i v j neq.
  now rewrite deceq_false.
Qed.

Lemma DiffPt_triv_left {A B} :
  forall (m : Map A B) i v,
  DiffPt (m [i ↦ v]) m i.
Proof.
  unfold DiffPt, update.
  intros m i v j neq.
  now rewrite deceq_false.
Qed.

Global Opaque update.