From Coq Require Import
  Logic
  Classical
  Program.Equality.

From LHL.Util Require Import
  Tactics.

Notation IRel M N := (forall X, M X -> N X -> Prop) (only parsing).

Definition ieq {M : Type -> Type} R (e1 e2 : M R) : Prop := e1 = e2.
Hint Unfold ieq : core.

Definition irespectful {M1 M2 N1 N2 : Type -> Type}
           (RM : IRel M1 M2)
           (RN : IRel N1 N2)
           (f1 : forall T, M1 T -> N1 T)
           (f2 : forall T, M2 T -> N2 T)
  : Prop :=
  forall T e1 e2, RM T e1 e2 -> RN T (f1 T e1) (f2 T e2).

Declare Scope isig_scope.
Delimit Scope isig_scope with isig.
(* Infix "==>" := irespectful (right associativity, at level 55) : isig_scope. *)


Section UPDT_ISTATE.
  Context 
  {A State : Type}.

  Definition differ_pointwise (ist ist' : A -> State) i :=
    (forall j , j <> i -> ist' j = ist j).

  Lemma differ_pointwise_comm: forall i s t,
    differ_pointwise s t i -> differ_pointwise t s i.
  Proof.
    unfold differ_pointwise. intros.
    apply H in H0; auto.
  Qed.

  Context 
  {eqA : A -> A -> bool}
  {eqA_dec : forall a a', eqA a a' = true <-> a = a'}.

  Definition updt_istate (ist : A -> State) (idx : A) (new_st : State) : A -> State :=
    fun a => if eqA a idx then new_st else ist a.
  
  Lemma updt_istate_pointwise (ist : A -> State) (idx : A) (new_st : State) : 
    differ_pointwise ist (updt_istate ist idx new_st) idx.
  Proof.
      unfold differ_pointwise. intros. 
      assert (eqA j idx = false).
      pose (eqA_dec j idx) as EQA_DEC.
      destruct EQA_DEC.
      destruct (eqA j idx).
      assert (true = true). reflexivity.
      apply H0 in H2. contradiction.
      reflexivity.
      unfold updt_istate.
      rewrite H0. reflexivity.
  Qed.

  Lemma updt_istate_i_eq_st (ist : A -> State) (idx : A) (new_st : State) :
    (updt_istate ist idx new_st) idx = new_st.
  Proof.
    unfold updt_istate.
    assert (idx = idx) by reflexivity.
    pose (eqA_dec idx idx) as EQA_DEC.
    destruct EQA_DEC. apply H1 in H.
    rewrite H. reflexivity.
  Qed.

End UPDT_ISTATE.

Definition eqb {A} (x y : A) : bool :=
  if classicT (x = y) then
    true
  else
    false.
Infix "=?" := eqb (at level 70).

Lemma eqb_id {A} : forall n : A, n =? n = true.
intros.
unfold eqb.
destruct (classicT (n = n)).
easy.
congruence.
Qed.

Lemma eqb_iff {A} : forall (x y : A), x =? y = true <-> x = y.
Proof.
  intros. unfold eqb.
  destruct (classicT (x = y)).
  - split; auto.
  - split; auto.
    inversion 1.
Qed.

Lemma eqb_nid {A} : forall n m : A, n <> m -> n =? m = false.
intros.
unfold eqb.
destruct (classicT (n = m)).
contradiction.
easy.
Qed.


Lemma differ_pointwise_trivial {A B} (f : A -> B) i x :
  differ_pointwise f (fun j => if i =? j then x else f j) i.
unfold differ_pointwise.
intros.
dec_eq_nats i j.
congruence.
rewrite eqb_nid; easy.
Qed.

Definition neqb {A} (x y : A) : bool :=
  if classicT (x <> y) then
    true
  else
    false.
Infix "/=?" := neqb (at level 70).

Lemma neqb_inv {A} :
  forall x y : A,
  neqb x y = false <-> eqb x y = true.
unfold neqb, eqb. split; intros.
destruct (classicT (x <> y)).
discriminate.
apply NNPP in n.
destruct (classicT (x = y)).
easy.
contradiction.
destruct (classicT (x = y)).
destruct (classicT (x <> y)).
contradiction.
easy.
discriminate.
Qed.

Lemma eqb_inv {A} :
  forall x y : A,
  neqb x y = true <-> eqb x y = false.
unfold neqb, eqb. split; intros.
destruct (classicT (x <> y)).
destruct (classicT (x = y)).
contradiction.
easy.
discriminate.
destruct (classicT (x = y)).
discriminate.
destruct (classicT (x <> y)).
easy.
exfalso. apply n0. easy.
Qed.

Ltac ddestruct H := dependent destruction H.
Ltac decide_prop P :=
  let H := fresh in
  assert (H : P \/ ~P) by apply excluded_middle;
  destruct H.

Definition set : Type -> Type := fun A => A -> Prop.
Definition emp : forall {A}, set A :=
  fun _ _ => False.
Definition insert : forall {A}, A -> set A -> set A :=
  fun _ x s y => x = y \/ s y.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Lemma insert_perm :
  forall {A} (s : set A) x y,
  insert x (insert y s) = insert y (insert x s).
intros.
extensionality z. unfold insert.
apply propositional_extensionality.
split; intros.
{
  destruct H.
  { right. now left. }
  {
    destruct H.
    { now left. }
    { right. now right. }
  }
}
{
  destruct H.
  { right. now left. }
  {
    destruct H.
    { now left. }
    { right. now right. }
  }
}
Qed.

Lemma insert_unique :
  forall {A} (s : set A) x,
  insert x (insert x s) = insert x s.
unfold insert. intros.
extensionality y.
apply propositional_extensionality.
split; intros.
{
  destruct H.
  { now left. }
  { easy. }
}
{
  destruct H.
  { now left. }
  { right. now right. }
}
Qed.

Lemma help : forall P Q, P = Q -> P <-> Q.
intros. now rewrite H.
Qed.

Lemma insert_cong1 :
  forall {A} (x y : A),
  insert x emp = insert y emp ->
  x = y.
unfold insert. intros.
apply equal_f with (x:=x) in H.
assert (x = x \/ emp x) by now left.
rewrite H in H0. now destruct H0.
Qed.

Lemma insert_cong2 :
  forall {A} (x y z w : A),
  x <> y ->
  insert x (insert y emp) = insert z (insert w emp) ->
  x = z /\ y = w \/
  x = w /\ y = z.
unfold insert, emp.
intros A x y z w neq. intros.
dec_eq_nats x z.
{
  dec_eq_nats y w.
  { now left. }
  {
    dec_eq_nats z w.
    {
      apply equal_f with (x:=y) in H.
      assert (w = y \/ y = y \/ False).
      { right. now left. }
      rewrite H in H1.
      destruct H1. congruence.
      destruct H1. congruence.
      easy.
    }
    {
      apply equal_f with (x:=y) in H.
      assert (z = y \/ y = y \/ False).
      { right. now left. }
      rewrite H in H2.
      destruct H2. now subst.
      destruct H2. congruence.
      easy.
    }
  }
}
{
  right.
  dec_eq_nats x w.
  {
    apply equal_f with (x:=y) in H.
    assert (w = y \/ y = y \/ False).
    { right. now left. }
    rewrite H in H1.
    destruct H1. easy.
    destruct H1. congruence.
    easy.
  }
  {
    dec_eq_nats y z.
    {
      apply equal_f with (x:=x) in H.
      assert (x = x \/ z = x \/ False).
      { now left. }
      rewrite H in H2.
      destruct H2. congruence.
      destruct H2. congruence.
      easy.
    }
    {
      dec_eq_nats w y.
      {
        apply equal_f with (x:=x) in H.
        assert (x = x \/ y = x \/ False).
        { now left. }
        rewrite H in H3.
        destruct H3. congruence.
        destruct H3. congruence.
        easy.
      }
      {
        apply equal_f with (x:=y) in H.
        assert (x = y \/ y = y \/ False).
        { right. now left. }
        rewrite H in H4.
        destruct H4. congruence.
        destruct H4. congruence.
        easy.
      }
    }
  }
}
Qed.

Lemma insert_cong2_left :
  forall {I A} (i j k l : I) (x y z w : A),
  i <> j ->
  j <> k ->
  insert (i, x) (insert (j, y) emp) = insert (k, z) (insert (l, w) emp) ->
  (i, x) = (k, z) /\ insert (j, y) emp = insert (l, w) emp.
intros I A i j k l x y z w.
intros neq1 neq2 H. 
apply insert_cong2 in H; auto.
2:{ unfold not. intros. now ddestruct H0. }
destruct H; destruct H;
ddestruct H; ddestruct H0;
easy.
Qed.

Lemma insert_cong2_pad :
  forall {I A} (i j k : I) (x y z : A),
  i <> j ->
  insert (i, x) (insert (j, y) emp) = insert (i, x) (insert (k, z) emp) ->
  (j, y) = (k, z).
unfold insert, emp. intros.
apply equal_f with (x:=(j, y)) in H0.
assert ((i, x) = (j, y) \/ (j, y) = (j, y) \/ False).
{ right. now left. }
rewrite H0 in H1.
destruct H1. now ddestruct H1.
now destruct H1.
Qed.

Lemma disj_cons : forall {A} (s : set A) x, insert x s <> emp.
unfold insert, emp, not. intros.
apply equal_f with (x:=x) in H.
rewrite <- H. now left.
Qed.

Lemma disj_cons2 :
  forall {I A} (i j : I) (x y : A),
  i <> j ->
  insert (i, x) (insert (j, y) emp) <> (insert (i, x) emp).
unfold insert, emp, not. intros.
apply equal_f with (x:=(j, y)) in H0.
apply H.
assert ((i, x) = (j, y) \/ (j, y) = (j, y) \/ False).
{ right. now left. }
rewrite H0 in H1.
destruct H1. now ddestruct H1.
easy.
Qed.

Lemma disj_cons2_abs :
  forall {A} (x y : A),
  x <> y ->
  insert x (insert y emp) <> (insert x emp).
unfold insert, emp, not. intros.
apply equal_f with (x:=y) in H0.
apply H.
assert (x = y \/ y = y \/ False).
{ right. now left. }
rewrite H0 in H1.
destruct H1. now ddestruct H1.
easy.
Qed.

Definition contains : forall {A}, A -> set A -> Prop :=
  fun A x s => s x.
Infix "∈" := contains (at level 40).

Lemma contains_triv : forall {A} (s : set A) x, contains x (insert x s).
unfold insert, contains. intros. now left.
Qed.

Lemma contains_contr : forall {A} (x : A), ~contains x emp.
easy.
Qed.

Lemma contains_invert : forall {A} (s : set A) x y,
  contains x (insert y s) ->
  x = y \/ contains x s.
unfold contains, insert.
intros. destruct H.
now left.
now right.
Qed.