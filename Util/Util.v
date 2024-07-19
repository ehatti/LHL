From Coq Require Import
  Logic
  Classical.

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

Parameter set : Type -> Type.
Parameter emp : forall {A}, set A.
Parameter insert : forall {A}, A -> set A -> set A.

Axiom insert_perm : forall {A} (s : set A) x y, insert x (insert y s) = insert y (insert x s).
Axiom insert_unique : forall {A} (s : set A) x, insert x (insert x s) = insert x s.
Axiom insert_cong : forall {A} (s1 s2 : set A) x y, insert x s1 = insert y s2 -> x = y /\ s1 = s2.

Axiom disj_cons : forall {A} (s : set A) x, insert x s <> emp.

Parameter contains : forall {A}, A -> set A -> Prop.
Infix "∈" := contains (at level 40).

Axiom contains_triv : forall {A} (s : set A) x, contains x (insert x s).