From Coq Require Import
  Logic.

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
Infix "==>" := irespectful (right associativity, at level 55) : isig_scope.


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

Require Import Coq.Arith.PeanoNat.

Lemma eqb_id : forall n : nat, n =? n = true.
intros.
induction n.
easy.
simpl.
f_equal.
easy.
Qed.

Lemma eqb_nid : forall n m : nat, n <> m -> n =? m = false.
fix rec 1.
intros.
destruct n.
destruct m.
easy.
easy.
destruct m.
easy.
simpl in *.
apply rec.
congruence.
Qed.
