From LHL Require Import
    Tactics
    Program.

Require Import
    Coq.Logic.FunctionalExtensionality.

Require Import Setoid.
Require Import SetoidClass.
Require Import Morphisms.

Definition frobProgram {E Ret} (p : Prog E Ret) :
  Prog E Ret :=
  match p with
    | Vis e f => Vis e f
    | Return a => Return a
    | Tau p' => Tau p'
  end.

Theorem frobProgId {E Ret} (p : Prog E Ret) :
  p = frobProgram p.
Proof.
  destruct p; reflexivity.
Defined. 

Ltac rewriteFrobProgram x :=
  let r := fresh "r" in
  let H := fresh "H" in
  remember x as r eqn: H;
    revert H;    
    match goal with
    | [ |- r = ?x -> ?y ] =>
      refine (
          match eq_sym (frobProgId x)
                in _ = X
                return r = X -> y
          with
          | eq_refl => _
          end)
    end;
    intro H; subst r.

Ltac progEqFrobL :=
  match goal with
      | [ |- progEq ?p ?p'] =>
       rewriteFrobProgram p
  end.

Ltac progEqFrobR :=
  match goal with
      | [ |- progEq ?p ?p'] =>
       rewriteFrobProgram p'
  end.

Ltac progEqFrob :=
  match goal with
      | [ |- progEq ?p ?p'] =>
       rewriteFrobProgram p; 
       rewriteFrobProgram p'
  end.

Lemma eqProgEq:
  forall E Ret p,
    @progEq E Ret p p.
Proof.
  intros E Ret.
  cofix self.
  intros.
  destruct p;
  constructor;
  auto.
Qed.

Lemma eqProgEq':
  forall E Ret p1 p2,
    p1 = p2 ->
    @progEq E Ret p1 p2.
Proof.
  intros.
  rewrite H.
  apply eqProgEq.
Qed.

Lemma progEqSym:
  forall E Ret p1 p2,
    @progEq E Ret p1 p2 ->
    @progEq E Ret p2 p1.
Proof.
  intros E Ret.
  cofix self.
  intros.
  destruct p1; destruct p2; inversion H; injpair; clear H.
  - constructor. intros. eauto.
  - constructor.
  - constructor. eauto.
Qed.

Lemma progEqTrans:
  forall E Ret p1 p2 p3,
    @progEq E Ret p1 p2 ->
    @progEq E Ret p2 p3 ->
    @progEq E Ret p1 p3.

Proof.
  intros E Ret.
  cofix self.
  intros.
  destruct p1; destruct p2; 
  inversion H; injpair; clear H; destruct p3; 
  inversion H0; injpair; clear H0.
  - constructor. intros. eauto.
  - constructor.
  - constructor. eauto.
Qed.


Add Parametric Relation E Ret: (@Prog E Ret) (@progEq E Ret)
    reflexivity proved by (eqProgEq E Ret)
    symmetry proved by (progEqSym E Ret)
    transitivity proved by (progEqTrans E Ret)                        
      as programEq_rel.

Add Parametric Morphism E Ret A: (@Vis E Ret A)
    with signature eq ==> pointwise_relation _ eq ==> eq
      as bind_eq_eq.
Proof.
  unfold pointwise_relation.
  intros. f_equal. apply functional_extensionality. assumption.
Qed.

Add Parametric Morphism E Ret A: (@Vis E Ret A)
    with signature eq ==> pointwise_relation _ progEq ==> progEq
      as bind_progEq_progEq.
Proof.
  unfold pointwise_relation.
  intros. constructor. assumption.
Qed.

Lemma mapProgProgEq:
  forall (E F : Type -> Type) (f : forall Ret : Type, E Ret -> F Ret) 
    (Ret : Type) (x y : Prog E Ret),
    progEq x y -> progEq (mapProg f x) (mapProg f y).
Proof.
  cofix self.
  intros.
  match goal with
  | [ |- progEq ?p ?p'] =>
    rewriteFrobProgram p;
      rewriteFrobProgram p'
  end.
  destruct x; destruct y; simpl in *; inversion H; injpair; clear H.
  - constructor. eauto.
  - reflexivity.
  - constructor. eauto.
Qed.

Lemma implEqRefl :   
  forall E F impl,
    @implEq E F impl impl.
Proof.
  unfold implEq; intros; apply eqProgEq.
Qed.

Lemma implEqSym :   
  forall E F impl impl',
    @implEq E F impl impl' -> 
    @implEq E F impl' impl.
Proof.
  unfold implEq; intros; eapply progEqSym; eauto.
Qed.

Lemma implEqTrans :   
  forall E F impl impl' impl'',
    @implEq E F impl impl' -> 
    @implEq E F impl' impl'' ->
    @implEq E F impl impl''.
Proof.
  unfold implEq; intros; eapply progEqTrans; eauto.
Qed.
