(*From Coq Require Import
     List
     Program
     Relations
     RelationClasses.

From Paco Require Import paco.*)

(* From C4.Util Require Import
  Util

From C4.Core Require Import
  Program
  ProgramOps
  ProgramFacts
  Object. 
*)

From Paco Require Import paco.

From LHL.Util Require Import
  Util
  Tactics.

Require Import Coq.Program.Equality.

From LHL.Core Require Import
  Program.

Inductive euttF {E A}
  (_eutt : Prog E A -> Prog E A -> Prop)
  : Prog E A -> Prog E A -> Prop :=
| euttF_Return r : euttF _eutt (Return r) (Return r)
| euttF_Vis X (e : E X) k k' : (forall x, _eutt (k x) (k' x)) ->
    euttF _eutt (Vis e k) (Vis e k')
| euttF_Tau p p' : _eutt p p' -> euttF _eutt (Tau p) (Tau p')
| euttF_L p p' : euttF _eutt p p' -> euttF _eutt (Tau p) p'
| euttF_R p p' : euttF _eutt p p' -> euttF _eutt p (Tau p')
.

Definition eutt {E} R
  : Prog E R -> Prog E R -> Prop := paco2 euttF bot2.
Arguments eutt {E} [R].

Definition euttImpl {E F}
  (impl : Impl E F) (impl' : Impl E F) : Prop := 
    forall Ret (f : F Ret) , eutt (impl Ret f) (impl' Ret f).
Arguments euttImpl {E F}.

Lemma monotone_euttF {E} R
  : monotone2 (euttF (E:=E) (A:=R)).
Proof.
  induction 1; constructor; auto.
Qed.
Hint Resolve monotone_euttF : paco.

Lemma eutt_Tau_l {E R}
  : forall (p1 p2 : Prog E R),
    eutt p1 p2 ->
    eutt (Tau p1) p2.
Proof.
  intros. punfold H. pfold.
  constructor. assumption.
Qed.

Lemma eutt_Tau_r (E : ESig)
    (R : Type) (p p' : Prog E R)
  : eutt p p' -> eutt p (Tau p').
Proof.
  intros. punfold H. pfold.
  constructor. assumption.
Qed.

Lemma Reflexive_eutt_ieq {E R}
  : forall (p : Prog E R), eutt p p.
Proof.
  pcofix self.
  pfold.
  intros []; repeat (constructor; auto).
Qed.

Global Hint Resolve Reflexive_eutt_ieq : core.

Lemma Symmetric_eutt {E R}
  : forall (p1 p2 : Prog E R),
    eutt p1 p2 -> eutt p2 p1.
Proof.
  pcofix self.
  intros p1 p2 H; punfold H; pfold.
  induction H; constructor; pclearbot; auto.
  right.
  apply self.
  apply H.
Qed.

Section Trans.

Lemma inv_eutt_Noop_left {E R}
  : forall (p1 p2 : Prog E R),
    euttF (upaco2 (euttF (A:=R)) bot2) (Tau p1) p2 ->
    euttF (upaco2 (euttF (A:=R)) bot2) p1 p2.
Proof.
  intros p1 p2 H; remember (Tau p1) as Tau_p1 eqn:EQp1.
  induction H; try discriminate.
  - constructor.
    destruct H; [| contradiction ].
    punfold H.
    inversion EQp1.
    subst; auto.
  - inversion EQp1. subst. auto.
  - constructor; auto.
Qed.

Lemma inv_eutt_Noop_right {E R}
  : forall (p1 p2 : Prog E R),
    euttF (upaco2 (euttF (A:=R)) bot2) p1 (Tau p2) ->
    euttF (upaco2 (euttF (A:=R)) bot2) p1 p2.
Proof.
  intros p1 p2 H; remember (Tau p2) as Noop_p1 eqn:EQp1.
  induction H; try discriminate.
  - constructor.
    destruct H; [| contradiction ].
    punfold H.
    inversion EQp1.
    subst; auto.
  - constructor; auto.
  - inversion EQp1. subst. auto.
Qed.

(* Lemma Transitive_eutt {E R}
 : forall (p1 p2 p3 : Prog E R),
   eutt p1 p2 ->
   eutt p2 p3 ->
   eutt p1 p3.
pcofix rec.
intros.
punfold H0.
dependent destruction H0.
punfold H1.
dependent destruction H1.
pfold.
constructor.
pfold.
constructor. *)


End Trans.

(*
Local Notation fI := flattenObject.

Inductive flattenProg_bisim {M1 M2 N1 N2}
          (RM : IRel M1 M2) (RN : IRel N1 N2)
          (f1 : forall R, M1 R -> Prog N1 R)
          (f2 : forall R, M2 R -> Prog N2 R)
          {R}
  : Prog N1 R -> Prog N2 R -> Prop :=
| flattenProg_bisim_base p1 p2
  : eutt RM p1 p2 ->
    flattenProg_bisim RM RN f1 f2 (flattenProg f1 p1) (flattenProg f2 p2)
| flattenProg_bisim_bind {S} k1 k2 (p1 : Prog N1 S) p2
  : (forall x, eutt RM (k1 x) (k2 x)) ->
    eutt RN p1 p2 ->
    flattenProg_bisim RM RN f1 f2
      (bindFlattenProg f1 k1 p1)
      (bindFlattenProg f2 k2 p2)
.
*)

Lemma euttF_Noop_L {E R}
      (_eutt : Prog E R -> Prog E R -> Prop)
  : forall (p1 p2 : Prog E R),
    paco2 euttF _eutt p1 p2 -> paco2 euttF _eutt (Tau p1) p2.
Proof.
  pcofix self.
  intros p1 p2 H. pfold. punfold H. induction H.
  - constructor. constructor.
  - constructor. constructor; auto. intros.
    eapply upaco2_mon; eauto.
  - apply euttF_L. constructor.
    eapply upaco2_mon; eauto.
  - constructor; auto.
  - constructor. left. pfold.
    eapply monotone_euttF; eauto.
    intros; eapply upaco2_mon; eauto.
Qed.

Inductive subst_subst_bisim {E F G}
          (f : Impl F G) (g : Impl E F)
          {R}
  : Prog E R -> Prog E R -> Prop :=
| subst_subst_bisim_base p
  : subst_subst_bisim f g
      (substProg g (substProg f p))
      (substProg (fun _ m => substProg g (f _ m)) p)
| subst_subst_bisim_bind {S} (p : _ S) k
  : subst_subst_bisim f g
      (substProg g (bindSubstProg f k p))
      (bindSubstProg
         (fun (A0 : Type) (m0 : G A0) => substProg g (f A0 m0)) k
         (substProg g p))
| subst_subst_bisim_bind_2 {S T} (p : _ S) (h : S -> _ T) k
  : subst_subst_bisim f g
      (bindSubstProg g (fun r0 : _ => bindSubstProg f k (h r0)) p)
      (bindSubstProg
         (fun (A0 : Type) (m0 : G A0) => substProg g (f A0 m0)) k
         (bindSubstProg g h p))
.