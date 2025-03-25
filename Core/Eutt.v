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

(*
Inductive untaus1 {E R} (P : Prog E R -> Prop) : Prog E R -> Prop :=
| untaus1_Noop p : untaus1 P p -> untaus1 P (Tau p)
| untaus1_Id p : P p -> untaus1 P p
.

Lemma eutt_Ret_inv {E E'} (RR : IRel E E') {R} (r : R) (p' : Prog E' R)
  : eutt RR (Return r) p' ->
    untaus1 (fun p => Return r = p) p'.
Proof.
  intros H. punfold H.
  remember (Return r) as p1; generalize dependent r.
  induction H.
  - constructor. inv Heqp1. reflexivity.
  - discriminate.
  - discriminate.
  - discriminate.
  - constructor. eauto.
Qed.

Lemma eq_Vis_inv {E R} {R1} (e1 : E R1) k1 {R2} (e2 : E R2) k2
  : (x <- e1; k1 x) = (x <- e2; k2 x) ->
    forall (P : forall R' (m : E R') (k : R' -> Prog E R), Prop),
      P _ e1 k1 -> P _ e2 k2.
Proof.
  intros H P.
  change (P _ e2 k2) with
      (match Vis e2 k2 with
       | Vis m k => P _ m k
       | _ => False
       end).
  remember (Vis e2 k2).
  destruct H.
  auto.
Qed.

Lemma eutt_Vis_inv {E1 E2} (RR : IRel E1 E2)
      {X} (e1 : E1 X) {R} (k1 : X -> Prog E1 R) (p2 : Prog E2 R)
  : eutt RR (Vis e1 k1) p2 ->
    exists e2 k2,
      RR _ e1 e2 /\
      (forall x, eutt RR (k1 x) (k2 x)) /\
      untaus1 (fun p => Vis e2 k2 = p) p2.
Proof.
  intros H. punfold H.
  remember (Vis e1 k1) as p1.
  revert e1 k1 Heqp1.
  induction H; intros.
  - discriminate.
  - pclearbot.
    inv Heqp1. injpair_; subst.
    exists e'. exists k'.
    split; [ assumption | ].
    split; [ assumption | ].
    constructor. reflexivity.
  - discriminate.
  - discriminate.
  - apply IHeuttF in Heqp1.
    destruct Heqp1 as (e2 & k2 & ? & ? & ?).
    exists e2. exists k2.
    split; [ assumption | ].
    split; [ assumption | ].
    constructor. auto.
Qed.



(***************)
(* BOILERPLATE *)



Lemma eutt_Noop_L_inv {M1 M2} (RR : IRel M1 M2) R
  : forall (p1 : Prog M1 R) (p2 : Prog M2 R),
    eutt RR (Noop p1) p2 ->
    eutt RR p1 p2.
Proof.
  pcofix self.
  intros p1 p2 H. remember (Noop p1) as Np1. revert dependent p1.
  punfold H. induction H.
  - discriminate.
  - discriminate.
  - pclearbot. injection 1. intros [].
    punfold H. pfold. constructor.
    eapply monotone_euttF; eauto.
    intros; eapply upaco2_mon_bot; eauto.
  - injection 1. intros []. pfold.
    eapply monotone_euttF; eauto.
    intros; eapply upaco2_mon_bot; eauto.
  - intros ? ?; subst p1. pfold. constructor.
    specialize (IHeuttF _ eq_refl). punfold IHeuttF.
Qed.

Lemma eutt_Ret_R_RR {M1 M2 M2'} (RR : IRel M1 M2) (RR' : IRel M1 M2') {R}
      (r : R) (p : Prog M1 R)
  : eutt RR p (Return r) -> eutt RR' p (Return r).
Proof.
  intros H; punfold H; pfold.
  remember (Return r). revert Heqp0.
  induction H; try (discriminate + constructor; auto).
  injection 1; intros; subst; constructor.
Qed.

Lemma eutt_Ret_L_RR {M1 M1' M2} (RR : IRel M1 M2) (RR' : IRel M1' M2) {R}
      (r : R) (p : Prog M2 R)
  : eutt RR (Return r) p -> eutt RR' (Return r) p.
Proof.
  intros H; punfold H; pfold.
  remember (Return r). revert Heqp0.
  induction H; try (discriminate + constructor; auto).
  injection 1; intros; subst; constructor.
Qed.
*)

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

(*
Lemma Proper_flattenProg {M1 M2 N1 N2}
      (RM : IRel M1 M2) (RN : IRel N1 N2)
      (f1 : forall R, M1 R -> Prog N1 R)
      (f2 : forall R, M2 R -> Prog N2 R)
      R
  : (RM ==> eutt RN)%isig f1 f2 ->
    forall (p1 : Prog M1 R) (p2 : Prog M2 R),
    eutt RM p1 p2 ->
    eutt RN (flattenProg f1 p1) (flattenProg f2 p2).
Proof.
  intros Hf.
  enough (forall (q1 : Prog N1 R) (q2 : Prog N2 R),
    flattenProg_bisim RM RN f1 f2 q1 q2 -> eutt RN q1 q2).
  { intros p1 p2 I; apply H; constructor; apply I. }
  pcofix self.
  intros q1 q2 [].
  - punfold H. induction H.
    + rewrite (frobProgId (_ f1 _ _)), (frobProgId (_ f2 _ _)).
      pfold; constructor.
    + rewrite (frobProgId (_ f1 _ _)), (frobProgId (_ f2 _ _)).
      cbn. pfold; constructor. right. apply self.
      pclearbot; constructor; auto.
    + rewrite (frobProgId (_ f1 _ _)), (frobProgId (_ f2 _ _)).
      cbn. pclearbot; pfold; constructor; right; apply self; constructor.
      auto.
    + rewrite (frobProgId (_ f1 _ _)).
      pfold. punfold IHeuttF.
      cbn. constructor. auto.
    + rewrite (frobProgId (_ f2 _ _)).
      pfold. punfold IHeuttF.
      cbn. constructor; auto.
  - punfold H0. induction H0.
    + rewrite (frobProgId (_ f1 _ _ _ _)), (frobProgId (_ f2 _ _ _ _)).
      cbn. pfold. constructor.
      right; apply self; constructor. auto.
    + rewrite (frobProgId (_ f1 _ _ _ _)), (frobProgId (_ f2 _ _ _ _)).
      cbn. pfold. constructor; auto.
      pclearbot. right. apply self; constructor; auto.
      apply H1.
    + rewrite (frobProgId (_ f1 _ _ _ _)), (frobProgId (_ f2 _ _ _ _)).
      cbn. pfold. constructor; auto.
      pclearbot. right. apply self; constructor; auto.
    + rewrite (frobProgId (_ f1 _ _ _ _)).
      cbn. punfold IHeuttF; pfold; constructor; auto.
    + rewrite (frobProgId (_ f2 _ _ _ _)).
      cbn. punfold IHeuttF; pfold; constructor; auto.
Qed.

*)

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

(*
Inductive all_eutt {M1 M2} (RR : IRel M1 M2)
  : list (sigT (Prog M1)) -> list (sigT (Prog M2)) -> Prop :=
| all_eutt_nil : all_eutt RR [] []
| all_eutt_cons T p1 p2 t1 t2 :
  eutt RR p1 p2 ->
  all_eutt RR t1 t2 ->
  all_eutt RR (existT _ T p1 :: t1) (existT _ T p2 :: t2)
.



Lemma eutt_ProgSteps {M} (o : Spec M) (Ret : Type) M2 {RR : IRel M M2}
      (s : State o) (x : Ret)
      (x0 : Prog M Ret)
  : eutt RR x0 (Return x) -> ProgSteps o Ret x0 s (Return x) s.
Proof.
  intros H; punfold H.
  remember (Return x) as p eqn:Hp.
  revert Hp; induction H; try discriminate.
  - injection 1; intros []. apply ProgStepsRefl.
  - intros I; apply IHeuttF in I.
    eapply ProgStepStepsImplSteps; [ constructor | eassumption ].
Qed.

Section FLATTENMAP.

Context {M M' I : Type -> Type}
  (impl : forall R : Type, M' R -> Prog I R)
  (f : forall R : Type, M R -> M' R) (R : Type).

Inductive _flattenMap_sim : Prog I R -> Prog I R -> Prop :=
| _flattenMap_Noop p q : _flattenMap_sim p q -> _flattenMap_sim (Noop p) (Noop q)
| _flattenMap_flatten p :
    _flattenMap_sim
      (flattenProg impl (mapProg f p))
      (flattenProg (fun (R0 : Type) (m : M R0) => impl R0 (f R0 m)) p)
| _flattenMap_bind S (p : Prog I S) (k : S -> _) :
    _flattenMap_sim
      (bindFlattenProg impl (fun x => mapProg f (k x)) p)
      (bindFlattenProg (fun _ m => impl _ (f _ m)) k p).

Lemma flattenMap (p : Prog M R)
  : eutt ieq
      (flattenProg impl (mapProg f p))
      (flattenProg (fun (R0 : Type) (m : M R0) => impl R0 (f R0 m)) p).
Proof.
  enough (J : forall p q, _flattenMap_sim p q -> eutt ieq p q).
  { apply J. constructor. }
  clear. pcofix SELF. intros p q; induction 1.
  - pfold; constructor; auto.
  - pfold.
    match goal with
    | [ |- _ ?t ?u ] => rewrite (frobProgId t), (frobProgId u)
    end.
    destruct p; cbn; constructor;
      right; apply SELF; constructor.
  - pfold.
    match goal with
    | [ |- _ ?t ?u ] => rewrite (frobProgId t), (frobProgId u)
    end.
    destruct p; cbn; constructor;
      try (right; apply SELF; constructor);
      try constructor.
Qed.

End FLATTENMAP.

*)