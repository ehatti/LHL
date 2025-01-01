From LHL.Core Require Import
  Program
  Specs.

From LHL.Util Require Import
  TransUtil
  Tactics
  Util.

From LHL.Examples Require Import
  Counter.CounterSig.

Variant RCntPend {T} :=
| MetPend {A} (i : Name T) (m : CounterSig A)
| RacePend (is : set (Name T)).
Arguments RCntPend : clear implicits.

Notation "[ i ]" := (insert i emp).
Notation "[ i , j ]" := (insert i (insert j emp)).

Record RCntState {T} := RCntSt {
  rcnt_num : option nat;
  rcnt_pend : option (RCntPend T)
}.
Arguments RCntState : clear implicits.
Arguments RCntSt {T}.

Notation RCntIdle s := (RCntSt s None).
Notation RCntRan s i m := (RCntSt s (Some (MetPend i m))).

Notation RCntDefIdle n := (RCntSt (Some n) None).
Notation RCntDefRan n i m := (RCntSt (Some n) (Some (MetPend i m))).

Notation RCntUBIdle := (RCntSt None None).
Notation RCntUBRan i m := (RCntSt None (Some (MetPend i m))).

Notation RCntRace s := (RCntSt None (Some (RacePend s))).

Variant RCntStep {T} : RCntState T -> ThreadEvent T CounterSig -> RCntState T -> Prop :=
| RCntCall i A (m : CounterSig A) s :
  RCntStep (RCntIdle s) (i, CallEv m) (RCntRan s i m)
| RCntRetGet i n :
  RCntStep (RCntDefRan n i Get) (i, RetEv Get n) (RCntDefIdle n)
| RCntRetInc i n :
  RCntStep (RCntDefRan n i Inc) (i, RetEv Inc tt) (RCntDefIdle (S n))
| RCntCallRace i j s :
  i <> j ->
  RCntStep (RCntDefRan s i Inc) (j, CallEv Inc) (RCntRace [i, j])
| RCntRet1Race i j :
  i <> j ->
  RCntStep (RCntRace [i, j]) (i, RetEv Inc tt) (RCntRace [j])
| RCntRet2Race j :
  RCntStep (RCntRace [j]) (j, RetEv Inc tt) RCntUBIdle
| RCntRetUB i A (m : CounterSig A) v :
  RCntStep (RCntUBRan i m) (i, RetEv m v) RCntUBIdle.

Require Import Coq.Program.Wf.
Require Import Coq.Logic.Classical_Prop.
Require Import Lia.
Require Import List.

Lemma dpt_sym {A B} {f g : A -> B} i :
  differ_pointwise f g i ->
  differ_pointwise g f i.
Proof.
  unfold differ_pointwise.
  intros. now rewrite H.
Qed.

Lemma tollens P Q :
  (P -> Q) ->
  (~Q -> ~P).
Proof.
  unfold not. intros.
  now apply H0, H.
Qed.

Require Import Coq.Logic.FunctionalExtensionality.

Lemma contract_set {A} :
  forall x y z : A,
  [x] = [y, z] ->
  x = y /\ x = z.
Proof.
  intros.
  unfold insert in *.
  assert (H' := H).
  apply equal_f with (x:=y) in H.
  assert (x = y \/ emp y).
  {
    rewrite H.
    now left.
  }
  destruct H0. 2: easy.
  subst. split. easy.
  clear H.
  apply equal_f with (x:=z) in H'.
  cut (y = z \/ emp z).
  {
    intros. now destruct H.
  }
  rewrite H'.
  right. now left.
Qed.

Program Fixpoint rcntSC {T}
  (p : list (ThreadEvent T CounterSig)) s t {measure (length p)}
: Steps RCntStep (RCntIdle s) p t ->
  SeqConsistent (fun _ => None) p
:= _.
Next Obligation.
Proof. 
  ddestruct H. constructor.
  ddestruct H.
  eapply SCCall with
    (a':=fun j =>
      if i =? j then
        Some (existT _ _ m)
      else
        None).
  { easy. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  ddestruct H0. constructor.
  ddestruct H.
  {
    eapply SCRet with
      (a':=fun _ => None).
    { now rewrite eqb_id. }
    { easy. }
    {
      unfold differ_pointwise.
      intros. now rewrite eqb_nid.
    }
    eapply rcntSC.
    { simpl. lia. }
    { exact H0. }
  }
  {
    eapply SCRet with
      (a':=fun _ => None).
    { now rewrite eqb_id. }
    { easy. }
    {
      unfold differ_pointwise.
      intros. now rewrite eqb_nid.
    }
    eapply rcntSC.
    { simpl. lia. }
    { exact H0. }
  }
  {
    eapply SCCall with
      (a':=fun k =>
        if j =? k then
          Some (existT _ _ Inc)
        else if i =? k then
          Some (existT _ _ Inc)
        else
          None).
    { now rewrite eqb_nid. }
    { now rewrite eqb_id. }
    { apply differ_pointwise_trivial. }
    {
      ddestruct H0. constructor.
      ddestruct H0.
      2:{
        apply contract_set in x.
        destruct x. subst. easy.
      }
      apply insert_cong2 in x; auto.
      destruct x; destruct H2;
      subst.
      {
        eapply SCRet with
          (a':=fun k =>
            if j =? k then
              Some (existT _ _ Inc)
            else
              None).
        { now rewrite eqb_id, eqb_nid. }
        { now rewrite eqb_nid. }
        {
          unfold differ_pointwise.
          intros. now rewrite eqb_nid with
            (n:=i) (m:=j0).
        }
        ddestruct H1. constructor.
        ddestruct H1.
        {
          symmetry in x.
          apply contract_set in x.
          destruct x. subst. easy.
        }
        apply insert_cong1 in x.
        subst.
        eapply SCRet with
          (a':=fun _ => None).
        { now rewrite eqb_id. }
        { easy. }
        {
          unfold differ_pointwise.
          intros. now rewrite eqb_nid.
        }
        eapply rcntSC.
        { simpl. lia. }
        { exact H2. }
      }
      {
        eapply SCRet with
          (a':=fun k =>
            if i =? k then
              Some (existT _ _ Inc)
            else
              None).
        { now rewrite eqb_id. }
        { now rewrite eqb_nid. }
        {
          unfold differ_pointwise.
          intros. now rewrite eqb_nid with
            (n:=j) (m:=j0).
        }
        ddestruct H1. constructor.
        ddestruct H1.
        {
          symmetry in x.
          apply contract_set in x.
          destruct x. subst. easy.
        }
        apply insert_cong1 in x.
        subst.
        eapply SCRet with
          (a':=fun _ => None).
        { now rewrite eqb_id. }
        { easy. }
        {
          unfold differ_pointwise.
          intros. now rewrite eqb_nid.
        }
        eapply rcntSC.
        { simpl. lia. }
        { exact H2. }
      }
    }
  }
  {
    eapply SCRet with
      (a':=fun _ => None).
    { now rewrite eqb_id. }
    { easy. }
    {
      unfold differ_pointwise.
      intros. now rewrite eqb_nid.
    }
    eapply rcntSC.
    { simpl. lia. }
    { exact H0. }
  }
Qed.

Program Definition rcntSpec {T} : Spec T CounterSig := {|
  State := RCntState T;
  Init := RCntDefIdle 0;
  Step := RCntStep
|}.

Next Obligation.
Proof.
  eapply rcntSC.
  exact H.
Qed.