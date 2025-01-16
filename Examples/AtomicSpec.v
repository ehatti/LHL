From LHL Require Import
  Program
  Specs
  TransUtil
  Util.

Require Import Coq.Unicode.Utf8.
Require Import Coq.Logic.FunctionalExtensionality.

Record AtomicSpec {T : nat} {E : ESig} := {
  AState : Type;
  AStep : AState -> Name T * {R & prod (E R) R} -> AState -> Prop;
  AInit : AState
}.
Arguments AtomicSpec : clear implicits.

Record AtomicState {T : nat} {E : ESig} {A : Type} := MkAtom {
  atom_val : A;
  atom_pend : option (Name T * sigT E)
}.
Arguments AtomicState : clear implicits.
Arguments MkAtom {T E A}.

Variant AtomicStep {T A E} {Step : A -> Name T * {R & prod (E R) R} -> A -> Prop} :
  AtomicState T E A -> ThreadEvent T E -> AtomicState T E A -> Prop :=
| AtomicCall s i R m :
    AtomicStep (MkAtom s None) (i, CallEv m) (MkAtom s (Some (i, existT E R m)))
| AtomicRet s i R m v t :
    Step s (i, existT _ R (m, v)) t ->
    AtomicStep (MkAtom s (Some (i, existT E R m))) (i, RetEv m v) (MkAtom t None).
Arguments AtomicStep {T A E} Step.

Require Import Coq.Program.Wf.
Require Import Lia.

Program Fixpoint atomicSC {T E} {V : AtomicSpec T E}
  (p : list (ThreadEvent T E)) {measure (length p)}
:
  ∀ s t,
    Steps (AtomicStep V.(AStep)) (MkAtom s None) p t ->
    SeqConsistent (fun _ => None) p
:= _.
Next Obligation.
Proof. 
  ddestruct H. constructor.
  ddestruct H.
  eapply SCCall with
    (a':=λ j,
      if i =? j then
        Some (existT _ _ m)
      else
        None).
  { easy. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  ddestruct H0. constructor.
  ddestruct H.
  eapply SCRet with
    (a':=λ _, None).
  { now rewrite eqb_id. }
  { easy. }
  {
    unfold differ_pointwise.
    intros. now rewrite eqb_nid.
  }
  eapply atomicSC.
  { simpl. lia. }
  { exact H0. }
Qed.

Program Definition LiftAtomic {T E} (V : AtomicSpec T E) : Spec T E := {|
  State := AtomicState T E V.(AState);
  Step := AtomicStep V.(AStep);
  Init := (MkAtom V.(AInit) None)
|}.

Next Obligation.
Proof.
  eapply atomicSC.
  { exact H. }
Qed.

Record RacyState {T : nat} {E : ESig} {A : Type} := MkRacy {
  racy_val : option A;
  racy_pend : set (Name T * sigT E)
}.
Arguments RacyState : clear implicits.
Arguments MkRacy {T E A}.

Notation "[ i ]" := (insert i emp).
Notation "[ i , j ]" := (insert i (insert j emp)).

Variant RacyStep {T A E} {Step : A -> Name T * {R & prod (E R) R} -> A -> Prop} :
  RacyState T E A -> ThreadEvent T E -> RacyState T E A -> Prop :=
| RacyCall s i R m p :
    RacyStep
      (MkRacy s p)
      (i, CallEv m)
      (MkRacy s (insert (i, existT E R m) p))
| RacyDefRet s i R m v t :
    Step s (i, existT _ R (m, v)) t ->
    RacyStep
      (MkRacy (Some s) [(i, existT E R m)])
      (i, RetEv m v)
      (MkRacy (Some t) emp)
| RaceCall s i j R1 m1 R2 m2 :
    i ≠ j ->
    RacyStep
      (MkRacy (Some s) [(i, existT E R1 m1)])
      (j, CallEv m2)
      (MkRacy None [(i, existT E R1 m1), (j, existT E R2 m2)])
(* | RaceRet i j R1 m1 v R2 m2 :
    i ≠ j ->
    RacyStep
      (MkRacy None [(i, existT E R1 m1), (j, existT E R2 m2)])
      (i, RetEv m1 v)
      (MkRacy None [(j, existT E R2 m2)])
| RacyUBRet i R m v :
    RacyStep
      (MkRacy None [(i, existT E R m)])
      (i, RetEv m v)
      (MkRacy None emp) *)
| RaceRet i R m v p :
  RacyStep
    (MkRacy None (insert (i, existT _ R m) p))
    (i, RetEv m v)
    (MkRacy None p)
.
Arguments RacyStep {T A E} Step.

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


Program Fixpoint racySC {T E} {V : AtomicSpec T E}
  (p : list (ThreadEvent T E)) {measure (length p)}
:
  ∀ s t,
    Steps (RacyStep V.(AStep)) (MkRacy s emp) p t ->
    SeqConsistent (fun _ => None) p
:= _.
Next Obligation.
Proof.
  ddestruct H. constructor. ddestruct H.
  all: try now apply disj_cons in x.
  eapply SCCall with
    (a':=λ j,
      if i =? j then
        Some (existT _ _ m)
      else
        None).
  { easy. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  ddestruct H0. constructor.
  ddestruct H.
  { symmetry in x. now apply disj_cons in x. }
  {
    apply insert_cong1 in x.
    ddestruct x.
    eapply SCRet with
      (a':=λ _, None).
    { now rewrite eqb_id. }
    { easy. }
    {
      unfold differ_pointwise.
      intros. now rewrite eqb_nid.
    }
    eapply racySC.
    { simpl. lia. }
    { exact H0. }
  }
  {
    apply insert_cong1 in x.
    ddestruct x.
    eapply SCRet with
      (a':=λ _, None).
    { now rewrite eqb_id. }
    { easy. }
    {
      unfold differ_pointwise.
      intros. now rewrite eqb_nid.
    }
    eapply racySC.
    { simpl. lia. }
    { exact H0. }
  }
  {
    apply insert_cong1 in x.
    ddestruct x.
    eapply SCCall with
      (a':=λ k,
        if j =? k then
          Some (existT _ _ m2)
        else if i =? k then
          Some (existT _ _ m)
        else
          None).
    { now rewrite eqb_nid. }
    { now rewrite eqb_id. }
    { apply differ_pointwise_trivial. }
    ddestruct H0. constructor.
    ddestruct H0.
    {
      clear - x. exfalso.
      unfold emp in x.
      eapply equal_f with
        (x:=_) in x.
      rewrite x.
      now left.
    }
    {
      apply contract_set in x.
      destruct x.
      ddestruct H0.
      ddestruct H2.
      easy.
    }
    {
      apply insert_cong2 in x.
      destruct x as [[Heq1 Heq2] | [Heq1 Heq2]];
      ddestruct Heq1; ddestruct Heq2.
      {
        eapply SCRet with
          (a':=λ k,
            if j =? k then
              Some (existT _ _ m2)
            else
              None).
        { now rewrite eqb_id, eqb_nid. }
        { now rewrite eqb_nid. }
        {
          unfold differ_pointwise. intros.
          now rewrite eqb_nid with (n:=i) (m:=j0).
        }
        ddestruct H1. constructor.
        ddestruct H1.
        { symmetry in x. now apply disj_cons in x. }
        {
          apply insert_cong1 in x.
          ddestruct x.
          eapply SCRet with
            (a':=λ _, None).
          { now rewrite eqb_id. }
          { easy. }
          {
            unfold differ_pointwise.
            intros. now rewrite eqb_nid.
          }
          eapply racySC.
          { simpl. lia. }
          { exact H2. }
        }
        {
          symmetry in x.
          apply contract_set in x.
          destruct x.
          ddestruct H3.
          ddestruct H4.
          easy.
        }
      }
      {
        eapply SCRet with
          (a':=λ k,
            if i =? k then
              Some (existT _ _ m)
            else
              None).
        { now rewrite eqb_id. }
        { now rewrite eqb_nid. }
        {
          unfold differ_pointwise. intros.
          now rewrite eqb_nid with (n:=j) (m:=j0).
        }
        ddestruct H1. constructor.
        ddestruct H1.
        { symmetry in x. now apply disj_cons in x. }
        {
          apply insert_cong1 in x.
          ddestruct x.
          eapply SCRet with
            (a':=λ _, None).
          { now rewrite eqb_id. }
          { easy. }
          {
            unfold differ_pointwise.
            intros. now rewrite eqb_nid.
          }
          eapply racySC.
          { simpl. lia. }
          { exact H2. }
        }
        {
          symmetry in x.
          apply contract_set in x.
          destruct x.
          ddestruct H3.
          ddestruct H4.
          easy.
        }
      }
      {
        unfold not. intros.
        now ddestruct H2.
      }
    }
  }
  {
    symmetry in x.
    apply contract_set in x.
    destruct x.
    ddestruct H1.
    ddestruct H2.
    easy.
  }
Qed.

Program Definition LiftRacy {T E} (V : AtomicSpec T E) : Spec T E := {|
  State := RacyState T E V.(AState);
  Step := RacyStep V.(AStep);
  Init := (MkRacy (Some V.(AInit)) emp)
|}.

Next Obligation.
Proof.
  eapply racySC.
  { exact H. }
Qed.