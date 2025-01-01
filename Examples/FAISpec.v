From LHL.Core Require Import
  Specs
  Traces
  Program.

From LHL.Util Require Import
  Tactics
  Util.

Variant FAISig : ESig :=
| FAI : FAISig nat.

Definition FAIState T : Type := nat * option (Name T).
Notation FAIIdle n := (n, None).
Notation FAIRan i n := (n, Some i).

Variant FAIStep {T} : FAIState T -> ThreadEvent T FAISig -> FAIState T -> Prop :=
| FAICall i n : FAIStep (FAIIdle n) (i, CallEv FAI) (FAIRan i n)
| FAIRet i n : FAIStep (FAIRan i n) (i, RetEv FAI n) (FAIIdle (S n)).

Require Import Coq.Program.Wf.
Require Import Lia.

Program Fixpoint faiSC {T} s
  (p : list (ThreadEvent T FAISig)) (n : nat) {measure (length p)}
: TransUtil.Steps FAIStep (FAIIdle n) p s ->
  SeqConsistent (fun _ : Name T => None) p
:= _.
Next Obligation.
Proof.
  ddestruct H. constructor.
  ddestruct H.
  eapply SCCall with
    (a':=fun j =>
      if i =? j then
        Some (existT _ _ FAI)
      else
        None).
  { easy. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  ddestruct H0. constructor.
  ddestruct H.
  eapply SCRet with
    (a':=fun _ => None).
  { now rewrite eqb_id. }
  { easy. }
  {
    unfold differ_pointwise.
    intros. now rewrite eqb_nid.
  }
  eapply faiSC.
  { simpl. lia. }
  { exact H0. }
Qed.

Program Definition faiSpec {T} : Spec T FAISig := {|
  State := FAIState T;
  Step := FAIStep;
  Init := FAIIdle 0
|}.

Next Obligation.
Proof.
  eapply faiSC.
  exact H.
Qed.