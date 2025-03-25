From LHL.Core Require Import
  Program
  Specs
  Logic
  LogicFacts
  Traces
  ProgramRules.

From LHL.Util Require Import
  Util.

Variant CASSig {A} : ESig :=
| CAS (v : option A) (v' : option A) : CASSig bool
| Get : CASSig (option A).
Arguments CASSig : clear implicits.

Record CASPend {T A} := MkCASPend {
  CASThread : Name T;
  CASRetTy : Type;
  CASName : CASSig A CASRetTy
}.
Arguments CASPend : clear implicits.
Arguments MkCASPend {T A} _ {_}.

Variant CASState {T A} :=
| CASDef (v : option A) (m : option (CASPend T A)). (* currently value and pending call *)
Arguments CASState : clear implicits.

Definition eval_cas {T A} (st : CASState T A) : option A := 
  match st with
  | CASDef v _ => v
  end.


Variant CASStep {T A} : CASState T A -> ThreadEvent T (CASSig A) -> CASState T A -> Prop :=
| CASCallCAS i a e n :
    CASStep
      (CASDef a None)
      (i, CallEv (CAS e n))
      (CASDef a (Some (MkCASPend i (CAS e n))))
| CASSucc i a e n :
    a = e ->
    CASStep
      (CASDef a (Some (MkCASPend i (CAS e n))))
      (i, RetEv (CAS e n) true)
      (CASDef n None)
| CASFail i a e n :
    a <> e ->
    CASStep
      (CASDef a (Some (MkCASPend i (CAS e n))))
      (i, RetEv (CAS e n) false)
      (CASDef a None)
| CASCallGet i a :
    CASStep
      (CASDef a None)
      (i, CallEv Get)
      (CASDef a (Some (MkCASPend i Get)))
| CASRetGet i a :
    CASStep
      (CASDef a (Some (MkCASPend i Get)))
      (i, RetEv Get a)
      (CASDef a None).

Require Import Coq.Lists.List.

Import ListNotations.

Lemma double_ind {A} :
  forall (P : list A -> Prop),
  P [] ->
  (forall x, P [x]) ->
  (forall x y xs, P xs -> P (x :: y :: xs)) ->
  forall xs,
  P xs.
intros.
generalize dependent xs.
fix rec 1.
intros.
destruct xs.
{ apply H. }
destruct xs.
{ apply H0. }
{
  apply H1.
  apply rec.
}
Qed.

Lemma casSeqCons {T A} :
  forall (p : list (ThreadEvent T (CASSig A))) (s : CASState T A),
    TransUtil.Steps CASStep (CASDef None None) p s ->
    SeqConsistent (fun _ : Name T => None) p.
intros.
generalize dependent (@None A).
apply double_ind with
  (P:=fun p =>
    forall o,
      TransUtil.Steps CASStep (CASDef o None) p s ->
      SeqConsistent (fun _ => None) p);
intros.
{
  constructor.
}
{
  ddestruct H.
  ddestruct H.
  eapply SCCall with
    (a':=fun j =>
      if i =? j then
        Some (existT _ _ _)
      else
        None).
  { easy. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  { constructor. }
  eapply SCCall with
    (a':=fun j =>
      if i =? j then
        Some (existT _ _ _)
      else
        None).
  { easy. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  { constructor. }
}
ddestruct H0. ddestruct H1.
ddestruct H0.
{
  ddestruct H1.
  eapply SCCall with
    (a':=fun j =>
      if i =? j then
        Some (existT _ _ _)
      else
        None).
  { easy. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  remember (CAS o n).
  move Heqc at bottom.
  {
    ddestruct Heqc.
    eapply SCRet with
      (a':=fun j => None).
    { now rewrite eqb_id. }
    { easy. }
    {
      unfold differ_pointwise.
      intros. now rewrite eqb_nid.
    }
    {
      eapply H.
      exact H2.
    }
  }
  eapply SCCall with
    (a':=fun j =>
      if i =? j then
        Some (existT _ _ _)
      else
        None).
  { easy. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  remember (CAS o n).
  move Heqc at bottom.
  {
    ddestruct Heqc.
    eapply SCRet with
      (a':=fun j => None).
    { now rewrite eqb_id. }
    { easy. }
    {
      unfold differ_pointwise.
      intros. now rewrite eqb_nid.
    }
    {
      eapply H.
      exact H2.
    }
  }
}
{
  ddestruct H1.
  eapply SCCall with
    (a':=fun j =>
      if i =? j then
        Some (existT _ _ _)
      else
        None).
  { easy. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  remember (Get (A:=A)).
  move Heqc at bottom.
  {
    ddestruct Heqc.
    eapply SCRet with
      (a':=fun j => None).
    { now rewrite eqb_id. }
    { easy. }
    {
      unfold differ_pointwise.
      intros. now rewrite eqb_nid.
    }
    {
      eapply H.
      exact H2.
    }
  }
}
Qed.

Definition casSpec {T A} : Spec T (CASSig A) := {|
  State := CASState T A;
  Step := CASStep;
  Init := CASDef None None;
  seq_cons := casSeqCons
|}.