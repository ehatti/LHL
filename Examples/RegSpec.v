From LHL.Core Require Import
  Program
  Specs.

From LHL.Util Require Import
  TransUtil
  Tactics
  Util.

Variant RegSig {A} : ESig :=
| Write (x : A) : RegSig unit
| Read : RegSig A.
Arguments RegSig : clear implicits.

Variant RegState {T A} :=
| RegDef (x : A) (m : option (Name T * {R & RegSig A R})).
Arguments RegState : clear implicits.

Arguments existT {A} {P}.

Variant RegStep {T A} : RegState T A -> ThreadEvent T (RegSig A) -> RegState T A -> Prop :=
| RegCall i x R (m : RegSig A R) :
  RegStep (RegDef x None)
          (i, CallEv m)
          (RegDef x (Some (i, existT _ m)))
| RetRetWrite i x y :
  RegStep (RegDef x (Some (i, existT _ (Write y))))
          (i, RetEv (Write y) tt)
          (RegDef y None)
| RegRetRead i x :
  RegStep (RegDef x (Some (i, existT _ Read)))
          (i, RetEv Read x)
          (RegDef x None).

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

Require Import Coq.Logic.FunctionalExtensionality.

Lemma regSeqCons {T A} init :
  forall (p : list (ThreadEvent T (RegSig A))) (s : RegState T A),
    Steps RegStep (RegDef init None) p s ->
    SeqConsistent (fun _ : Name T => None) p.
intros.
revert H.
generalize dependent init.
change (
  forall init,
  Steps RegStep (RegDef init None) p s -> SeqConsistent (fun _ : Name T => None) p
) with (
  (fun p =>
    forall init,
    Steps RegStep (RegDef init None) p s -> SeqConsistent (fun _ : Name T => None) p
  ) p
).
apply double_ind; intros.
{ constructor. }
{
  ddestruct H.
  ddestruct H.
  eapply SCCall with
    (a':=fun j =>
      if i =? j then
        Some (existT _ m)
      else
        (fun _ : Name T => None) j).
  { easy. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  { constructor. }
}
{
  ddestruct H0. ddestruct H0.
  eapply SCCall with
    (a':=fun j =>
      if i =? j then
        Some (existT _ m)
      else
        (fun _ : Name T => None) j).
  { easy. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  ddestruct H1. ddestruct H0.
  eapply SCRet with
    (a':=fun j =>
      if i =? j then
        None
      else if i =? j then
        Some (existT _ (Write y))
      else
        (fun _ : Name T => None) j).
  { now rewrite eqb_id. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  assert (
    (fun j : Name T =>
      if i =? j then
        None
      else if i =? j then
        Some (existT (P:=RegSig A) unit (Write y))
      else None
    ) = (fun _ => None)
  ).
  {
    extensionality j.
    dec_eq_nats i j.
    { now rewrite eqb_id. }
    { now rewrite eqb_nid. }
  }
  rewrite H0 at 1.
  eapply H. exact H1.
  eapply SCRet with
    (a':=fun j =>
      if i =? j then
        None
      else if i =? j then
        Some (existT _ Read)
      else
        (fun _ : Name T => None) j).
  { now rewrite eqb_id. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  assert (
    (fun j : Name T =>
      if i =? j then
        None
      else if i =? j then
        Some (existT (P:=RegSig R) _ Read)
      else None
    ) = (fun _ => None)
  ).
  {
    extensionality j.
    dec_eq_nats i j.
    { now rewrite eqb_id. }
    { now rewrite eqb_nid. }
  }
  rewrite H0 at 1.
  eapply H. exact H1.
}
Qed.

Definition regSpec {T A} (init : A)
: Spec T (RegSig A) := {|
  State := RegState T A;
  Step := RegStep;
  Init := RegDef init None;
  seq_cons := regSeqCons init
|}.