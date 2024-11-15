From LHL.Core Require Import
  Program
  Specs
  Logic.

From LHL.Examples Require Import
  ArraySpec.

From LHL.Util Require Import
  Tactics
  TransUtil
  Util.

Variant RandSig : ESig :=
| Random (k : nat) : RandSig (Index k).

Definition RandState T := ActiveMap T RandSig.

Variant RandStep {T} : RandState T -> ThreadEvent T RandSig -> RandState T -> Prop :=
| CallRand i m k : RandStep
    (fun j => if i =? j then None else m j)
    (i, CallEv (Random k))
    (fun j => if i =? j then Some (existT _ _ (Random k)) else m j)
| RetRand i m k n : True -> RandStep
    (fun j => if i =? j then Some (existT _ _ (Random k)) else m j)
    (i, RetEv (Random k) n)
    (fun j => if i =? j then None else m j).

Program Definition randSpec {T} : Spec T RandSig := {|
  State := RandState T;
  Step := RandStep;
  Init _ := None
|}.

Next Obligation.
generalize dependent (fun _ : Name T => @None {A & RandSig A}).
intros. induction H. constructor.
ddestruct H.
{
  eapply SCCall with
    (a':=fun j =>
      if i =? j then
        Some (existT _ _ (Random k))
      else
        m j).
  { now rewrite eqb_id. }
  { now rewrite eqb_id. }
  {
    unfold differ_pointwise. intros.
    now rewrite eqb_nid.
  }
  { easy. }
}
{
  eapply SCRet with
    (a':=fun j =>
      if i =? j then
        None
      else
        m j).
  { now rewrite eqb_id. }
  { now rewrite eqb_id. }
  {
    unfold differ_pointwise. intros.
    now rewrite eqb_nid.
  }
  { easy. }
}
Qed.