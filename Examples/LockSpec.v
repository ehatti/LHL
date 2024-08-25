From LHL.Core Require Import
  Program
  Specs
  UBLayer.

From LHL.Util Require Import
  Util
  Tactics
  TransUtil.

From Coq Require Import
  Program.Equality.

Require Import List.
Import ListNotations.

Variant LockSig : ESig :=
| Acq : LockSig unit
| Rel : LockSig unit.

Variant LockState {T} :=
| LockDef (owner : option T) (m : option (LockSig unit)).

Definition LockUnowned {T} := @LockDef T None None.
Definition LockAcqRan {T} i := @LockDef T (Some i) (Some Acq).
Definition LockRelRan {T} i := @LockDef T (Some i) (Some Rel).
Definition LockOwned {T} i := @LockDef T (Some i) None.

Variant LockStep {T} : LockState -> ThreadEvent T LockSig -> LockState -> Prop :=
| LockCallAcq i : LockStep LockUnowned (i, CallEv Acq) (LockAcqRan i)
| LockRetAcq i : LockStep (LockAcqRan i) (i, RetEv Acq tt) (LockOwned i)
| LockCallRel i : LockStep (LockOwned i) (i, CallEv Rel) (LockRelRan i)
| LockRetRel i : LockStep (LockRelRan i) (i, RetEv Rel tt) LockUnowned.

Definition LockActiveMap {T} : ActiveF (@LockStep T) := 
  fun s => match s with
  | LockDef None _ => fun _ => None
  | LockDef (Some i) (Some Acq) => 
      fun j => if (eqb i j) then Some (existT _ _ Acq) else None
  | LockDef (Some i) (Some Rel) =>
      fun j => if (eqb i j) then Some (existT _ _ Rel) else None
  | _ => fun _ => None
  end.

Lemma LockStepActiveMapStep {T} :
  forall s1 s2 (te: @ThreadEvent T LockSig), LockStep s1 te s2 ->
    ActiveMapStep (LockActiveMap s1) te (LockActiveMap s2).
Proof.
  intros.
  inversion H; subst.
  + econstructor; unfold LockActiveMap; simpl.
    { reflexivity. }
    { rewrite eqb_id. reflexivity. }
    { apply differ_pointwise_trivial. }
  + econstructor; unfold LockActiveMap; simpl.
    { rewrite eqb_id. reflexivity. }
    { reflexivity. }
    { unfold differ_pointwise. intros. rewrite eqb_nid; easy. }
  + econstructor; unfold LockActiveMap; simpl.
    { reflexivity. }
    { rewrite eqb_id. reflexivity. }
    { apply differ_pointwise_trivial. }
  + econstructor; unfold LockActiveMap; simpl.
    { rewrite eqb_id. reflexivity. }
    { reflexivity. }
    { unfold differ_pointwise. intros. rewrite eqb_nid; easy. }
Qed.

Program Definition lockSpec {T} : Spec T LockSig := {|
  State := LockState;
  Step := LockStep;
  Init := LockUnowned
|}.

Next Obligation.
  intros.
  change (fun _ : Name T => None) with ((@LockActiveMap T) LockUnowned).
  generalize dependent (@LockUnowned (Name T)).
  induction p; intros.
  + constructor.
  + inversion H; subst.
    specialize (IHp st'' H4).
    pose proof LockStepActiveMapStep l st'' a H2.
    apply (ActiveMapStepSeqcons _ _ _ _ H0 IHp).
Qed.

Global Lemma LockActiveMapSound {T} : @acf_sound T LockSig lockSpec LockActiveMap.
Proof.
  split.
  + reflexivity.
  + intros.
    apply LockStepActiveMapStep, H.
Qed.


Definition lockClientSpec {T} : forall A, LockSig A -> Name T -> LockState -> Prop :=
  fun A m i s => 
    match m with
    | Acq => (s <> LockOwned i) /\ (s <> LockAcqRan i) /\ (s <> LockRelRan i)
    | Rel => s = LockOwned i
    end.