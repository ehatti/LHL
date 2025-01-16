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

Record LockState {T} := LockDef {
  lock_owner : option (option (Name T));
  lock_pend : option (Name T * LockSig unit)
}.
Arguments LockDef {T}.

Notation LockUnowned := (LockDef (Some None) None).
Notation LockAcqRan i := (LockDef (Some (Some i)) (Some (i, Acq))).
Notation LockRelRan i := (LockDef (Some (Some i)) (Some (i, Rel))).
Notation LockOwned i := (LockDef (Some (Some i)) None).
Notation LockUB m := (LockDef None m).

Variant LockStep {T} : LockState -> ThreadEvent T LockSig -> LockState -> Prop :=
| LockCallAcq i : LockStep LockUnowned (i, CallEv Acq) (LockAcqRan i)
| LockRetAcq i : LockStep (LockAcqRan i) (i, RetEv Acq tt) (LockOwned i)
| LockCallRel i : LockStep (LockOwned i) (i, CallEv Rel) (LockRelRan i)
| LockRetRel i : LockStep (LockRelRan i) (i, RetEv Rel tt) LockUnowned
| LockCallUBAcq i : LockStep (LockOwned i) (i, CallEv Acq) (LockUB (Some (i, Acq)))
| LockCallRelDUB i : LockStep LockUnowned (i, CallEv Rel) (LockUB (Some (i, Rel)))
| LockCallRelOUB i j : i <> j -> LockStep (LockOwned j) (i, CallEv Rel) (LockUB (Some (i, Rel)))
| LockCallUB i m : LockStep (LockUB None) (i, CallEv m) (LockUB (Some (i, m)))
| LockRetUB i m v : LockStep (LockUB (Some (i, m))) (i, RetEv m v) (LockUB None).

Require Import Lia.

Program Fixpoint lockSC {T}
  (p : list (ThreadEvent T LockSig)) s t {measure (length p)}
: (s = LockUnowned \/ s = LockUB None \/ exists i, s = LockOwned i) ->
  Steps LockStep s p t ->
  SeqConsistent (fun _ => None) p
:= _.
Next Obligation.
Proof.
  destruct H; subst.
  {
    ddestruct H0. constructor.
    ddestruct H.
    eapply SCCall with
      (a':=fun j =>
        if i =? j then
          Some (existT _ _ Acq)
        else
          None).
    { easy. }
    { now rewrite eqb_id. }
    { apply differ_pointwise_trivial. }
    ddestruct H0. constructor.
    {
      ddestruct H.
      eapply SCRet with
        (a':=fun _ => None).
      { now rewrite eqb_id. }
      { easy. }
      {
        unfold differ_pointwise.
        intros. now rewrite eqb_nid.
      }
      eapply lockSC.
      { simpl. lia. }
      2: exact H0.
      { right. right. now exists i. }
    }
    {
      eapply SCCall with
        (a':=fun j =>
          if i =? j then
            Some (existT _ _ Rel)
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
      eapply lockSC.
      { simpl. lia. }
      2: exact H0.
      { right. now left. }
    }
  }
  destruct H; destruct_all; subst.
  {
    ddestruct H0. constructor.
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
    eapply SCRet with
      (a':=fun _ => None).
    { now rewrite eqb_id. }
    { easy. }
    {
      unfold differ_pointwise.
      intros. now rewrite eqb_nid.
    }
    eapply lockSC.
    { simpl. lia. }
    2: exact H0.
    { right. now left. }
  }
  {
    rename x into i.
    ddestruct H0. constructor.
    ddestruct H.
    eapply SCCall with
      (a':=fun j =>
        if i =? j then
          Some (existT _ _ Rel)
        else
          None).
    { easy. }
    { now rewrite eqb_id. }
    { apply differ_pointwise_trivial. }
    ddestruct H0. constructor.
    {
      ddestruct H.
      eapply SCRet with
        (a':=fun _ => None).
      { now rewrite eqb_id. }
      { easy. }
      {
        unfold differ_pointwise.
        intros. now rewrite eqb_nid.
      }
      eapply lockSC.
      { simpl. lia. }
      2: exact H0.
      { now left. }
    }
    {
      eapply SCCall with
        (a':=fun k =>
          if i =? k then
            Some (existT _ _ Acq)
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
      eapply lockSC.
      { simpl. lia. }
      2: exact H0.
      { right. now left. }
    }
    {
      eapply SCCall with
        (a':=fun j =>
          if i0 =? j then
            Some (existT _ _ Rel)
          else
            None).
      { easy. }
      { now rewrite eqb_id. }
      { apply differ_pointwise_trivial. }
      ddestruct H0. constructor.
      ddestruct H0.
      eapply SCRet with
        (a':=fun _ => None).
      { now rewrite eqb_id. }
      { easy. }
      {
        unfold differ_pointwise.
        intros. now rewrite eqb_nid.
      }
      eapply lockSC.
      { simpl. lia. }
      2: exact H1.
      { right. now left. }
    }
  }
Qed.

Program Definition lockSpec {T} : Spec T LockSig := {|
  State := LockState;
  Init := LockUnowned;
  Step := LockStep
|}.

Next Obligation.
Proof.
  eapply lockSC.
  { now left. }
  { exact H. }
Qed.

(* Definition LockActiveMap {T} : ActiveF (@LockStep T) := 
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


Definition lockClientSpec {T} : ClientSpec T LockSig LockState :=
  fun '(i, e) s =>
    match e with
    | CallEv Acq => s = LockUnowned
    | CallEv Rel => s = LockOwned i
    | _ => True
    end. *)