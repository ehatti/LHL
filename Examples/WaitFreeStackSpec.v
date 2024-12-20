From LHL.Core Require Import
  Program
  Specs
  Logic.

From LHL.Util Require Import
  Tactics
  TransUtil
  Util.

Variant StkRet {A} :=
| PASS (v : A)
| FAIL.
Arguments StkRet : clear implicits.

Variant WaitFreeStackSig {A} : ESig :=
| WFPush (v : A) : WaitFreeStackSig (StkRet unit)
| WFPop : WaitFreeStackSig (StkRet (option A)).
Arguments WaitFreeStackSig : clear implicits.

Record WaitFreeStackPend {T A} := MkWFSPend {
  StkRetTy : Type;
  StkName : Name T;
  StkCall : WaitFreeStackSig A StkRetTy
}.
Arguments WaitFreeStackPend : clear implicits.
Arguments MkWFSPend {T A StkRetTy}.

Definition WFSPend T A:=
  option (option (WaitFreeStackPend T A) * WaitFreeStackPend T A).

Notation NoPend :=
  (None : WFSPend _ _).
Notation PassPend i m :=
  (Some (None, MkWFSPend i m) : WFSPend _ _).
Notation FailPend j mf i mp :=
  (Some (Some (MkWFSPend j mf), MkWFSPend i mp)).

Variant WaitFreeStackState {T A} :=
| WaitFreeStackDef (vs : list A) (m : WFSPend T A).
Arguments WaitFreeStackState : clear implicits.

Variant WaitFreeStackStep {T A} : WaitFreeStackState T A -> ThreadEvent T (WaitFreeStackSig A) -> WaitFreeStackState T A -> Prop :=
| StackCall i R (m : _ R) vs :
    WaitFreeStackStep
      (WaitFreeStackDef vs NoPend)
      (i, CallEv m)
      (WaitFreeStackDef vs (PassPend i m))
| StackContendCall i j vs RO (mo : _ RO) RN (mn : _ RN) :
    i <> j ->
    WaitFreeStackStep
      (WaitFreeStackDef vs (PassPend i mo))
      (j, CallEv mn)
      (WaitFreeStackDef vs (FailPend j mn i mo))
| StackContendRet i j vs RO (mo : _ RO) RN (mn : _ (StkRet RN)) :
    i <> j ->
    WaitFreeStackStep
      (WaitFreeStackDef vs (FailPend j mn i mo))
      (j, RetEv mn FAIL)
      (WaitFreeStackDef vs (PassPend i mo))
| RetPush i v vs :
    WaitFreeStackStep
      (WaitFreeStackDef vs (PassPend i (WFPush v)))
      (i, RetEv (WFPush v) (PASS tt))
      (WaitFreeStackDef (v :: vs) NoPend)
| RetPopPass i v vs :
    WaitFreeStackStep
      (WaitFreeStackDef (v :: vs) (PassPend i WFPop))
      (i, RetEv WFPop (PASS (Some v)))
      (WaitFreeStackDef vs NoPend)
| RetPopFail i :
    WaitFreeStackStep
      (WaitFreeStackDef nil (PassPend i WFPop))
      (i, RetEv WFPop (PASS None))
      (WaitFreeStackDef nil NoPend).

Ltac sccall i m :=
let jj := fresh "j" in
eapply SCCall with
      (a':=fun jj =>
        if i =? jj then
          Some (existT _ _ m)
        else
          _ jj);
[
  easy |
  now rewrite eqb_id |
  apply differ_pointwise_trivial |
  idtac
].

Require Import Coq.Program.Wf.
Require Import Lia.


(* Program Fixpoint wfsSeqCons_help {T A}
  (p : list (ThreadEvent T (WaitFreeStackSig A))) {measure (length p)} :
  forall s : WaitFreeStackState T A, forall l m i,
  Steps WaitFreeStackStep (WaitFreeStackDef l None) p s ->
  SeqConsistent
    (fun j =>
      if i =? j then
        Some (existT _ _ m)
      else
        None)
    p
:= _. *)

Program Fixpoint wfsSeqCons_help {T A}
  (p : list (ThreadEvent T (WaitFreeStackSig A))) {measure (length p)} :
  (
    forall q : list (ThreadEvent T (WaitFreeStackSig A)),
    length q < length p ->
    forall s : WaitFreeStackState T A, forall l,
    Steps WaitFreeStackStep (WaitFreeStackDef l None) q s ->
    SeqConsistent (fun _ : Name T => None) q) ->
  forall s : WaitFreeStackState T A, forall l R m j,
  Steps WaitFreeStackStep (WaitFreeStackDef l (Some (None, MkWFSPend j m))) p s ->
  SeqConsistent
    (fun i : Name T => if j =? i then Some (existT _ R m) else None)
    p := _.
Next Obligation.
Proof.
  ddestruct H0. constructor.
  ddestruct H0.
  {
    eapply SCCall with
      (a':=fun k =>
        if j =? k then
          Some (existT _ _ m)
        else if j0 =? k then
          Some (existT _ _ mn)
        else
          None).
    { now rewrite eqb_nid. }
    { now rewrite eqb_id, eqb_nid. }
    {
      unfold differ_pointwise. intros.
      now rewrite eqb_nid with (m:=j1) (n:=j0).
    }
    ddestruct H1. constructor.
    ddestruct H1.
    eapply SCRet with
      (a':=fun k =>
        if j =? k then
          Some (existT _ _ m)
        else
          None).
    { now rewrite eqb_id, eqb_nid. }
    { now rewrite eqb_nid. }
    {
      unfold differ_pointwise. intros.
      now rewrite eqb_nid with (n:=j0) (m:=j1).
    }
    {
      eapply wfsSeqCons_help.
      { simpl. lia. }
      {
        intros.
        eapply H.
        { simpl. lia. }
        { exact H4. }
      }
      { exact H2. }
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
    {
      eapply H.
      { simpl. lia. }
      { exact H1. }
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
    {
      eapply H.
      { simpl. lia. }
      { exact H1. }
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
    {
      eapply H.
      { simpl. lia. }
      { exact H1. }
    }
  }
Qed.

Program Fixpoint wfsSeqCons {T A}
  (p : list (ThreadEvent T (WaitFreeStackSig A))) {measure (length p)} :
  forall s : WaitFreeStackState T A, forall l,
  Steps WaitFreeStackStep (WaitFreeStackDef l None) p s ->
  SeqConsistent (fun _ : Name T => None) p := _.
Next Obligation.
Proof.
  ddestruct H. constructor. ddestruct H.
  ddestruct H0.
  {
    sccall i m.
    constructor.
  }
  ddestruct H.
  {
    sccall i m.
    eapply SCCall with
      (a':=fun k =>
        if j =? k then
          _
        else
          _).
    { now rewrite eqb_nid. }
    { now rewrite eqb_id. }
    {
      unfold differ_pointwise.
      intros. now rewrite eqb_nid.
    }
    ddestruct H0. constructor.
    ddestruct H0.
    eapply SCRet with
      (a':=fun k =>
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
    eapply wfsSeqCons_help.
    {
      intros. eapply wfsSeqCons.
      simpl. lia.
      exact H3.
    }
    exact H1.
  }
  {
    sccall i (WFPush v).
    eapply SCRet with
      (a':=fun _ => None).
    { now rewrite eqb_id. }
    { easy. }
    {
      unfold differ_pointwise.
      intros. now rewrite eqb_nid.
    }
    {
      eapply wfsSeqCons.
      simpl. lia.
      exact H0.
    }
  }
  {
    sccall i (WFPop (A:=A)).
    eapply SCRet with
      (a':=fun _ => None).
    { now rewrite eqb_id. }
    { easy. }
    {
      unfold differ_pointwise.
      intros. now rewrite eqb_nid.
    }
    {
      eapply wfsSeqCons.
      simpl. lia.
      exact H0.
    }
  }
  {
    sccall i (WFPop (A:=A)).
    eapply SCRet with
      (a':=fun _ => None).
    { now rewrite eqb_id. }
    { easy. }
    {
      unfold differ_pointwise.
      intros. now rewrite eqb_nid.
    }
    {
      eapply wfsSeqCons.
      simpl. lia.
      exact H0.
    }
  }
Qed.

Program Definition wfStackSpec {T A} : Spec T (WaitFreeStackSig A) := {|
  State := WaitFreeStackState T A;
  Step := WaitFreeStackStep;
  Init := WaitFreeStackDef nil NoPend
|}.

Next Obligation.
Proof.
  eapply wfsSeqCons.
  exact H.
Qed.