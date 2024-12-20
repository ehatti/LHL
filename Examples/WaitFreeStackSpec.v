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

Module AtomicWFStack.
  Variant WFStackState {T V} :=
  | WFSsIdle (vs : list V)
  | WFSsPend (t : Name T) (vs : list V) {R:Type} (m:WaitFreeStackSig V R).
  Arguments WFStackState : clear implicits.

  Definition eval_stack {T V} (st : WFStackState T V) : list V :=
    match st with
    | WFSsIdle vs | WFSsPend _ vs _ => vs
    end.

  Variant WFStackStep {T A} : WFStackState T A -> ThreadEvent T (WaitFreeStackSig A) -> WFStackState T A -> Prop :=
  | WFCall vs i R (m : _ R):
      WFStackStep (WFSsIdle vs) (i, CallEv m) (WFSsPend i vs m)
  | WFRetFail vs i R (m : _ (StkRet R)):
      WFStackStep
        (WFSsPend i vs m)
        (i, RetEv m FAIL)
        (WFSsIdle vs)
  | WFPushRetSucc i v vs :
      WFStackStep
        (WFSsPend i vs (WFPush v))
        (i, RetEv (WFPush v) (PASS tt))
        (WFSsIdle (v :: vs))
  | WFPopRetSome i v vs :
      WFStackStep
        (WFSsPend i (v :: vs) WFPop)
        (i, RetEv WFPop (PASS (Some v)))
        (WFSsIdle vs)
  | WFPopRetNone i :
      WFStackStep
        (WFSsPend i nil WFPop)
        (i, RetEv WFPop (PASS None))
        (WFSsIdle nil).

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

  Program Definition WFStackSpec {T A} : Spec T (WaitFreeStackSig A) := {|
    State := WFStackState T A;
    Step := WFStackStep;
    Init := WFSsIdle nil
  |}.
  Next Obligation.
    generalize dependent (@nil A).
    apply double_ind with
      (P := fun p => forall l, Steps WFStackStep (WFSsIdle l) p s -> SeqConsistent (fun _ : Name T => None) p); intros; try constructor.
    {
      inversion H; subst.
      inversion H2; subst.
      eapply SCCall with
        (a':=fun j =>
          if i =? j then
            Some (existT _ _ _)
          else
            None);
      [auto|
      now rewrite eqb_id|
      apply differ_pointwise_trivial| ].
      constructor.
    }
    {
      inversion H0; subst; clear H0.
      inversion H3; subst; clear H3.
      inversion H5; subst; clear H5.
      inversion H2; subst; clear H2;
        (eapply SCCall with
          (a':=fun j =>
          if i =? j then
            Some (existT _ _ _)
          else
            None);
        [auto|
        now rewrite eqb_id|
        apply differ_pointwise_trivial| ];
        eapply SCRet with (a':=fun j => None); [
          now rewrite eqb_id|
          auto|
          unfold differ_pointwise; intros; erewrite eqb_nid; eauto|
          eauto
        ]).
    }
  Defined.
    (* remember (WFSsIdle nil) as st.
    remember (fun _ : Name T => None) as tst.
    assert (forall tid, tst tid <> None <-> exists vs, st = WFSsPend tid vs) as Hinv;
    [split; intros; subst; [|destruct H0]; congruence|].    
    clear Heqst. clear Heqtst.
    generalize dependent tst.
    generalize dependent st.
    induction p; [constructor|];intros.
    destruct a as [i ev].
    inversion H; subst.
    inversion H2; subst.
    {
      assert (forall j, tst j = None).
      {
        intros.
        specialize (Hinv j) as [? _].
        destruct (tst j); auto.
        assert (exists vs0 : list A, WFSsIdle vs = WFSsPend j vs0) as [? ?];
        [apply H0; inversion 1|].
        inversion H1.
      }

      eapply SCCall with
        (a':=fun j =>
        if i =? j then
          Some (existT _ _ _)
        else
          tst j).
      - apply H0.
      - rewrite eqb_id; constructor.
      - apply differ_pointwise_trivial.
      - apply (IHp (WFSsPend i vs)); auto.
        split; intros.
        + destruct (i =? tid) eqn:eq; try congruence.
          rewrite eqb_iff in eq; subst.
          eauto.
        + destruct H1.
          inversion H1; subst.
          rewrite eqb_id; intros; congruence.
    }
    {
      apply SCRet with (a':=fun j => None); auto.

    } *)
End AtomicWFStack.

Module SetWFStack.
  
End SetWFStack.



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

Program Definition wfStackSpec {T A} : Spec T (WaitFreeStackSig A) := {|
  State := WaitFreeStackState T A;
  Step := WaitFreeStackStep;
  Init := WaitFreeStackDef nil NoPend
|}.

Admit Obligations.