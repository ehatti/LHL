From LHL.Core Require Import
  ProgramRules
  Program
  LogicFacts
  SingConds
  Program
  ProgramRules
  ProgramFacts
  Traces
  Tensor
  Logic
  Specs
  VisPoss.

From LHL.Util Require Import
  TransUtil
  Tactics
  Util.

From LHL.Examples Require Import
  ExchangerSpec
  AtomicStackSpec
  WaitFreeStackSpec.
Import AtomicWFStack.

From Coq Require Import
  Lists.List
  Logic.FunctionalExtensionality
  Logic.PropExtensionality.
Import ListNotations.

Unset Printing Records.

Definition E A :=
  ExchSig (option A) |+| WaitFreeStackSig A.

Definition VE T A : Spec T (E A) :=
  tensorSpec exchSpec WFStackSpec.

Definition F A := AtomicStackSig A.

Definition VF T A : Spec T (F A) :=
  atomicStackSpec.

Definition push {A} (v : A) : Prog (E A) unit :=
  loop (
    b <- call (WFPush v);
    match b with
    | PASS tt => ret (Break tt)
    | FAIL =>
        b <- call (Exch (Some v));
        match b with
        | Some None => ret (Break tt)
        | _ => ret Continue
        end
    end
  ).

(* TODO: fix FAIL case *)
Definition pop {A} : Prog (E A) (option A) :=
  loop (
    b <- call WFPop;
    match b with
    | PASS v => ret (Break v)
    | FAIL =>
        b <- call (Exch None);
        match b with
        | Some (Some v) => ret (Break (Some v))
        | _ => ret Continue
        end
    end
  ).

Definition EBStack A : Impl (E A) (F A) :=
  fun _ m => match m with
  | Push v => push v
  | Pop => pop
  end.

Definition Prec T A := SPrec (VE T A) (VF T A).
Definition Relt T A := SRelt (VE T A) (VF T A).
Definition Post T A R := R -> SRelt (VE T A) (VF T A).

Notation stkSt s := (RState (snd s)).
Notation exchSt s := (LState (snd s)).

Notation pendSet s := (
  match exchSt s with
  | ExchDef ps _ => ps
  end
).

Notation doneSet s := (
  match exchSt s with
  | ExchDef _ ds => ds
  end
).

Notation IStep s i e t :=
  (InterStep (EBStack _) s (i, UEvent (Some e)) t).

Notation ISt := (InterState (F _) (VE _ _)).

Variant EBTran {T A} : Name T -> Relt T A :=
| StkInvoke i s x t y :
    InvokeAny (EBStack A) i s (eq x) t (eq y) ->
    EBTran i s x t y
| StkReturn i s x t y :
    ReturnAny (EBStack A) i s (eq x) t (eq y) ->
    EBTran i s x t y
| StkCallPush s x t i v :
    IStep s i (CallEv (inr (WFPush v))) t ->
    EBTran i s x t x
| StkPushPass (s : ISt) x t y i v :
    forall (nin_pend :
      forall v, (i, v) ∈ pendSet s -> doneSet s <> {}
    ),
    IStep s i (RetEv (inr (WFPush v)) (PASS tt)) t ->
    VisPossSteps x [(i, CallEv (Push v)); (i, RetEv (Push v) tt)] y ->
    EBTran i s x t y
| StkPushFail s x t i v :
    IStep s i (RetEv (inr (WFPush v)) FAIL) t ->
    EBTran i s x t x
| StkCallPop s x t i :
    IStep s i (CallEv (inr WFPop)) t ->
    EBTran i s x t x
| StkPopPass (s : ISt) x t y i v :
    forall (nin_pend :
      forall v, (i, v) ∈ pendSet s -> doneSet s <> {}
    ),
    IStep s i (RetEv (inr WFPop) (PASS v)) t ->
    VisPossSteps x [(i, CallEv Pop); (i, RetEv Pop v)] y ->
    EBTran i s x t y
| StkPopFail s x t i :
    IStep s i (RetEv (inr WFPop) FAIL) t ->
    EBTran i s x t x
| StkOffer s x t i v :
    forall (i_wait :
      match v with
      | Some v => Waiting i (Push v) x
      | None => Waiting i Pop x
      end),
    IStep s i (CallEv (inl (Exch v))) t ->
    EBTran i s x t x
| StkRevoke s x t i v :
    IStep s i (RetEv (inl (Exch v)) None) t ->
    EBTran i s x t x
| StkPushAccept (s : ISt) x t y i j v :
    forall (neq : i <> j),
    forall (seq :
      exchSt s = ExchDef {i => Some v, j => None} {}
    ),
    IStep s i (RetEv (inl (Exch (Some v))) (Some None)) t ->
    VisPossSteps
      x
      [(i, CallEv (Push v)); (i, RetEv (Push v) tt);
       (j, CallEv Pop); (j, RetEv Pop (Some v))]
      y ->
    EBTran i s x t y
| StkPushConflict (s : ISt) x t i j v w :
    forall (neq : i <> j),
    forall (seq :
      exchSt s = ExchDef {i => Some v, j => Some w} {}
    ),
    IStep s i (RetEv (inl (Exch (Some v))) (Some (Some w))) t ->
    EBTran i s x t x
| StkPopAccept (s : ISt) x t y i j v :
    forall (neq : i <> j),
    forall (seq :
      exchSt s = ExchDef {i => None, j => Some v} {}
    ),
    IStep s i (RetEv (inl (Exch None)) (Some (Some v))) t ->
    VisPossSteps
      x
      [(j, CallEv (Push v)); (j, RetEv (Push v) tt);
       (i, CallEv Pop); (i, RetEv Pop (Some v))]
      y ->
    EBTran i s x t y
| StkPopConflict (s : ISt) x t i j :
    forall (neq : i <> j),
    forall (seq :
      exchSt s = ExchDef {i => None, j => None} {}
    ),
    IStep s i (RetEv (inl (Exch None)) (Some None)) t ->
    EBTran i s x t x
| StkFinish (s : ISt) x t i j (v w : option A) :
    forall (neq : i <> j),
    forall (seq :
      exchSt s = ExchDef {j => w} {i => v}
    ),
    IStep s i (RetEv (inl (Exch v)) (Some w)) t ->
    EBTran i s x t x
| StkTau s x t i :
    InterStep (EBStack _) s (i, UEvent None) t ->
    EBTran i s x t x.

Definition Guar {T A} (i : Name T) : Relt T A :=
  EBTran i.

Definition Rely {T A} (i : Name T) : Relt T A :=
  SRTC (fun s x t y => exists j, i <> j /\ EBTran j s x t y).

Record Inv {T A}
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
:= {
  state_consistent :
    exists vs pu,
      (pu = None /\ stkSt s = WFSsIdle vs \/
      exists i R m,
        pu = Some (i, existT m) /\
        stkSt s = WFSsPend (R:=R) i vs m) /\
      PState x = AtomicStackDef vs None;
  wait_inv :
    forall i v,
      contains (i, v) (pendSet s) ->
      doneSet s = {} ->
      match v with
      | Some v => Waiting i (Push v) x
      | None => Waiting i Pop x
      end
}.

Record Ready {T A} (i : Name T)
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
:= {
  ready_inv : Inv s x;
  ready_lazy :
    forall v,
      contains (i, v) (pendSet s) ->
      doneSet s <> {}
}.

Record Complete {T A} (i : Name T) (v : option A)
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
:= {
  comp_inv : Inv s x;
  comp_pres : contains (i, v) (pendSet s);
  comp_emp : doneSet s = {}
}.

Record ReadyWaiting {T A} (i : Name T) {R} (m : F A R)
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
:= {
  wait_ready : Ready i s x;
  ready_wait : Waiting i m x
}.

Record ReadyDone {T A} (i : Name T) {R} (m : F A R) (r : R)
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
:= {
  done_ready : Ready i s x;
  ready_done : Done i m r x;
}.

From Equations Require Import Equations.

Equations rde_prop {T A R}
  (s : InterState (F A) (VE T A))
  (i : Name T) (m : F A R) (r : R) : Prop :=
rde_prop s i (Push v) _ :=
  exists j, exchSt s = ExchDef {j => None} {i => Some v};
rde_prop s i Pop v :=
  exists j, exchSt s = ExchDef {j => v} {i => None}.

Record ReadyDoneExch {T A} (i : Name T) {R} (m : F A R) (r : R)
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
:= {
  dexch_ready : ReadyDone i m r s x;
  ready_proper : rde_prop s i m r
}.

Record Conflicted {T A} (i : Name T) {R} (m : F A R)
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
:= {
  wexch_ready : ReadyWaiting i m s x;
  ready_improper :
    match m with
    | Push v => exists j w, exchSt s = ExchDef {j => Some w} {i => Some v}
    | Pop => exists j, exchSt s = ExchDef {j => None} {i => None}
    end
}.

Lemma foldProg {E A} :
  forall p : Prog E A,
  match p with
  | Return v => Return v
  | Vis m k => Vis m k
  | Tau p => Tau p
  end = p.
intros.
destruct p; easy.
Qed.

Lemma stepLoopVis {E E' A B} e `{SigCoercion E' E} :
  forall m : E' A,
  forall C : A -> Prog E (ControlFlow B),
  loopAux e (x <- call m; C x) = (x <- call m; loopAux e (C x)). 
intros.
rewrite frobProgId with (p:=loopAux _ _). cbn.
rewrite frobProgId with (p:= x <- call m; _). cbn.
f_equal. extensionality x.
rewrite frobProgId at 1. simpl.
rewrite frobProgId with (p:= x0 <- Return x; _).
simpl. easy.
Qed.

Lemma stepLoopBreak {E A} e :
  forall v : A,
  loopAux e (ret (E:=E) (Break v)) = ret v.
intros. now rewrite frobProgId at 1.
Qed.

Lemma stepLoopCont {E A} e :
  loopAux e (ret (E:=E) (Continue (A:=A))) = Tau (loop e).
intros. now rewrite frobProgId at 1.
Qed.

Lemma stepCall {E E' A B} {m : E' A} {k : A -> Prog E B} `{SigCoercion E' E} :
  (x <- call m; k x) = Vis (coerceOp _ m) k.
rewrite frobProgId at 1. cbn.
f_equal. extensionality x.
rewrite frobProgId at 1. simpl.
apply foldProg.
Qed.

Lemma eq_inj {A} {x y : A} :
  eq x = eq y -> x = y.
intros. now rewrite H.
Qed.

Ltac easycons := repeat (easy || constructor).

Ltac recons := repeat econstructor.

Ltac eq_inj H :=
  apply eq_inj in H; subst.

Ltac begin_commit :=
  unfold Commit, LiftSPrec; intros.

Ltac begin_stable :=
  unfold Stable, stablePost, stableRelt, stablePrec, sub, subRelt, subPrec;
  unfold SStable, stableSRelt, stableSPrec, ssub, subSRelt, subSPrec;
  unfold ReltToPrec, LiftSPrec, LiftSRelt;
  intros; psimpl.

Ltac simp_sets :=
  repeat match goal with
  | [ H : {?i => ?v} = {} |- _ ] =>
      now apply disj_cons in H
  | [ H : {} = {?i => ?v} |- _ ] =>
      symmetry in H;
      now apply disj_cons in H
  | [ H : insert ?x emp = insert ?y emp |- _ ] =>
      apply insert_cong1 in H;
      ddestruct H
  | [ H : insert (?i, ?x) (insert (?j, ?y) emp) =
          insert (?i, ?x) (insert (?k, ?z) emp),
      H0 : ?i <> ?j
    |-
      _
    ] =>
      apply (insert_cong2_pad _ _ _ _ _ _ H0) in H;
      ddestruct H
  (* | [ H : insert ?x ?xs = insert ?y ?ys |- _ ] =>
      let H2 := fresh in
      let H3 := fresh in
      apply insert_cong in H;
      destruct H as [H2 H3];
      ddestruct H2 *)
  | [ H : emp = emp |- _ ] =>
      clear H
  | [ H : contains ?x (insert ?y ?s) |- _ ] =>
      let HL := fresh in
      let HR := fresh in
      apply contains_invert in H;
      destruct H as [HL | HR];
      [ddestruct HL | idtac]
  | [ H : contains ?x emp |- _ ] =>
      now apply contains_contr in H
  end.


Lemma SRTC_stable {T A} {P : Prec T A} {R : Relt T A} :
  (forall s x t y,
    P s x ->
    R s x t y ->
    P t y) ->
  forall s x t y,
    P s x ->
    SRTC R s x t y ->
    P t y.
intros. induction H1. easy.
eapply IHSRTC, H. exact H0. easy.
Qed.

Axiom StkRet_inj : forall A B, StkRet A = StkRet B -> A = B.

Ltac dsteps :=
do 10 try (
  do 2 psimpl;
  match goal with
  | [ H : IStep ?s ?i ?m ?t |- _ ] =>
    unfold InterStep, ThreadsStep, StateStep in H;
    destruct H
  | [ H : PointStep ?M ?s ?m ?t |- _ ] =>
    ddestruct H
  | [ H : WFStackStep ?s ?m ?t |- _ ] =>
    ddestruct H
  | [ H : ExchStep ?s ?m ?t |- _ ] =>
    ddestruct H
  | [ H1 : ?s = ?y, H2 : AtomicStackStep ?y ?m ?z |- _ ] =>
    rewrite H1 in H2 at 1;
    ddestruct H2
  | [ H : AtomicStackStep ?x ?m ?y |- _ ] =>
    ddestruct H
  | [ H : InterStep ?M ?s ?m ?t |- _ ] =>
    unfold InterStep, ThreadsStep, StateStep in H;
    destruct H
  end;
  do 2 psimpl
).

Ltac drecs :=
do 10 try (
  match goal with
  | [ H : Inv ?s ?x |- _ ] =>
    destruct H
  | [ H : Ready ?i ?s ?x |- _ ] =>
    destruct H
  end
).

Ltac simp_eqs :=
do 10 try (
  lazymatch goal with
  | [ H1 : ?y = ?x, H2 : ?z = ?x |- _ ] =>
    rewrite <- H2 in H1 at 1;
    ddestruct H1
  | [ H1 : ?x = ?y, H2 : ?z = ?x |- _ ] =>
    rewrite H1 in H2;
    ddestruct H2
  | [ H1 : ?x = ?y, H2 : ?y = ?z |- _ ] =>
    rewrite H2 in H1 at 1;
    ddestruct H1
  | [ H1 : ?x = ?y, H2 : ?z = ?y |- _ ] =>
    rewrite <- H2 in H1 at 1;
    ddestruct H1
  | [ H : StkRet ?A = StkRet ?B |- _ ] =>
    apply StkRet_inj in H;
    subst
  | [ H : existT ?F ?A ?x = existT ?F ?A ?y |- _ ] =>
    ddestruct H
  end
).

Lemma sing_elem {A} {P : A -> Prop} :
  forall x : A,
  eq x = P ->
  P x.
intros. now rewrite <- H.
Qed.

Lemma Inv_stable {T A} (self : Name T) :
  SStable (Rely self) (@Inv T A).
Proof.
  begin_stable.
  eapply SRTC_stable.
  2: exact H. 2: exact H0.
  clear. intros. cbn in *.
  destruct H0 as [j [neq H0]].
  ddestruct H0.
  {
    unfold InvokeAny, TInvoke, TIdle in H0.
    psimpl. apply sing_elem in H3. psimpl.
    specialize (H4 x2 eq_refl). psimpl.
    destruct H1. cbn in *. ddestruct H1.
    drecs. constructor.
    {
      setoid_rewrite <- H2.
      setoid_rewrite H5.
      easy.
    }
    {
      intros.
      dec_eq_nats i0 i.
      {
        destruct v.
        {
          assert (Waiting i (Push a) x2).
          {
            apply wait_inv0 with (v:= Some a);
            now rewrite H2 at 1.
          }
          destruct H11.
          now rewrite H3 in call_waiting.
        }
        {
          assert (Waiting i Pop x2).
          {
            apply wait_inv0 with (v:= None);
            now rewrite H2 at 1.
          }
          destruct H11.
          now rewrite H3 in call_waiting.
        }
      }
      {
        assert (
          match v with
          | Some v0 => Waiting i0 (Push v0) x2
          | None => Waiting i0 Pop x2
          end
        ).
        {
          apply wait_inv0;
          now rewrite H2 at 1.
        }
        destruct v; destruct H12;
        constructor; now rewrite ?H8, ?H9.
      }
    }
  }
  {
    unfold ReturnAny, TReturn, mapRetPoss in H0.
    psimpl. apply sing_elem in H3. psimpl.
    drecs. constructor.
    {
      setoid_rewrite <- H2.
      setoid_rewrite H10.
      easy.
    }
    {
      intros.
      destruct H1. cbn in *. ddestruct H1.
      symmetry in x4. apply H0 in x4.
      specialize (x4 x3 eq_refl). psimpl.
      dec_eq_nats i0 i.
      {
        destruct v.
        {
          assert (Waiting i (Push a) x3).
          {
            apply wait_inv0 with (v:= Some a);
            now rewrite H2 at 1.
          }
          destruct H15.
          now rewrite H12 in call_waiting.
        }
        {
          assert (Waiting i Pop x3).
          {
            apply wait_inv0 with (v:= None);
            now rewrite H2 at 1.
          }
          destruct H15.
          now rewrite H12 in call_waiting.
        }
      }
      {
        assert (
          match v with
          | Some v0 => Waiting i0 (Push v0) x3
          | None => Waiting i0 Pop x3
          end
        ).
        {
          apply wait_inv0;
          now rewrite H2 at 1.
        }
        destruct v; destruct H16;
        constructor; now rewrite ?H8, ?H9.
      }
    }
  }
  {
    dsteps; drecs;
    psimpl; simp_eqs.
    {
      constructor.
      {
        destruct H; psimpl.
        2:{
          rewrite H7 in x1 at 1.
          ddestruct x1.
        }
        rewrite H7 in x1 at 1.
        ddestruct x1.
        eexists x2, (Some (i, existT _)).
        split. 2: easy.
        right. recons.
        now rewrite <-x at 1.
      }
      { now setoid_rewrite <- H6. }
    }
  }
  {
    dsteps; simp_eqs;
    drecs; psimpl; simp_eqs.
    ddestruct H2.
    ddestruct H3.
    constructor.
    {
      destruct H; psimpl;
      rewrite H3 in x1 at 1;
      ddestruct x1.
      exists (v :: x2), None.
      destruct_big_steps.
      rewrite H2 in H.
      ddestruct H.
      rewrite <-x in H13.
      ddestruct H13.
      split. 2: easy.
      now left.
    }
    {
      setoid_rewrite <- H6. intros.
      dec_eq_nats i0 i.
      { now apply (nin_pend v0) in H8. }
      {
        apply (wait_inv0 i0 v0) in H8.
        2: easy. destruct_big_steps.
        destruct v0, H21;
        constructor; cbn;
        rewrite ?H19, ?H20, ?H12, ?H13; auto.
        now rewrite H18, H11.
        now rewrite H18, H11.
      }
    }
  }
  {
    dsteps; simp_eqs.
    drecs. psimpl. simp_eqs.
    destruct H; psimpl;
    rewrite H8 in x1;
    ddestruct x1.
    constructor.
    {
      exists x2, None.
      split. 2: easy.
      now left.
    }
    { now setoid_rewrite <- H6. }
  }
  {
    dsteps; simp_eqs.
    {
      drecs. psimpl. simp_eqs.
      constructor.
      {
        destruct H; psimpl;
        rewrite H7 in x1;
        ddestruct x1.
        exists x2, (Some (i, existT WFPop)).
        split. 2: easy.
        right. now recons.
      }
      { now setoid_rewrite <- H6. }
    }
  }
  {
    dsteps; simp_eqs;
    drecs; psimpl; simp_eqs.
    ddestruct H2.
    {
      constructor.
      {
        setoid_rewrite <- x at 1.
        destruct_big_steps. dsteps.
        {
          simp_eqs. rewrite H2 in x7.
          ddestruct x7.
          destruct H; psimpl;
          rewrite H0 in x4;
          ddestruct x4.
          exists vs1, None.
          split. 2: easy.
          now left.
        }
        {
          simp_eqs. rewrite H2 in x7.
          ddestruct x7.
          destruct H; psimpl;
          rewrite H0 in x4;
          ddestruct x4.
        }
      }
      {
        setoid_rewrite <- H6. intros.
        dec_eq_nats i0 i.
        { now apply nin_pend in H8. }
        {
          apply wait_inv0 in H8.
          2: easy. destruct_big_steps.
          destruct v1, H21;
          constructor; cbn;
          now rewrite ?H19, ?H20, ?H12, ?H13.
        }
      }
    }
    {
      constructor.
      {
        setoid_rewrite <- x at 1.
        destruct_big_steps. dsteps.
        {
          simp_eqs. rewrite H2 in x7.
          ddestruct x7.
          destruct H; psimpl;
          rewrite H0 in x4;
          ddestruct x4.
        }
        {
          simp_eqs. rewrite H2 in x7.
          ddestruct x7.
          destruct H; psimpl;
          rewrite H0 in x4;
          ddestruct x4.
          exists [], None.
          split. 2: easy.
          now left.
        }
      }
      {
        setoid_rewrite <- H6. intros.
        dec_eq_nats i0 i.
        { now apply nin_pend in H8. }
        {
          apply wait_inv0 in H8.
          2: easy. destruct_big_steps.
          destruct v0, H21;
          constructor; cbn;
          now rewrite ?H19, ?H20, ?H12, ?H13.
        }
      }
    }
  }
  {
    dsteps; simp_eqs.
    drecs. psimpl. simp_eqs.
    constructor.
    {
      setoid_rewrite <- x at 1.
      destruct H; psimpl;
      rewrite H8 in x1;
      ddestruct x1.
      exists x2, None.
      split. 2: easy.
      now left.
    }
    { now setoid_rewrite <- H6. }
  }
  {
    dsteps; simp_eqs;
    drecs. simp_eqs.
    {
      constructor.
      { now setoid_rewrite <- H6. }
      {
        intros.
        rewrite <- x in H at 1.
        simp_sets. now destruct v.
      }
    }
    {
      constructor.
      { now setoid_rewrite <- H6. }
      {
        intros.
        rewrite <- x in H at 1.
        simp_sets.
        { now destruct v. }
        {
          apply wait_inv0.
          {
            rewrite <- x2 at 1.
            apply contains_triv.
          }
          { now rewrite <- x2 at 1. }
        }
      }
    }
  }
  {
    dsteps. simp_eqs.
    drecs. simp_eqs.
    constructor.
    { now setoid_rewrite <- H6. }
    {
      intros.
      rewrite <- x in H at 1.
      simp_sets.
    }
  }
  {
    dsteps; simp_eqs;
    drecs; simp_eqs.
    {
      simp_sets.
      destruct_big_steps.
      simp_eqs. dsteps.
      constructor.
      {
        setoid_rewrite <- H6.
        exists x5, x10.
        split. easy.
        rewrite <-x15.
        f_equal.
        rewrite H9 in x4.
        ddestruct x4.
        rewrite <-x in x8.
        ddestruct x8.
        rewrite <-x9 in x11.
        ddestruct x11.
        rewrite <-x12 in x14.
        now ddestruct x14.
      }
      {
        intros.
        rewrite <- x2 in H10 at 1.
        simp_sets.
      }
    }
    {
      simp_sets.
    }
  }
  {
    dsteps; simp_eqs;
    drecs; simp_eqs;
    simp_sets.
    constructor.
    { now setoid_rewrite <- H6. }
    {
      intros.
      rewrite <- x0 in H7 at 1.
      simp_sets.
    }
  }
  {
    dsteps; simp_eqs;
    drecs; simp_eqs;
    simp_sets; simp_eqs.
    psimpl. destruct_big_steps.
    rewrite H8 in H2. dsteps. simp_eqs.
    constructor.
    {
      setoid_rewrite <- H6.
      exists x3, x2.
      rewrite <- x10 in x7.
      ddestruct x7.
      easy.
    }
    {
      intros.
      rewrite <- x4 in H2 at 1.
      simp_sets.
    }
  }
  {
    dsteps; simp_eqs;
    drecs; simp_eqs;
    simp_sets.
    constructor.
    { now setoid_rewrite <- H6. }
    {
      intros.
      rewrite <- x0 in H7 at 1.
      simp_sets.
    }
  }
  {
    dsteps; simp_eqs;
    simp_sets. drecs.
    constructor.
    { now setoid_rewrite <- H6. }
    {
      intros.
      rewrite <- x2 in H at 1.
      simp_sets.
    }
  }
  {
    dsteps. drecs.
    constructor;
    now setoid_rewrite <- H2.
  }
Qed.

Lemma ready_stable {T A} (i : Name T) :
  SStable (Rely i) (Ready (A:=A) i).
Proof.
  begin_stable.
  eapply SRTC_stable.
  2: exact H. 2: exact H0.
  clear. intros.
  destruct H.
  constructor.
  {
    eapply Inv_stable.
    psplit. exact ready_inv0.
    econstructor.
    2: constructor.
    exact H0.
  }
  destruct H0 as [j [neq H0]].
  ddestruct H0.
  {
    unfold InvokeAny, TInvoke in H. psimpl.
    now setoid_rewrite <- H1.
  }
  {
    unfold ReturnAny, TReturn in H. psimpl.
    now setoid_rewrite <- H1.
  }
  { dsteps; now setoid_rewrite <- H5. }
  {
    dsteps.
    {
      clear - x2 H1.
      exfalso.
      apply StkRet_inj in x2.
      subst. ddestruct H1.
    }
    now setoid_rewrite <-H5.
  }
  { dsteps. now setoid_rewrite <- H5. }
  { dsteps; now setoid_rewrite <- H5. }
  {
    dsteps.
    {
      apply StkRet_inj in x2.
      subst. ddestruct H1.
    }
    now setoid_rewrite <-H5.
    now setoid_rewrite <-H5.
  }
  { dsteps. now setoid_rewrite <- H5. }
  {
    dsteps; drecs; intros.
    {
      rewrite <- x in H1.
      now simp_sets.
    }
    {
      rewrite <- x in H6.
      simp_sets.
      { easy. }
      {
        exfalso.
        eapply ready_lazy0.
        {
          rewrite <- x2 at 1.
          apply contains_triv.
        }
        { now rewrite <- x2 at 1. }
      }
    }
  }
  {
    dsteps. drecs. intros.
    rewrite <- x in H1 at 1.
    simp_sets.
  }
  {
    dsteps; simp_eqs; simp_sets.
    intros. rewrite <- x0 in H7 at 1.
    now simp_sets.
  }
  {
    dsteps; simp_eqs; simp_sets.
    intros. rewrite <- x0 in H6 at 1.
    now simp_sets.
  }
  {
    dsteps; simp_eqs; simp_sets.
    intros. rewrite <- x0 in H7 at 1.
    now simp_sets.
  }
  {
    dsteps; simp_eqs; simp_sets.
    intros. rewrite <- x0 in H6 at 1.
    now simp_sets.
  }
  {
    dsteps; simp_eqs; simp_sets.
    intros. rewrite <- x2 in H6 at 1.
    now simp_sets.
  }
  {
    dsteps.
    now setoid_rewrite <- H1.
  }
Qed.

Lemma ready_waiting_stable {T A} (i : Name T) {R} (m : F A R) :
  SStable (Rely i) (ReadyWaiting i m).
Proof.
  begin_stable.
  eapply SRTC_stable.
  2: exact H. 2: exact H0.
  clear. intros.
  destruct H.
  constructor.
  {
    eapply ready_stable.
    psplit. exact wait_ready0.
    econstructor.
    2: constructor.
    easy.
  }
  destruct H0 as [j [neq H]].
  destruct wait_ready0, ready_wait0.
  destruct ready_inv0. psimpl.
  ddestruct H.
  all: try easy.
  {
    unfold InvokeAny, TInvoke, TIdle in H.
    psimpl. specialize (H5 x eq_refl). psimpl.
    apply sing_elem in H4. psimpl.
    dec_eq_nats i0 i.
    { now rewrite call_waiting in H5. }
    {
      constructor.
      { now rewrite H10. }
      { now rewrite H11. }
    }
  }
  {
    unfold ReturnAny, TReturn, Returned, mapRetPoss in H.
    psimpl. destruct H2. cbn in *. ddestruct H2.
    symmetry in x6. specialize (H x6 x5 eq_refl).
    psimpl. apply sing_elem in H4. psimpl.
    dec_eq_nats i0 i.
    { now rewrite call_waiting in H2. }
    {
      constructor.
      { now rewrite H10. }
      { now rewrite H11. }
    }
  }
  {
    dsteps; simp_eqs.
    { ddestruct H3. }
    ddestruct H4.
    destruct_big_steps.
    constructor.
    { now rewrite H18, H11. }
    { now rewrite H19, H12. }
  }
  {
    dsteps; simp_eqs.
    { ddestruct H3. }
    ddestruct H4.
    destruct_big_steps;
    constructor;
    now rewrite ?H18, ?H19, ?H12, ?H11.
    destruct_big_steps;
    constructor;
    now rewrite ?H20, ?H19, ?H13, ?H12.
  }
  {
    dec_eq_nats i0 i.
    {
      exfalso.
      eapply ready_lazy0 with
        (v:= Some v).
      {
        rewrite seq at 1.
        apply contains_triv.
      }
      { now rewrite seq at 1. }
    }
    dec_eq_nats i j.
    {
      exfalso.
      eapply ready_lazy0 with
        (v:= None).
      {
        rewrite seq at 1.
        rewrite insert_perm.
        apply contains_triv.
      }
      { now rewrite seq at 1. }
    }
    destruct_big_steps.
    constructor.
    { now rewrite H28, H21, H14, H7. }
    { now rewrite H29, H22, H15, H8. }
  }
  {
    dec_eq_nats i0 i.
    {
      exfalso.
      eapply ready_lazy0 with
        (v:= None).
      {
        rewrite seq at 1.
        apply contains_triv.
      }
      { now rewrite seq at 1. }
    }
    dec_eq_nats i j.
    {
      exfalso.
      eapply ready_lazy0 with
        (v:= Some v).
      {
        rewrite seq at 1.
        rewrite insert_perm.
        apply contains_triv.
      }
      { now rewrite seq at 1. }
    }
    destruct_big_steps.
    constructor.
    { now rewrite H28, H21, H14, H7. }
    { now rewrite H29, H22, H15, H8. }
  }
Qed.

Lemma ready_done_stable {T A} (i : Name T) {R} (m : F A R) (r : R) :
  SStable (Rely i) (ReadyDone i m r).
Proof.
  begin_stable.
  eapply SRTC_stable.
  2: exact H. 2: exact H0.
  clear. intros.
  destruct H.
  constructor.
  {
    eapply ready_stable.
    psplit. exact done_ready0.
    econstructor.
    2: constructor.
    easy.
  }
  destruct H0 as [j [neq H0]].
  destruct ready_done0.
  ddestruct H0.
  all: try easy.
  {
    unfold InvokeAny, TInvoke, TIdle in H.
    psimpl. specialize (H3 x eq_refl). psimpl.
    apply sing_elem in H2. psimpl.
    dec_eq_nats i0 i.
    { now rewrite call_done in H3. }
    {
      constructor.
      { now rewrite H8. }
      { now rewrite H9. }
    }
  }
  {
    unfold ReturnAny, TReturn, Returned, mapRetPoss in H.
    psimpl. destruct H0. cbn in *. ddestruct H0.
    symmetry in x4. specialize (H x4 x3 eq_refl).
    psimpl. apply sing_elem in H2. psimpl.
    dec_eq_nats i0 i.
    { now rewrite call_done in H0. }
    {
      constructor.
      { now rewrite H8. }
      { now rewrite H9. }
    }
  }
  {
    destruct_big_steps.
    constructor.
    { now rewrite H12, H5. }
    { now rewrite H13, H6. }
  }
  {
    destruct_big_steps.
    constructor.
    { now rewrite H12, H5. }
    { now rewrite H13, H6. }
  }
  {
    destruct_big_steps.
    dec_eq_nats i j.
    {
      rewrite <- H5 in call_done; auto.
      rewrite <- H12 in call_done; auto.
      now rewrite call_done in H15.
    }
    constructor.
    { now rewrite H26, H19, H12, H5. }
    { now rewrite H27, H20, H13, H6. }
  }
  {
    destruct_big_steps.
    dec_eq_nats i j.
    { now rewrite call_done in H1. }
    constructor.
    { now rewrite H26, H19, H12, H5. }
    { now rewrite H27, H20, H13, H6. }
  }
Qed.

Lemma ready_done_exch_stable {T A} (i : Name T) {R} (m : F A R) (r : R) :
  SStable (Rely i) (ReadyDoneExch i m r).
Proof.
  begin_stable.
  eapply SRTC_stable.
  2: exact H. 2: exact H0.
  clear. intros.
  destruct H.
  constructor.
  {
    eapply ready_done_stable.
    psplit. exact dexch_ready0.
    econstructor.
    2: constructor.
    easy.
  }
  destruct dexch_ready0, ready_done0.
  destruct done_ready0, ready_inv0.
  destruct H0 as [j [neq H0]].
  ddestruct H0.
  {
    unfold InvokeAny, TInvoke in H.
    psimpl. destruct m; simp rde_prop;
    now setoid_rewrite <- H1.
  }
  {
    unfold ReturnAny, TReturn in H.
    psimpl. destruct m; simp rde_prop;
    now setoid_rewrite <- H1.
  }
  { dsteps; destruct m; simp rde_prop; now setoid_rewrite <- H7. }
  {
    dsteps; simp_eqs; destruct m; simp rde_prop.
    ddestruct H3. ddestruct H3.
    all: repeat (ddestruct H4 || now setoid_rewrite <- H7).
  }
  {
    dsteps; simp_eqs; destruct m; simp rde_prop;
    now setoid_rewrite <- H7.
  }
  { dsteps; simp_eqs; destruct m; simp rde_prop; now setoid_rewrite <- H7. }
  {
    dsteps; simp_eqs; destruct m; simp rde_prop;
    repeat (ddestruct H4 || now setoid_rewrite <- H7).
    ddestruct H3. ddestruct H3.
  }
  {
    dsteps; simp_eqs; destruct m; simp rde_prop;
    now setoid_rewrite <- H7.
  }
  { dsteps; destruct m; simp rde_prop in *; psimpl; simp_eqs; simp_sets. }
  { dsteps; destruct m; simp rde_prop in *; psimpl; simp_eqs; simp_sets. }
  {
    dsteps; destruct m; simp rde_prop in *; psimpl;
    simp_eqs; simp_sets.
    rewrite H9 in seq at 1.
    ddestruct seq. simp_sets.
    rewrite H9 in seq at 1.
    ddestruct seq. simp_sets.
  }
  {
    dsteps; destruct m; simp rde_prop in *; psimpl;
    simp_eqs; simp_sets.
    rewrite H8 in seq at 1.
    ddestruct seq. simp_sets.
    rewrite H8 in seq at 1.
    ddestruct seq. simp_sets.
  }
  {
    dsteps; destruct m; simp rde_prop in *;
    psimpl; simp_eqs; simp_sets.
    rewrite H9 in seq at 1.
    ddestruct seq. simp_sets.
    rewrite H9 in seq at 1.
    ddestruct seq. simp_sets.
  }
  {
    dsteps; destruct m; simp rde_prop in *;
    psimpl; simp_eqs; simp_sets.
    rewrite H8 in seq at 1.
    ddestruct seq. simp_sets.
    rewrite H8 in seq at 1.
    ddestruct seq. simp_sets.
  }
  {
    destruct m; simp rde_prop in *; psimpl;
    rewrite H0 in seq at 1;
    ddestruct seq; simp_sets;
    dsteps; simp_eqs; simp_sets;
    easy.
  }
  {
    dsteps. destruct m; simp rde_prop in *;
    now setoid_rewrite <- H3.
  }
Qed.

Lemma conflicted_stable {T A} (i : Name T) {R} (m : F A R) :
  SStable (Rely i) (Conflicted i m).
Proof.
  begin_stable.
  eapply SRTC_stable.
  2: exact H. 2: exact H0.
  clear. intros.
  destruct H.
  constructor.
  {
    eapply ready_waiting_stable.
    psplit. exact wexch_ready0.
    econstructor.
    2: constructor.
    easy.
  }
  destruct wexch_ready0, ready_wait0.
  destruct wait_ready0, ready_inv0.
  destruct H0 as [j [neq H0]].
  ddestruct H0.
  {
    unfold InvokeAny, TInvoke in H.
    psimpl. destruct m; now setoid_rewrite <- H1.
  }
  {
    unfold ReturnAny, TReturn in H.
    psimpl. destruct m; now setoid_rewrite <- H1.
  }
  { dsteps; destruct m; now setoid_rewrite <- H7. }
  {
    dsteps; simp_eqs; destruct m; simp rde_prop;
    repeat (ddestruct H4 || now setoid_rewrite <- H7).
    ddestruct H3. ddestruct H3.
  }
  { dsteps; simp_eqs; destruct m; now setoid_rewrite <- H7. }
  { dsteps; simp_eqs; destruct m; simp rde_prop;
    repeat (ddestruct H4 || now setoid_rewrite <- H7). }
  {
    dsteps; simp_eqs; destruct m; simp rde_prop;
    repeat (ddestruct H4 || now setoid_rewrite <- H7).
    ddestruct H3. ddestruct H3.
  }
  {
    dsteps; simp_eqs; destruct m; now setoid_rewrite <- H7.
  }
  { dsteps; destruct m; psimpl; simp_eqs; simp_sets. }
  { dsteps; destruct m; psimpl; simp_eqs; simp_sets. }
  {
    dsteps; destruct m; psimpl;
    simp_eqs; simp_sets.
    rewrite H9 in seq at 1.
    ddestruct seq. simp_sets.
    rewrite H9 in seq at 1.
    ddestruct seq. simp_sets.
  }
  {
    dsteps; destruct m; psimpl;
    simp_eqs; simp_sets.
    rewrite H8 in seq at 1.
    ddestruct seq. simp_sets.
    rewrite H8 in seq at 1.
    ddestruct seq. simp_sets.
  }
  {
    dsteps; destruct m;
    psimpl; simp_eqs; simp_sets.
    rewrite H9 in seq at 1.
    ddestruct seq. simp_sets.
    rewrite H9 in seq at 1.
    ddestruct seq. simp_sets.
  }
  {
    dsteps; destruct m;
    psimpl; simp_eqs; simp_sets.
    rewrite H8 in seq at 1.
    ddestruct seq. simp_sets.
    rewrite H8 in seq at 1.
    ddestruct seq. simp_sets.
  }
  {
    destruct m; psimpl;
    rewrite H0 in seq at 1;
    ddestruct seq; simp_sets;
    dsteps; simp_eqs; simp_sets;
    easy.
  }
  {
    dsteps. destruct m;
    now setoid_rewrite <- H3.
  }
Qed.

Lemma complete_tran_pop {T A} (i : Name T) :
  forall s x t y,
  Complete i None s x ->
  Rely i s x t y ->
  Complete i None t y \/
  (exists w, ReadyDoneExch i Pop (Some w) t y) \/
  Conflicted (A:=A) i Pop t y.
Proof.
  intros.
  change (
    Complete i None t y \/
    (exists w, ReadyDoneExch i Pop (Some w) t y) \/
    Conflicted i Pop t y
  ) with (
    (fun t y =>
      Complete i None t y \/
      (exists w, ReadyDoneExch i Pop (Some w) t y) \/
      Conflicted i Pop t y
    ) t y
  ).
  eapply SRTC_stable.
  2:{ left. exact H. }
  2:{ exact H0. }
  clear. intros.
  destruct H0 as [j [neq H0]].
  destruct H.
  2:{
    assert (Rely i s x t y).
    {
      econstructor.
      2: constructor.
      now exists j.
    }
    right.
    destruct H.
    {
      left.
      psimpl. exists x0.
      eapply ready_done_exch_stable.
      psplit. exact H. easy.
    }
    {
      right.
      eapply conflicted_stable.
      psplit. exact H. easy.
    }
  }
  assert (tran : Inv t y).
  {
    eapply Inv_stable.
    psplit. eapply H.(comp_inv _ _ _ _).
    econstructor.
    2: constructor.
    exists j. split.
    exact neq. easy.
  }
  destruct H, comp_inv0.
  ddestruct H0.
  {
    unfold InvokeAny, TInvoke, TIdle in H.
    psimpl. apply sing_elem in H2. psimpl.
    specialize (H3 x4 eq_refl). psimpl.
    left.
    constructor.
    { easy. }
    { now rewrite <- H1 at 1. }
    { now rewrite <- H1 at 1. }
  }
  {
    unfold ReturnAny, TReturn, Returned, mapRetPoss in H.
    psimpl. apply sing_elem in H2. psimpl. destruct H0.
    cbn in *. ddestruct H0. symmetry in x6.
    specialize (H x6 x5 eq_refl). psimpl.
    left.
    constructor.
    { easy. }
    { now rewrite <- H1 at 1. }
    { now rewrite <- H1 at 1. }
  }
  {
    left.
    dsteps.
    constructor.
    { easy. }
    { now rewrite <- H7 at 1. }
    { now rewrite <- H7 at 1. }
    (* constructor.
    { easy. }
    { now rewrite <- H7 at 1. }
    { now rewrite <- H7 at 1. } *)
  }
  {
    left.
    dsteps; simp_eqs.
    ddestruct H4. ddestruct H3.
    constructor.
    { easy. }
    { now rewrite <- H7 at 1. }
    { now rewrite <- H7 at 1. }
  }
  {
    left.
    dsteps; simp_eqs.
    constructor.
    { easy. }
    { now rewrite <- H7 at 1. }
    { now rewrite <- H7 at 1. }
  }
  {
    left.
    dsteps; simp_eqs.
    constructor.
    { easy. }
    { now rewrite <- H7 at 1. }
    { now rewrite <- H7 at 1. }
    (* constructor.
    { easy. }
    { now rewrite <- H7 at 1. }
    { now rewrite <- H7 at 1. } *)
  }
  {
    left.
    dsteps; simp_eqs.
    ddestruct H4. ddestruct H3.
    constructor.
    { easy. }
    { now rewrite <- H7 at 1. }
    { now rewrite <- H7 at 1. }
    constructor.
    { easy. }
    { now rewrite <- H7 at 1. }
    { now rewrite <- H7 at 1. }
  }
  {
    left.
    dsteps; simp_eqs.
    constructor.
    { easy. }
    { now rewrite <- H7 at 1. }
    { now rewrite <- H7 at 1. }
  }
  {
    dsteps.
    rewrite <- x2 in comp_pres0.
    simp_sets.
    rewrite <- x4 in comp_pres0.
    simp_sets.
    left.
    constructor.
    { easy. }
    {
      rewrite <- x at 1.
      rewrite insert_perm.
      apply contains_triv.
    }
    { now rewrite <- x at 1. }
  }
  {
    dsteps.
    rewrite <- x2 in comp_pres0 at 1.
    now simp_sets.
  }
  {
    rewrite seq in comp_pres0 at 1.
    simp_sets. right. left. exists v.
    dsteps; simp_eqs; simp_sets.
    constructor.
    {
      constructor.
      {
        constructor.
        { easy. }
        {
          intros.
          rewrite <- x2 at 1.
          apply disj_cons.
        }
      }
      {
        destruct_big_steps.
        now constructor.
      }
    }
    { simp rde_prop. now exists i0. }
  }
  {
    rewrite seq in comp_pres0 at 1.
    simp_sets.
  }
  {
    rewrite seq in comp_pres0 at 1.
    simp_sets. right. left.
    dsteps; simp_eqs; simp_sets.
    exists v.
    constructor.
    {
      constructor.
      {
        constructor.
        { easy. }
        {
          intros.
          rewrite <- x2 at 1.
          apply disj_cons.
        }
      }
      {
        destruct_big_steps.
        constructor.
        { now rewrite H34, H27. }
        { now rewrite H35, H28. }
      }
    }
    { now exists i0. }
  }
  {
    rewrite seq in comp_pres0 at 1.
    simp_sets. easy.
    dsteps; simp_eqs; simp_sets.
    right. right.
    constructor.
    {
      constructor.
      {
        constructor.
        { easy. }
        {
          intros.
          rewrite <- x2 at 1.
          apply disj_cons.
        }
      }
      {
        eapply wait_inv0 with (v:= None).
        {
          rewrite seq, insert_perm at 1.
          apply contains_triv.
        }
        { now rewrite seq at 1. }
      }
    }
    { now exists i0. }
  }
  {
    rewrite seq in comp_emp0 at 1.
    simp_sets.
  }
  {
    left.
    dsteps.
    constructor.
    { easy. }
    { now rewrite <- H3 at 1. }
    { now rewrite <- H3 at 1. }
  }
Qed.


Lemma complete_tran_push {T A} (i : Name T) (v : A) :
  forall s x t y,
  Complete i (Some v) s x ->
  Rely i s x t y ->
  Complete i (Some v) t y \/
  ReadyDoneExch i (Push v) tt t y \/
  Conflicted i (Push v) t y.
Proof.
  intros.
  change (
    Complete i (Some v) t y \/
    ReadyDoneExch i (Push v) tt t y \/
    Conflicted i (Push v) t y
  ) with (
    (fun t y =>
      Complete i (Some v) t y \/
      ReadyDoneExch i (Push v) tt t y \/
    Conflicted i (Push v) t y
    ) t y
  ).
  eapply SRTC_stable.
  2:{ left. exact H. }
  2:{ exact H0. }
  clear. intros.
  destruct H0 as [j [neq H0]].
  destruct H.
  2:{
    assert (Rely i s x t y).
    {
      econstructor.
      2: constructor.
      now exists j.
    }
    right.
    destruct H.
    {
      left.
      eapply ready_done_exch_stable.
      psplit. exact H. easy.
    }
    {
      right.
      eapply conflicted_stable.
      psplit. exact H. easy.
    }
  }
  assert (tran : Inv t y).
  {
    eapply Inv_stable.
    psplit. eapply H.(comp_inv _ _ _ _).
    econstructor.
    2: constructor.
    exists j. split.
    exact neq. easy.
  }
  destruct H, comp_inv0.
  ddestruct H0.
  {
    unfold InvokeAny, TInvoke, TIdle in H.
    psimpl. apply sing_elem in H2. psimpl.
    specialize (H3 x4 eq_refl). psimpl.
    left.
    constructor.
    { easy. }
    { now rewrite <- H1 at 1. }
    { now rewrite <- H1 at 1. }
  }
  {
    unfold ReturnAny, TReturn, Returned, mapRetPoss in H.
    psimpl. apply sing_elem in H2. psimpl. destruct H0.
    cbn in *. ddestruct H0. symmetry in x6.
    specialize (H x6 x5 eq_refl). psimpl.
    left.
    constructor.
    { easy. }
    { now rewrite <- H1 at 1. }
    { now rewrite <- H1 at 1. }
  }
  {
    left.
    dsteps.
    constructor.
    { easy. }
    { now rewrite <- H7 at 1. }
    { now rewrite <- H7 at 1. }
    (* constructor.
    { easy. }
    { now rewrite <- H7 at 1. }
    { now rewrite <- H7 at 1. } *)
  }
  {
    left.
    dsteps; simp_eqs.
    ddestruct H4. ddestruct H3.
    constructor.
    { easy. }
    { now rewrite <- H7 at 1. }
    { now rewrite <- H7 at 1. }
  }
  {
    left.
    dsteps; simp_eqs.
    constructor.
    { easy. }
    { now rewrite <- H7 at 1. }
    { now rewrite <- H7 at 1. }
  }
  {
    left.
    dsteps; simp_eqs.
    constructor.
    { easy. }
    { now rewrite <- H7 at 1. }
    { now rewrite <- H7 at 1. }
    (* constructor.
    { easy. }
    { now rewrite <- H7 at 1. }
    { now rewrite <- H7 at 1. } *)
  }
  {
    left.
    dsteps; simp_eqs.
    ddestruct H4. ddestruct H3.
    constructor.
    { easy. }
    { now rewrite <- H7 at 1. }
    { now rewrite <- H7 at 1. }
    constructor.
    { easy. }
    { now rewrite <- H7 at 1. }
    { now rewrite <- H7 at 1. }
  }
  {
    left.
    dsteps; simp_eqs.
    constructor.
    { easy. }
    { now rewrite <- H7 at 1. }
    { now rewrite <- H7 at 1. }
  }
  {
    dsteps.
    rewrite <- x2 in comp_pres0.
    simp_sets.
    rewrite <- x4 in comp_pres0.
    simp_sets.
    left.
    constructor.
    { easy. }
    {
      rewrite <- x at 1.
      rewrite insert_perm.
      apply contains_triv.
    }
    { now rewrite <- x at 1. }
  }
  {
    dsteps.
    rewrite <- x2 in comp_pres0 at 1.
    now simp_sets.
  }
  {
    rewrite seq in comp_pres0 at 1.
    now simp_sets.
  }
  {
    rewrite seq in comp_pres0 at 1.
    simp_sets. easy.
    right. right. dsteps;
    simp_eqs; simp_sets.
    constructor.
    {
      constructor.
      {
        constructor.
        { easy. }
        {
          intros.
          rewrite <- x2 at 1.
          apply disj_cons.
        }
      }
      {
        assert (contains (j, Some w) (pendSet s)).
        {
          rewrite seq, insert_perm at 1.
          apply contains_triv.
        }
        now eapply wait_inv0 with (v:= Some w).
      }
    }
    { now exists i0, v0. }
  }
  {
    rewrite seq in comp_pres0 at 1.
    simp_sets. right. left.
    dsteps; simp_eqs; simp_sets.
    constructor.
    {
      constructor.
      {
        constructor.
        { easy. }
        {
          intros.
          rewrite <- x2 at 1.
          apply disj_cons.
        }
      }
      {
        destruct_big_steps.
        constructor.
        { now rewrite H34, H27. }
        { now rewrite H35, H28. }
      }
    }
    { now exists i0. }
  }
  {
    rewrite seq in comp_pres0 at 1.
    simp_sets.
  }
  {
    rewrite seq in comp_emp0 at 1.
    simp_sets.
  }
  {
    left.
    dsteps.
    constructor.
    { easy. }
    { now rewrite <- H3 at 1. }
    { now rewrite <- H3 at 1. }
  }
Qed.

Lemma push_correct {T A} {i : Name T} {v : A} :
  VerifyProg i (LiftSRelt (Rely i)) (LiftSRelt (Guar i))
    (prComp (LiftSPrec (Ready i))
            (TInvoke (EBStack A) i _ (Push v)) ->>
     LiftSRelt (Rely i))
    (push v)
    (fun _ _ _ => LiftSPrec (ReadyDone i (Push v) tt)).
eapply weakenPrec with
  (P:=fun _ _ => LiftSPrec (ReadyWaiting i (Push v))).
2:{
  unfold sub, subRelt, LiftSPrec, LiftSRelt.
  intros. psimpl.
  assert (x0 = eq (invPoss i x1 (Push v))).
  {
    unfold TInvoke in H1. psimpl. unfold invPoss.
    set_ext y. split; intros; psimpl.
    {
      destruct x0, y. cbn in *.
      f_equal. easy.
      extensionality j.
      dec_eq_nats i j.
      now rewrite eqb_id.
      now rewrite eqb_nid, H8.
      extensionality j.
      dec_eq_nats i j.
      now rewrite eqb_id.
      now rewrite eqb_nid, H9.
    }
    {
      exists x1. split. easy.
      cbn. rewrite eqb_id.
      repeat split; (easy || apply differ_pointwise_trivial).
    }
  }
  subst. specialize (H0 _ eq_refl).
  psimpl. exists x0. split. easy.
  assert (ReadyWaiting i (Push v) x (invPoss i x1 (Push v))).
  {
    assert (snd s = snd x).
    { unfold TInvoke in H1. now psimpl. }
    drecs.
    constructor.
    {
      constructor.
      {
        constructor; cbn.
        { now setoid_rewrite <- H. }
        {
          setoid_rewrite <- H. intros.
          dec_eq_nats i0 i.
          { now apply ready_lazy0 in H2. }
          {
            assert (
              match v0 with
              | Some v => Waiting i0 (Push v) x1
              | None => Waiting i0 Pop x1
              end
            ).
            { now apply wait_inv0. }
            destruct v0; destruct H5;
            constructor; cbn;
            now rewrite eqb_nid.
          }
        }
      }
      { now rewrite <- H. }
    }
    {
      constructor; cbn;
      now rewrite eqb_id.
    }
  }
  {
    apply ready_waiting_stable.
    psplit. exact H. easy.
  }
}
cut (
  forall P,
  P ==> (fun _ _ => LiftSPrec (ReadyWaiting i (Push v))) ->
    VerifyProg i (LiftSRelt (Rely i)) (LiftSRelt (Guar i))
      P
      (push v)
      (fun _ _ _ => LiftSPrec (ReadyDone i (Push v) tt))
).
{ intros. now apply H. }
cofix rec. intros P impH. unfold push, loop.
rewrite stepLoopVis, stepCall.
eapply SafeVis with
  (QI:=fun _ _ => LiftSPrec (ReadyWaiting i (Push v)))
  (QR:=fun r _ _ => LiftSPrec (fun s x =>
    match r with
    | PASS tt => ReadyDone i (Push v) tt s x
    | FAIL => ReadyWaiting i (Push v) s x
    end)).
{
  clear rec impH. begin_stable.
  specialize (H0 x1 eq_refl). psimpl.
  exists x0. split. easy.
  apply ready_waiting_stable.
  psplit. exact H1. easy.
}
{
  clear rec impH. begin_stable.
  specialize (H0 x1 eq_refl). psimpl.
  exists x0. split. easy.
  destruct v0.
  {
    destruct v0.
    eapply ready_done_stable.
    psplit. exact H1. easy.
  }
  {
    eapply ready_waiting_stable.
    psplit. exact H1. easy.
  }
}
{
  clear rec. begin_commit.
  psimpl. apply impH in H.
  clear impH. psimpl.
  unfold LiftSPrec in H. psimpl.
  exists (eq x).
  split.
  { recons. }
  split.
  { intros. subst. recons. }
  split.
  {
    exists x. split. easy.
    destruct H7, wait_ready0, ready_inv0.
    psimpl. constructor.
    {
      constructor.
      {
        constructor.
        ddestruct H2.
        {
          destruct H; psimpl;
          rewrite H2 in x3;
          ddestruct x3. eexists x0, _.
          split. 2: easy.
          right. recons.
          symmetry. exact x.
        }
        { now setoid_rewrite <-H6. }
      }
      { now setoid_rewrite <- H6. }
    }
    { easy. }
  }
  {
    exists x. split. easy. eq_inj H.
    eapply StkCallPush with
      (i:=i) (v:=v).
    constructor.
    {
      constructor; cbn. easy.
      intros. now rewrite H0.
    }
    { easy. }
  }
}
clear impH.
intros. destruct v0.
{
  clear rec.
  destruct v0.
  split.
  {
    begin_commit. do 5 destruct H.
    clear H. psimpl. psimpl.
    ddestruct H.
    {
      exfalso.
      clear - H x2.
      apply StkRet_inj in x2.
      subst. ddestruct H.
    }
    destruct H3, wait_ready0.
    destruct ready_wait0, ready_inv0.
    destruct_all.
    destruct H; destruct_all;
    rewrite H7 in x1 at 1;
    ddestruct x1.
    rename x2 into vs.
    rename x5 into i.
    exists (eq (
      comRetPoss i
        (comInvPoss i
          x3
          (Push v)
          (AtomicStackDef vs (Some (MkStkPend i (Push v)))))
        (Push v)
        (AtomicStackDef (v :: vs) None)
        tt
    )).
    assert (
      VisPossSteps
        x3
        (([] ++ [(i, CallEv (Push v))]) ++ [(i, RetEv (Push v) tt)])
        (comRetPoss i
          (comInvPoss i
            x3
            (Push v)
            (AtomicStackDef vs (Some (MkStkPend i (Push v)))))
          (Push v)
          (AtomicStackDef (v :: vs) None)
          tt)
    ).
    {
      apply retStep. apply callStep.
      constructor.
      { rewrite H3. easycons. }
      { cbn. rewrite eqb_id. easycons. }
    }
    split.
    { recons. }
    split.
    {
      intros. subst.
      exists x3. split. easy.
      eapply erase_vis. exact H.
    }
    split.
    {
      eexists. split. easy.
      constructor.
      {
        constructor.
        {
          constructor.
          {
            setoid_rewrite <- x at 1.
            recons.
          }
          {
            setoid_rewrite <- H6.
            intros.
            dec_eq_nats i0 i.
            {
              apply ready_lazy0 in H8.
              now rewrite H9 in H8 at 1.
            }
            {
              apply wait_inv0 in H8.
              2: easy. destruct v0;
              destruct H8; constructor;
              cbn; now rewrite eqb_nid.
            }
          }
        }
        { now setoid_rewrite <- H6. }
      }
      {
        constructor; cbn;
        now rewrite eqb_id.
      }
    }
    {
      eexists. split. easy. eq_inj H8.
      eapply StkPushPass with
        (i:=i) (v:=v).
      { easy. }
      {
        constructor.
        {
          constructor; cbn. easy.
          intros. now rewrite H0.
        }
        {
          cbn. rewrite H7, <- x at 1.
          easycons.
        }
      }
      { easy. }
    }
  }
  {
    rewrite stepLoopBreak. apply SafeReturn.
    unfold sub, subRelt. intros. psimpl.
    unfold LiftSPrec in H1. psimpl.
    now exists x3.
  }
}
{
  split.
  {
    clear rec. begin_commit.
    do 5 destruct H. clear H.
    do 2 psimpl. exists (eq x3). ddestruct H.
    apply StkRet_inj in x2. psimpl. clear x5.
    destruct H3, wait_ready0, ready_wait0, ready_inv0.
    psimpl. rewrite <- x1 in H3 at 1.
    destruct H3; destruct_all; ddestruct H8.
    split.
    { recons. }
    split.
    {
      intros. subst.
      recons.
    }
    split.
    {
      eexists.
      split. easy.
      constructor.
      {
        constructor.
        {
          constructor.
          {
            rewrite x in x1 at 1.
            ddestruct x1.
            exists x2, None.
            easycons.
          }
          { now setoid_rewrite <- H6. }
        }
        { now setoid_rewrite <- H6. }
      }
      { constructor; easy. }
    }
    {
      eexists. split. easy. eq_inj H8.
      eapply StkPushFail with
        (i:=i) (v:=v).
      constructor.
      {
        constructor; cbn. easy.
        intros. now rewrite H0.
      }
      {
        cbn. rewrite <- x1, <- x8 at 1.
        ddestruct H. easycons.
      }
    }
  }
  {
    rewrite stepLoopVis, stepCall.
    eapply SafeVis with
      (QI:=fun _ _ => LiftSPrec (fun s x =>
        Complete i (Some v) s x \/
        ReadyDoneExch i (Push v) tt s x \/
        Conflicted i (Push v) s x))
      (QR:=fun r _ _ => LiftSPrec (fun s x =>
        match r with
        | Some None => ReadyDone i (Push v) tt s x
        | _ => ReadyWaiting i (Push v) s x
        end)).
    {
      clear rec. begin_stable.
      specialize (H0 x1 eq_refl). psimpl.
      exists x0. split. easy.
      destruct H1.
      {
        eapply complete_tran_push.
        exact H. easy.
      }
      destruct H.
      {
        right. left.
        eapply ready_done_exch_stable.
        psplit. exact H. easy.
      }
      {
        right. right.
        eapply conflicted_stable.
        psplit. exact H. easy.
      }
    }
    {
      clear rec. begin_stable.
      specialize (H0 x1 eq_refl). psimpl.
      exists x0. split. easy.
      destruct v0. destruct o.
      {
        apply ready_waiting_stable.
        psplit. exact H1. easy.
      }
      {
        apply ready_done_stable.
        psplit. exact H1. easy.
      }
      {
        apply ready_waiting_stable.
        psplit. exact H1. easy.
      }
    }
    {
      clear rec. begin_commit.
      rewrite <- reltCompAssoc in H.
      do 5 destruct H. clear H. do 2 psimpl.
      destruct H3, wait_ready0, ready_wait0, ready_inv0.
      psimpl. exists (eq x3).
      split.
      { recons. }
      split.
      { intros. subst. recons. }
      split.
      2:{
        eexists. split. easy.
        eq_inj H8. eapply StkOffer with
          (i:=i) (v:= Some v).
        { constructor; easy. }
        constructor.
        {
          constructor; cbn. easy.
          intros. now rewrite H0.
        }
        { easy. }
      }
      eexists. split. easy.
      {
        left.
        constructor.
        {
          constructor.
          {
            exists x, x1.
            destruct H3.
            split. 2: easy.
            destruct H3; psimpl.
            {
              left.
              split. easy.
              now rewrite <-H6 at 1.
            }
            {
              split. 2: easy. right.
              now setoid_rewrite <-H6.
            }
          }
          {
            intros.
            ddestruct H.
            {
              rewrite <- x in H8 at 1.
              now simp_sets.
            }
            {
              rewrite <- x in H8 at 1.
              simp_sets.
              { easy. }
              {
                apply wait_inv0.
                rewrite <- x5 at 1.
                { apply contains_triv. }
                { now rewrite <- x5 at 1. }
              }
            }
          }
        }
        {
          ddestruct H;
          rewrite <- x at 1;
          apply contains_triv.
        }
        {
          ddestruct H;
          now rewrite <- x at 1.
        }
      }
    }
    intros.
    assert (v0 = Some None \/ v0 <> Some None).
    {
      destruct v0. destruct o.
      now right. now left. now right.
    }
    destruct H. subst.
    {
      clear rec.
      split.
      {
        begin_commit. do 5 destruct H.
        clear H. do 2 psimpl.
        destruct H3.
        {
          destruct H3, comp_inv0.
          psimpl. remember (Some None).
          move Heqo at bottom. ddestruct H.
          2:{
            rewrite <- x5 in comp_emp0.
            simp_sets.
          }
          2:{ easy. }
          ddestruct Heqo.
          rename x4 into vs.
          epose (p' :=
            comRetPoss j
              (comInvPoss j
                (comRetPoss i
                  (comInvPoss i
                    x3
                    (Push v)
                    (AtomicStackDef vs _))
                  (Push v)
                  (AtomicStackDef (v :: vs) _)
                  tt)
                Pop
                (AtomicStackDef (v :: vs) _))
              Pop
              (AtomicStackDef vs _)
              (Some v)
          ).
          assert (
            VisPossSteps
              x3
              ([] ++
               [(i, CallEv (Push v))] ++
               [(i, RetEv (Push v) tt)] ++
               [(j, CallEv Pop)] ++
               [(j, RetEv Pop (Some v))])
              p'
          ).
          {
            assert (Waiting i (Push v) x3).
            {
              eapply wait_inv0 with (v:= Some v).
              {
                rewrite <- x2 at 1.
                apply contains_triv.
              }
              { now rewrite <- x2 at 1. }
            }
            assert (Waiting j Pop x3).
            {
              eapply wait_inv0 with (v:= None).
              {
                rewrite <- x2 at 1.
                rewrite insert_perm.
                apply contains_triv.
              }
              { now rewrite <- x2 at 1. }
            }
            destruct H8, H9.
            repeat rewrite app_assoc.
            apply retStep. apply callStep.
            apply retStep. apply callStep.
            constructor.
            { rewrite H7. easycons. }
            { cbn. rewrite eqb_id. easycons. }
            { cbn. rewrite eqb_nid; easycons. }
            { cbn. rewrite eqb_id, eqb_nid; easycons. }
          }
          exists (eq p').
          split.
          { recons. }
          split.
          {
            intros. subst.
            eexists. split. easy.
            eapply erase_vis. exact H8.
          }
          split.
          {
            exists p'.
            split. easy.
            constructor.
            {
              constructor.
              {
                constructor.
                {
                  exists vs, x1.
                  now setoid_rewrite <-H6.
                }
                {
                  intros.
                  rewrite <- x in H10 at 1.
                  simp_sets.
                }
              }
              {
                intros.
                rewrite <- x at 1.
                apply disj_cons.
              }
            }
            {
              constructor; cbn;
              now rewrite eqb_id, eqb_nid.
            }
          }
          {
            exists p'. split. easy. eq_inj H9.
            eapply StkPushAccept with
              (i:=i) (j:=j) (v:=v).
            { easy. }
            { easy. }
            {
              constructor.
              {
                constructor; cbn. easy.
                intros. now rewrite H0.
              }
              {
                cbn. rewrite <- x2, <- x at 1.
                easycons.
              }
            }
            { exact H8. }
          }
        }
        destruct H3.
        {
          exists (eq x3).
          split.
          { recons. }
          split.
          { intros. subst. recons. }
          split.
          {
            exists x3. split. easy.
            destruct H3, dexch_ready0.
            destruct done_ready0, ready_inv0.
            constructor.
            {
              constructor.
              {
                constructor.
                { now setoid_rewrite <- H6. }
                {
                  intros.
                  ddestruct H.
                  {
                    rewrite <- x in H7 at 1.
                    simp_sets.
                  }
                  {
                    rewrite <- x in H3 at 1.
                    simp_sets.
                  }
                }
              }
              {
                intros.
                ddestruct H.
                {
                  rewrite <- x at 1.
                  apply disj_cons.
                }
                {
                  rewrite <- x in H3 at 1.
                  simp_sets.
                }
              }
            }
            { easy. }
          }
          {
            eexists. split. easy. eq_inj H7.
            destruct H3. simp rde_prop in ready_proper0.
            psimpl.
            eapply StkFinish with
              (i:=i) (j:=x1) (v:= Some v).
            {
              ddestruct H.
              {
                rewrite H3 in x2.
                ddestruct x2.
                simp_sets.
              }
              {
                rewrite H3 in x4.
                ddestruct x4.
                now simp_sets.
              }
            }
            { exact H3. }
            constructor.
            {
              constructor; cbn. easy.
              intros. now rewrite H0.
            }
            { easy. }
          }
        }
        {
          destruct H3. psimpl.
          remember (Some v).
          remember (Some None).
          move Heqo at bottom.
          move Heqo0 at bottom.
          ddestruct H.
          {
            rewrite H3 in x2.
            ddestruct x2.
            simp_sets.
          }
          {
            ddestruct Heqo0.
            rewrite H3 in x5.
            ddestruct x5.
            simp_sets.
          }
          { easy. }
        }
      }
      {
        rewrite stepLoopBreak.
        apply SafeReturn.
        unfold sub, subRelt.
        intros. unfold LiftSPrec in H.
        psimpl. exists x4. now destruct H3.
      }
    }
    {
      split.
      {
        begin_commit.
        repeat rewrite <- reltCompAssoc in H0.
        do 5 destruct H0. clear H0. do 2 psimpl.
        destruct H4.
        {
          destruct H4, comp_inv0.
          ddestruct H0.
          2:{
            rewrite <- x2 in comp_emp0 at 1.
            simp_sets.
          }
          {
            assert (exists w, y = Some w).
            {
              destruct y.
              { now exists a. }
              { easy. }
            }
            destruct H4 as [w]. subst.
            exists (eq x3).
            split.
            { recons. }
            split.
            { intros. subst. recons. }
            split.
            {
              eexists. split. easy.
              constructor.
              {
                constructor.
                {
                  constructor.
                  { now setoid_rewrite <- H7. }
                  {
                    intros.
                    rewrite <- x in H8 at 1.
                    simp_sets.
                  }
                }
                {
                  intros.
                  rewrite <- x at 1.
                  apply disj_cons.
                }
              }
              {
                eapply wait_inv0 with (v:= Some v).
                {
                  rewrite <- x1 at 1.
                  apply contains_triv.
                }
                { now rewrite <- x1 at 1. }
              }
            }
            {
              eexists. split. easy. eq_inj H4.
              eapply StkPushConflict with
                (i:=i) (j:=j) (v:=v) (w:=w).
              { easy. }
              { easy. }
              constructor.
              {
                constructor; cbn. easy.
                intros. now rewrite H1.
              }
              {
                cbn. rewrite <- x, <- x1 at 1.
                easycons.
              }
            }
          }
          {
            exists (eq x3).
            split.
            { recons. }
            split.
            { intros. subst. recons. }
            split.
            {
              eexists. split. easy.
              constructor.
              {
                constructor.
                {
                  constructor.
                  { now setoid_rewrite <- H7. }
                  {
                    intros.
                    rewrite <- x in H0 at 1.
                    simp_sets.
                  }
                }
                {
                  intros.
                  rewrite <- x in H0 at 1.
                  simp_sets.
                }
              }
              {
                eapply wait_inv0 with (v:= Some v).
                {
                  rewrite <- x1 at 1.
                  apply contains_triv.
                }
                { now rewrite <- x1 at 1. }
              }
            }
            {
              eexists. split. easy. eq_inj H0.
              eapply StkRevoke with
                (i:=i) (v:= Some v).
              constructor.
              {
                constructor; cbn. easy.
                intros. now rewrite H1.
              }
              {
                cbn. rewrite <- x1, <- x at 1.
                easycons.
              }
            }
          }
        }
        destruct H4.
        {
          destruct H4, dexch_ready0.
          destruct done_ready0, ready_inv0.
          simp rde_prop in *. psimpl.
          ddestruct H0.
          {
            rewrite H4 in x4 at 1.
            ddestruct x4. simp_sets.
          }
          {
            rewrite H4 in x6 at 1.
            ddestruct x6. now simp_sets.
          }
          {
            rewrite H4 in x4 at 1.
            ddestruct x4. simp_sets.
          }
        }
        {
          destruct H4. psimpl.
          remember v0.
          move Heqo at bottom.
          ddestruct H0; subst.
          {
            rewrite H4 in x2 at 1.
            ddestruct x2. simp_sets.
          }
          {
            rewrite H4 in x5 at 1.
            ddestruct x5. simp_sets.
            exists (eq x3).
            split.
            { recons. }
            split.
            { intros. subst. recons. }
            split.
            {
              eexists. split. easy.
              destruct wexch_ready0.
              destruct wait_ready0.
              destruct ready_inv0.
              constructor.
              {
                constructor.
                {
                  constructor.
                  { now setoid_rewrite <- H7. }
                  {
                    intros.
                    rewrite <- x5 in H8 at 1.
                    simp_sets.
                  }
                }
                {
                  intros.
                  rewrite <- x5 in H8 at 1.
                  simp_sets.
                }
              }
              { easy. }
            }
            {
              eexists. split. easy. eq_inj H8.
              eapply StkFinish with (j:=x4).
              { easy. }
              { exact H4. }
              {
                constructor.
                {
                  constructor; cbn. easy.
                  intros. now rewrite H1.
                }
                {
                  cbn. rewrite <- x5, H4 at 1.
                  recons. all: easy.
                }
              }
            }
          }
          {
            rewrite H4 in x2 at 1.
            ddestruct x2. simp_sets.
          }
        }
      }
      {
        eassert (
          match v0 with
          | Some None => ret (Break tt)
          | _ => ret Continue
          end = ret Continue
        ).
        {
          destruct v0.
          destruct o.
          all: easy.
        }
        rewrite H0. clear H0.
        rewrite stepLoopCont.
        apply SafeTau with
          (QS:=fun _ _ => LiftSPrec (fun s x =>
            match v0 with
            | Some None => ReadyDone i (Push v) tt s x
            | _ => ReadyWaiting i (Push v) s x
            end)).
        {
          (* Inv and Waiting stable *)
          clear rec. begin_stable.
          specialize (H1 x1 eq_refl). psimpl.
          exists x0. split. easy.
          destruct v0. destruct o.
          {
            apply ready_waiting_stable.
            psplit. exact H2. easy.
          }
          {
            apply ready_done_stable.
            psplit. exact H2. easy.
          }
          {
            apply ready_waiting_stable.
            psplit. exact H2. easy.
          }
        }
        {
          unfold SilentStep. intros.
          unfold LiftSPrec in *.
          repeat rewrite <- reltCompAssoc in H0.
          do 5 destruct H0. clear H0. psimpl.
          split.
          {
            eexists. split. easy.
            ddestruct H2. destruct v0.
            {
              destruct o.
              {
                destruct H3, wait_ready0, ready_inv0.
                easycons.
              }
              {
                destruct H3, done_ready0, ready_inv0.
                easycons.
              }
            }
            {
              destruct H3, wait_ready0, ready_inv0.
              easycons.
            }
          }
          {
            eexists. split. easy. eq_inj H0.
            eapply StkTau with (i:=i).
            constructor.
            {
              constructor; cbn. easy.
              intros. now rewrite H1.
            }
            { easy. }
          }
        }
        {
          eapply rec.
          unfold sub, subRelt.
          intros. psimpl.
          destruct v0.
          destruct o.
          all: easy.
        }
      }
    }
  }
}
Qed.

Lemma pop_correct {T A} {i : Name T} :
  VerifyProg i (LiftSRelt (Rely i)) (LiftSRelt (Guar i))
    (prComp (LiftSPrec (Ready i))
            (TInvoke (EBStack A) i _ Pop) ->>
     LiftSRelt (Rely i))
    pop
    (fun v _ _ => LiftSPrec (ReadyDone i Pop v)).
eapply weakenPrec with
  (P:=fun _ _ => LiftSPrec (ReadyWaiting i Pop)).
2:{
  unfold sub, subRelt, LiftSPrec, LiftSRelt.
  intros. psimpl.
  assert (x0 = eq (invPoss i x1 Pop)).
  {
    unfold TInvoke in H1. psimpl. unfold invPoss.
    set_ext y. split; intros; psimpl.
    {
      destruct x0, y. cbn in *.
      f_equal. easy.
      extensionality j.
      dec_eq_nats i j.
      now rewrite eqb_id.
      now rewrite eqb_nid, H8.
      extensionality j.
      dec_eq_nats i j.
      now rewrite eqb_id.
      now rewrite eqb_nid, H9.
    }
    {
      exists x1. split. easy.
      cbn. rewrite eqb_id.
      repeat split; (easy || apply differ_pointwise_trivial).
    }
  }
  subst. specialize (H0 _ eq_refl).
  psimpl. exists x0. split. easy.
  assert (ReadyWaiting i Pop x (invPoss i x1 Pop)).
  {
    assert (snd s = snd x).
    { unfold TInvoke in H1. now psimpl. }
    drecs.
    constructor.
    {
      constructor.
      {
        constructor; cbn.
        { now setoid_rewrite <- H. }
        {
          setoid_rewrite <- H. intros.
          dec_eq_nats i0 i.
          { now apply ready_lazy0 in H2. }
          {
            assert (
              match v with
              | Some v => Waiting i0 (Push v) x1
              | None => Waiting i0 Pop x1
              end
            ).
            { now apply wait_inv0. }
            destruct v; destruct H5;
            constructor; cbn;
            now rewrite eqb_nid.
          }
        }
      }
      { now rewrite <- H. }
    }
    {
      constructor; cbn;
      now rewrite eqb_id.
    }
  }
  {
    apply ready_waiting_stable.
    psplit. exact H. easy.
  }
}
cut (
  forall P,
  P ==> (fun _ _ => LiftSPrec (ReadyWaiting i Pop)) ->
    VerifyProg i (LiftSRelt (Rely i)) (LiftSRelt (Guar i))
      P
      pop
      (fun v _ _ => LiftSPrec (ReadyDone (A:=A) i Pop v))
).
{ intros. now apply H. }
cofix rec. intros P impH. unfold pop, loop.
rewrite stepLoopVis, stepCall.
eapply SafeVis with
  (QI:=fun _ _ => LiftSPrec (ReadyWaiting i Pop))
  (QR:=fun r _ _ => LiftSPrec (fun s x =>
    match r with
    | PASS v => ReadyDone i Pop v s x
    | FAIL => ReadyWaiting i Pop s x
    end)).
{
  clear rec impH. begin_stable.
  specialize (H0 x1 eq_refl). psimpl.
  exists x0. split. easy.
  apply ready_waiting_stable.
  psplit. exact H1. easy.
}
{
  clear rec impH. begin_stable.
  specialize (H0 x1 eq_refl). psimpl.
  exists x0. split. easy.
  destruct v.
  {
    eapply ready_done_stable.
    psplit. exact H1. easy.
  }
  {
    eapply ready_waiting_stable.
    psplit. exact H1. easy.
  }
}
{
  clear rec. begin_commit.
  psimpl. apply impH in H.
  clear impH. psimpl.
  unfold LiftSPrec in H. psimpl.
  exists (eq x).
  split.
  { recons. }
  split.
  { intros. subst. recons. }
  split.
  {
    exists x. split. easy.
    destruct H7, wait_ready0, ready_inv0.
    psimpl. constructor.
    {
      constructor.
      {
        ddestruct H2.
        destruct H; psimpl;
        rewrite H2 in x3;
        ddestruct x3.
        constructor.
        {
          exists x0, (Some (i, existT WFPop)).
          split. 2: easy.
          right. recons.
          symmetry. exact x.
        }
        { now setoid_rewrite <-H6. }
      }
      { now setoid_rewrite <- H6. }
    }
    { easy. }
  }
  {
    exists x. split. easy. eq_inj H.
    eapply StkCallPop with
      (i:=i).
    constructor.
    {
      constructor; cbn. easy.
      intros. now rewrite H0.
    }
    { easy. }
  }
}
clear impH.
intros. destruct v.
{
  clear rec.
  destruct v.
  {
    split.
    {
      begin_commit. do 5 destruct H.
      clear H. psimpl. psimpl.
      unfold coerceOp, coerceId in H.
      remember (PASS (Some a)).
      move Heqs0 at bottom.
      ddestruct H.
      {
        apply StkRet_inj in x4.
        subst. ddestruct H2.
        ddestruct H.
      }
      {
        ddestruct Heqs0.
        destruct H3, wait_ready0.
        destruct ready_wait0, ready_inv0.
        destruct_all. destruct H; psimpl;
        rewrite H7 in x1; ddestruct x1.
        rename a into v.
        rename x5 into i.
        pose (p' :=
          comRetPoss i
            (comInvPoss i
              x3
              Pop
              (AtomicStackDef (v :: vs) (Some (MkStkPend i Pop))))
            Pop
            (AtomicStackDef vs None)
            (Some v)
        ).
        exists (eq p').
        assert (
          VisPossSteps
            x3
            (([] ++ [(i, CallEv Pop)]) ++ [(i, RetEv Pop (Some v))])
            p'
        ).
        {
          apply retStep. apply callStep.
          constructor.
          { rewrite H3. easycons. }
          { cbn. rewrite eqb_id. easycons. }
        }
        split.
        { recons. }
        split.
        {
          intros. subst.
          exists x3. split. easy.
          eapply erase_vis. exact H.
        }
        split.
        {
          eexists. split. easy.
          constructor.
          {
            constructor.
            {
              constructor.
              {
                setoid_rewrite <- x at 1.
                recons.
              }
              {
                setoid_rewrite <- H6.
                intros.
                dec_eq_nats i0 i.
                {
                  apply ready_lazy0 in H8.
                  now rewrite H9 in H8 at 1.
                }
                {
                  apply wait_inv0 in H8.
                  2: easy. destruct v0;
                  destruct H8; constructor;
                  cbn; now rewrite eqb_nid.
                }
              }
            }
            { now setoid_rewrite <- H6. }
          }
          {
            constructor; cbn;
            now rewrite eqb_id.
          }
        }
        {
          eexists. split. easy. eq_inj H8.
          eapply StkPopPass with
            (i:=i) (v:= Some v).
          { easy. }
          {
            constructor.
            {
              constructor; cbn. easy.
              intros. now rewrite H0.
            }
            { 
              cbn. rewrite H7, <- x at 1.
              easycons.
            }
          }
          { easy. }
        }
      }
      {
        ddestruct Heqs0.
      }
    }
    {
      rewrite stepLoopBreak. apply SafeReturn.
      unfold sub, subRelt. intros. psimpl.
      unfold LiftSPrec in H1. psimpl.
      now exists x3.
    }
  }
  {
    split.
    {
      begin_commit. do 5 destruct H.
      clear H. psimpl. psimpl.
      unfold coerceOp, coerceId in H.
      remember (PASS None).
      move Heqs0 at bottom.
      ddestruct H.
      {
        apply StkRet_inj in x4.
        subst. ddestruct H2.
        ddestruct H.
      }
      { ddestruct Heqs0. }
      {
        ddestruct Heqs0.
        destruct H3, wait_ready0.
        destruct ready_wait0, ready_inv0.
        destruct_all. destruct H; psimpl;
        rewrite H7 in x1; ddestruct x1.
        rename x5 into i.
        pose (p' :=
          comRetPoss i
            (comInvPoss i
              x3
              Pop
              (AtomicStackDef [] (Some (MkStkPend i Pop))))
            Pop
            (AtomicStackDef [] None)
            None
        ).
        exists (eq p').
        assert (
          VisPossSteps
            x3
            (([] ++ [(i, CallEv Pop)]) ++ [(i, RetEv Pop None)])
            p'
        ).
        {
          apply retStep. apply callStep.
          constructor.
          { rewrite H3. easycons. }
          { cbn. rewrite eqb_id. easycons. }
        }
        split.
        { recons. }
        split.
        {
          intros. subst.
          exists x3. split. easy.
          eapply erase_vis. exact H.
        }
        split.
        {
          eexists. split. easy.
          constructor.
          {
            constructor.
            {
              constructor.
              {
                setoid_rewrite <- x at 1.
                recons.
              }
              {
                setoid_rewrite <- H6.
                intros.
                dec_eq_nats i0 i.
                {
                  apply ready_lazy0 in H8.
                  now rewrite H9 in H8 at 1.
                }
                {
                  apply wait_inv0 in H8.
                  2: easy. destruct v;
                  destruct H8; constructor;
                  cbn; now rewrite eqb_nid.
                }
              }
            }
            { now setoid_rewrite <- H6. }
          }
          {
            constructor; cbn;
            now rewrite eqb_id.
          }
        }
        {
          eexists. split. easy. eq_inj H8.
          eapply StkPopPass with
            (i:=i) (v:= None).
          { easy. }
          {
            constructor.
            {
              constructor; cbn. easy.
              intros. now rewrite H0.
            }
            { 
              cbn. rewrite H7, <- x at 1.
              easycons.
            }
          }
          { easy. }
        }
      }
    }
    {
      rewrite stepLoopBreak. apply SafeReturn.
      unfold sub, subRelt. intros. psimpl.
      unfold LiftSPrec in H1. psimpl.
      now exists x3.
    }
  }
}
{
  split.
  {
    clear rec. begin_commit.
    do 5 destruct H. clear H.
    do 2 psimpl. exists (eq x3). ddestruct H.
    apply StkRet_inj in x2. psimpl. clear x5.
    destruct H3, wait_ready0, ready_wait0, ready_inv0.
    psimpl. rewrite <- x1 in H3 at 1. destruct H3;
    psimpl; ddestruct H8. ddestruct H.
    rewrite x in x1. ddestruct x1.
    rename x5 into i.
    split.
    { recons. }
    split.
    {
      intros. subst.
      recons.
    }
    split.
    {
      eexists.
      split. easy.
      constructor.
      {
        constructor.
        {
          constructor.
          {
            exists x2, None.
            easycons.
          }
          { now setoid_rewrite <- H6. }
        }
        { now setoid_rewrite <- H6. }
      }
      { constructor; easy. }
    }
    {
      eexists. split. easy. eq_inj H.
      eapply StkPopFail with
        (i:=i).
      constructor.
      {
        constructor; cbn. easy.
        intros. now rewrite H0.
      }
      {
        cbn. rewrite <-x4, x at 1.
        easycons.
      }
    }
  }
  {
    rewrite stepLoopVis, stepCall.
    eapply SafeVis with
      (QI:=fun _ _ => LiftSPrec (fun s x =>
        Complete i None s x \/
        (exists w, ReadyDoneExch i Pop (Some w) s x) \/
        Conflicted i Pop s x))
      (QR:=fun r _ _ => LiftSPrec (fun s x =>
        match r with
        | Some (Some v) => ReadyDone i Pop (Some v) s x
        | _ => ReadyWaiting i Pop s x
        end)).
    {
      clear rec. begin_stable.
      specialize (H0 x1 eq_refl). psimpl.
      exists x0. split. easy.
      destruct H1.
      {
        eapply complete_tran_pop.
        exact H. easy.
      }
      destruct H.
      {
        right. left.
        psimpl. exists x2.
        eapply ready_done_exch_stable.
        psplit. exact H. easy.
      }
      {
        right. right.
        eapply conflicted_stable.
        psplit. exact H. easy.
      }
    }
    {
      clear rec. begin_stable.
      specialize (H0 x1 eq_refl). psimpl.
      exists x0. split. easy.
      destruct v. destruct o.
      {
        apply ready_done_stable.
        psplit. exact H1. easy.
      }
      {
        apply ready_waiting_stable.
        psplit. exact H1. easy.
      }
      {
        apply ready_waiting_stable.
        psplit. exact H1. easy.
      }
    }
    {
      clear rec. begin_commit.
      rewrite <- reltCompAssoc in H.
      do 5 destruct H. clear H. do 2 psimpl.
      destruct H3, wait_ready0, ready_wait0, ready_inv0.
      psimpl. exists (eq x3).
      split.
      { recons. }
      split.
      { intros. subst. recons. }
      split.
      2:{
        eexists. split. easy.
        eq_inj H8. eapply StkOffer with
          (i:=i) (v:= None).
        { constructor; easy. }
        constructor.
        {
          constructor; cbn. easy.
          intros. now rewrite H0.
        }
        { easy. }
      }
      eexists. split. easy.
      {
        left.
        constructor.
        {
          constructor.
          {
            exists x, x1.
            now setoid_rewrite <- H6.
          }
          {
            intros.
            ddestruct H.
            {
              rewrite <- x in H8 at 1.
              now simp_sets.
            }
            {
              rewrite <- x in H8 at 1.
              simp_sets.
              { easy. }
              {
                apply wait_inv0.
                rewrite <- x5 at 1.
                { apply contains_triv. }
                { now rewrite <- x5 at 1. }
              }
            }
          }
        }
        {
          ddestruct H;
          rewrite <- x at 1;
          apply contains_triv.
        }
        {
          ddestruct H;
          now rewrite <- x at 1.
        }
      }
    }
    intros.
    assert (
      (exists x, v = Some (Some x)) \/
      forall x, v <> Some (Some x)).
    {
      destruct v. destruct o.
      { left. recons. }
      { now right. }
      { now right. }
    }
    destruct H. psimpl.
    {
      clear rec.
      split.
      {
        begin_commit. do 5 destruct H.
        clear H. do 2 psimpl.
        destruct H3.
        {
          destruct H3, comp_inv0.
          psimpl. remember (Some (Some x)).
          move Heqo at bottom. ddestruct H.
          2:{
            rewrite <- x6 in comp_pres0 at 1.
            now simp_sets.
          }
          2:{ easy. }
          ddestruct Heqo.
          rename x0 into vs.
          rename x5 into v.
          rename x4 into p.
          epose (p' :=
            comRetPoss i
              (comInvPoss i
                (comRetPoss j
                  (comInvPoss j
                    p
                    (Push v)
                    (AtomicStackDef vs _))
                  (Push v)
                  (AtomicStackDef (v :: vs) _)
                  tt)
                Pop
                (AtomicStackDef (v :: vs) _))
              Pop
              (AtomicStackDef vs _)
              (Some v)
          ).
          assert (
            VisPossSteps
              p
              ([] ++
               [(j, CallEv (Push v))] ++
               [(j, RetEv (Push v) tt)] ++
               [(i, CallEv Pop)] ++
               [(i, RetEv Pop (Some v))])
              p'
          ).
          {
            assert (Waiting j (Push v) p).
            {
              eapply wait_inv0 with (v:= Some v).
              {
                rewrite <- x3 at 1.
                rewrite insert_perm.
                apply contains_triv.
              }
              { now rewrite <- x3 at 1. }
            }
            assert (Waiting i Pop p).
            {
              eapply wait_inv0 with (v:= None).
              {
                rewrite <- x3 at 1.
                apply contains_triv.
              }
              { now rewrite <- x3 at 1. }
            }
            destruct H8, H9.
            repeat rewrite app_assoc.
            apply retStep. apply callStep.
            apply retStep. apply callStep.
            constructor.
            { rewrite H7. easycons. }
            { cbn. rewrite eqb_id. easycons. }
            { cbn. rewrite eqb_nid; easycons. }
            { cbn. rewrite eqb_id, eqb_nid; easycons. }
          }
          exists (eq p').
          split.
          { recons. }
          split.
          {
            intros. subst.
            eexists. split. easy.
            eapply erase_vis. exact H8.
          }
          split.
          {
            exists p'.
            split. easy.
            constructor.
            {
              constructor.
              {
                constructor.
                {
                  exists vs, x2.
                  now setoid_rewrite <- H6.
                }
                {
                  intros.
                  rewrite <- x in H10 at 1.
                  simp_sets.
                }
              }
              {
                intros.
                rewrite <- x at 1.
                apply disj_cons.
              }
            }
            {
              constructor; cbn;
              now rewrite eqb_id.
            }
          }
          {
            exists p'. split. easy. eq_inj H9.
            eapply StkPopAccept with
              (i:=i) (j:=j) (v:=v).
            { easy. }
            { easy. }
            {
              constructor.
              {
                constructor; cbn. easy.
                intros. now rewrite H0.
              }
              {
                cbn. rewrite <- x3, <- x at 1.
                easycons.
              }
            }
            { exact H8. }
          }
        }
        destruct H3.
        {
          psimpl.
          rename x4 into p.
          assert (x0 = x).
          {
            destruct H3, dexch_ready0.
            simp rde_prop in *. psimpl.
            remember (Some x0).
            move Heqo at bottom.
            destruct done_ready0, ready_inv0.
            remember (Some (Some x)).
            move Heqo0 at bottom.
            ddestruct H.
            {
              rewrite H3 in x3 at 1.
              ddestruct x3. simp_sets.
            }
            {
              rewrite H3 in x5 at 1.
              ddestruct x5. simp_sets.
              subst. now ddestruct Heqo0.
            }
            { easy. }
          }
          subst.
          exists (eq p).
          split.
          { recons. }
          split.
          { intros. subst. recons. }
          split.
          {
            eexists. split. easy.
            destruct H3, dexch_ready0.
            destruct done_ready0, ready_inv0.
            constructor.
            {
              constructor.
              {
                constructor.
                { now setoid_rewrite <- H6. }
                {
                  intros.
                  ddestruct H.
                  {
                    rewrite <- x in H7 at 1.
                    simp_sets.
                  }
                  {
                    rewrite <- x in H3 at 1.
                    simp_sets.
                  }
                }
              }
              {
                intros.
                ddestruct H.
                {
                  rewrite <- x at 1.
                  apply disj_cons.
                }
                {
                  rewrite <- x in H3 at 1.
                  simp_sets.
                }
              }
            }
            { easy. }
          }
          {
            eexists. split. easy. eq_inj H7.
            destruct H3. simp rde_prop in *.
            psimpl.
            eapply StkFinish with
              (i:=i) (j:=x2) (v:= None).
            {
              ddestruct H.
              {
                rewrite H3 in x3.
                ddestruct x3.
                simp_sets.
              }
              {
                rewrite H3 in x5.
                ddestruct x5.
                now simp_sets.
              }
            }
            { exact H3. }
            constructor.
            {
              constructor; cbn. easy.
              intros. now rewrite H0.
            }
            { easy. }
          }
        }
        {
          destruct H3. psimpl.
          remember (Some (Some x)).
          remember None.
          move Heqo at bottom.
          move Heqo0 at bottom.
          ddestruct H.
          {
            rewrite H3 in x2.
            ddestruct x2.
            simp_sets.
          }
          {
            ddestruct Heqo0.
            rewrite H3 in x5.
            ddestruct x5.
            simp_sets.
          }
          { easy. }
        }
      }
      {
        rewrite stepLoopBreak.
        apply SafeReturn.
        unfold sub, subRelt.
        intros. unfold LiftSPrec in H.
        psimpl. now exists x5.
      }
    }
    {
      split.
      {
        begin_commit.
        repeat rewrite <- reltCompAssoc in H0.
        do 5 destruct H0. clear H0. do 2 psimpl.
        destruct H4.
        {
          destruct H4, comp_inv0.
          ddestruct H0.
          2:{
            rewrite <- x2 in comp_emp0 at 1.
            simp_sets.
          }
          {
            assert (y = None).
            {
              destruct y.
              now specialize (H a).
              easy.
            }
            subst.
            exists (eq x3).
            split.
            { recons. }
            split.
            { intros. subst. recons. }
            split.
            {
              eexists. split. easy.
              constructor.
              {
                constructor.
                {
                  constructor.
                  { now setoid_rewrite <- H7. }
                  {
                    intros.
                    rewrite <- x in H4 at 1.
                    simp_sets.
                    eapply wait_inv0 with (v:=None).
                    {
                      rewrite <- x1 at 1.
                      apply contains_triv.
                    }
                    { now rewrite <- x1 at 1. }
                  }
                }
                {
                  intros.
                  rewrite <- x at 1.
                  apply disj_cons.
                }
              }
              {
                eapply wait_inv0 with (v:=None).
                {
                  rewrite <- x1 at 1.
                  apply contains_triv.
                }
                { now rewrite <- x1 at 1. }
              }
            }
            {
              eexists. split. easy. eq_inj H4.
              eapply StkPopConflict with
                (i:=i) (j:=j).
              { easy. }
              { easy. }
              constructor.
              {
                constructor; cbn. easy.
                intros. now rewrite H1.
              }
              {
                cbn. rewrite <- x1, <- x at 1.
                easycons.
              }
            }
          }
          {
            exists (eq x3).
            split.
            { recons. }
            split.
            { intros. subst. recons. }
            split.
            {
              eexists. split. easy.
              constructor.
              {
                constructor.
                {
                  constructor.
                  { now setoid_rewrite <- H7. }
                  {
                    intros.
                    rewrite <- x in H0 at 1.
                    simp_sets.
                  }
                }
                {
                  intros.
                  rewrite <- x in H0 at 1.
                  simp_sets.
                }
              }
              {
                eapply wait_inv0 with (v:= None).
                {
                  rewrite <- x1 at 1.
                  apply contains_triv.
                }
                { now rewrite <- x1 at 1. }
              }
            }
            {
              eexists. split. easy. eq_inj H0.
              eapply StkRevoke with
                (i:=i) (v:=None).
              constructor.
              {
                constructor; cbn. easy.
                intros. now rewrite H1.
              }
              {
                cbn. rewrite <- x, <- x1 at 1.
                easycons.
              }
            }
          }
        }
        destruct H4.
        {
          psimpl.
          destruct H4, dexch_ready0.
          simp rde_prop in *. psimpl.
          exists (eq x3).
          split.
          { recons. }
          split.
          { intros. subst. recons. }
          split.
          {
            eexists. split. easy.
            dsteps; simp_eqs; simp_sets.
            constructor.
            {
              destruct done_ready0, ready_inv0.
              constructor.
              {
                constructor.
                { now setoid_rewrite <- H7. }
                {
                  intros.
                  rewrite <- x5 in H8 at 1.
                  simp_sets.
                }
              }
              {
                intros.
                rewrite <- x5 in H8 at 1.
                simp_sets.
              }
            }
            { easy. }
          }
          {
            dsteps; simp_eqs; simp_sets.
            eexists. split. easy. eq_inj H8.
            eapply StkFinish with (j:=x1).
            { easy. }
            { exact H4. }
            {
              constructor.
              {
                constructor; cbn. easy.
                intros. now rewrite H1.
              }
              {
                cbn. rewrite H4, <- x5 at 1.
                recons. all: easy.
              }
            }
          }
        }
        {
          destruct H4. psimpl.
          ddestruct H0; subst.
          {
            rewrite H4 in x1 at 1.
            ddestruct x1. simp_sets.
          }
          {
            rewrite H4 in x4 at 1.
            ddestruct x4. simp_sets.
            exists (eq x3).
            split.
            { recons. }
            split.
            { intros. subst. recons. }
            split.
            {
              eexists. split. easy.
              destruct wexch_ready0.
              destruct wait_ready0.
              destruct ready_inv0.
              constructor.
              {
                constructor.
                {
                  constructor.
                  { now setoid_rewrite <- H7. }
                  {
                    intros.
                    rewrite <- x4 in H8 at 1.
                    simp_sets.
                  }
                }
                {
                  intros.
                  rewrite <- x4 in H8 at 1.
                  simp_sets.
                }
              }
              { easy. }
            }
            {
              eexists. split. easy. eq_inj H8.
              eapply StkFinish with (j:=x2).
              { easy. }
              { exact H4. }
              {
                constructor.
                {
                  constructor; cbn. easy.
                  intros. now rewrite H1.
                }
                {
                  cbn. rewrite <- x4, H4 at 1.
                  recons. all: easy.
                }
              }
            }
          }
          {
            rewrite H4 in x1 at 1.
            ddestruct x1. simp_sets.
          }
        }
      }
      {
        assert (
          match v with
          | Some (Some v) => ret (E:= E A) (Break (Some v))
          | _ => ret Continue
          end = ret Continue
        ).
        {
          destruct v.
          destruct o.
          { now specialize (H a). }
          { easy. }
          { easy. }
        }
        rewrite H0. clear H0.
        rewrite stepLoopCont.
        apply SafeTau with
          (QS:=fun _ _ => LiftSPrec (fun s x =>
            match v with
            | Some (Some v) => ReadyDone i Pop (Some v) s x
            | _ => ReadyWaiting i Pop s x
            end)).
        {
          (* Inv and Waiting stable *)
          clear rec. begin_stable.
          specialize (H1 x1 eq_refl). psimpl.
          exists x0. split. easy.
          destruct v. destruct o.
          {
            apply ready_done_stable.
            psplit. exact H2. easy.
          }
          {
            apply ready_waiting_stable.
            psplit. exact H2. easy.
          }
          {
            apply ready_waiting_stable.
            psplit. exact H2. easy.
          }
        }
        {
          unfold SilentStep. intros.
          unfold LiftSPrec in *.
          repeat rewrite <- reltCompAssoc in H0.
          do 5 destruct H0. clear H0. psimpl.
          split.
          {
            eexists. split. easy.
            ddestruct H2. destruct v.
            {
              destruct o.
              {
                destruct H3, done_ready0, ready_inv0.
                easycons.
              }
              {
                destruct H3, wait_ready0, ready_inv0.
                easycons.
              }
            }
            {
              destruct H3, wait_ready0, ready_inv0.
              easycons.
            }
          }
          {
            eexists. split. easy. eq_inj H0.
            eapply StkTau with (i:=i).
            constructor.
            {
              constructor; cbn. easy.
              intros. now rewrite H1.
            }
            { easy. }
          }
        }
        {
          eapply rec.
          unfold sub, subRelt.
          intros. psimpl.
          destruct v.
          destruct o.
          { now specialize (H a). }
          { easy. }
          { easy. }
        }
      }
    }
  }
}
Qed.

Lemma Invoke_pres_single {T A R} :
  forall (m : F A R) i s ρ t σs,
  TInvoke (VE:= VE T A) (VF:= VF T A) (EBStack A) i R m s (eq ρ) t σs ->
  exists σ, σs = eq σ.
intros.
unfold TInvoke in H. psimpl.
exists (invPoss i ρ m).
set_ext σ. split; intros; destruct_all; subst.
{
  unfold TIdle in H. destruct_all.
  specialize (H2 x eq_refl). destruct_all.
  destruct x, σ. unfold invPoss. cbn in *.
  f_equal; try easy.
  extensionality j. dec_eq_nats i j.
  rewrite eqb_id. easy.
  rewrite eqb_nid, H6; easy.
  extensionality j. dec_eq_nats i j.
  rewrite eqb_id. easy.
  rewrite eqb_nid, H7; easy.
}
{
  cbn. rewrite eqb_id. exists ρ.
  repeat split; (easy || apply differ_pointwise_trivial).
}
Qed.

Lemma Return_pres_single {T A R} :
  forall (m : F A R) v i s ρ t σs,
  TReturn (VE:= VE T A) (VF:= VF T A) (EBStack A) i m v s (eq ρ) t σs ->
  exists σ, σs = eq σ.
intros.
unfold TReturn, mapRetPoss in H. psimpl.
exists (retPoss i ρ).
set_ext σ. split; intros; destruct_all; subst.
{
  unfold retPoss. destruct x, σ. cbn in *.
  f_equal. easy.
  extensionality j. dec_eq_nats i j.
  rewrite eqb_id. easy.
  rewrite eqb_nid, H7; easy.
  extensionality j. dec_eq_nats i j.
  rewrite eqb_id. easy.
  rewrite eqb_nid, H8; easy.
}
{
  cbn. rewrite eqb_id. exists ρ.
  destruct H0. ddestruct H0. cbn in *.
  symmetry in x0. apply H in x0.
  specialize (x0 ρ eq_refl).
  repeat split; (easy || apply differ_pointwise_trivial).
}
Qed.


Theorem EBStackCorrect T A :
  VerifyImpl (VE T A) (VF T A)
  (fun i => LiftSRelt (Rely i))
  (fun i => LiftSRelt (Guar i))
  (fun i _ _ => LiftSPrec (Ready i))
  (EBStack A)
  (fun i _ m r _ _ => LiftSPrec (ReadyDone i m r))
  (TReturn (EBStack A)).
constructor.
{
  intros.
  eexists. subst.
  split. easy.
  constructor.
}
{
  unfold sub, subRelt, LiftSRelt.
  intros. psimpl.
  specialize (H x eq_refl). psimpl.
  specialize (H1 x2 eq_refl). psimpl.
  eexists. split. easy.
  eapply srtcTrans.
  psplit. exact H0. easy.
}
{
  unfold sub, subRelt, LiftSRelt.
  intros. psimpl.
  specialize (H0 x eq_refl). psimpl.
  eexists. split. easy.
  econstructor.
  2: constructor.
  now exists i.
}
{
  unfold sub, subRelt, LiftSRelt.
  intros. psimpl.
  assert (exists x, σ = eq x).
  {
    unfold InvokeAny in H0. psimpl.
    eapply Invoke_pres_single.
    exact H0.
  }
  psimpl.
  eexists. split. easy.
  econstructor. 2: constructor.
  exists i. split. easy.
  apply StkInvoke. easy.
}
{
  unfold sub, subRelt, LiftSRelt.
  intros. psimpl.
  assert (exists x, σ = eq x).
  {
    unfold ReturnAny in H0. psimpl.
    eapply Return_pres_single.
    exact H0.
  }
  psimpl.
  eexists. split. easy.
  econstructor. 2: constructor.
  exists i. split. easy.
  apply StkReturn. easy.
}
{
  unfold LiftSPrec.
  intros. eexists.
  split. easy.
  constructor.
  {
    constructor.
    {
      exists [], None.
      split. 2: easy.
      now left.
    }
    { cbn. intros. easy. }
  }
  { cbn. intros. easy. }
}
{
  begin_stable.
  specialize (H0 x1 eq_refl). psimpl.
  eexists. split. easy.
  eapply ready_stable.
  psplit. exact H1. easy.
}
{
  unfold sub, subPrec.
  unfold LiftSRelt, LiftSPrec.
  intros. psimpl.
  assert (exists x, ρ = eq x).
  {
    eapply Return_pres_single.
    exact H0.
  }
  psimpl.
  eexists. split. easy.
  unfold TReturn, InterOStep in H0.
  psimpl. ddestruct H0. cbn in *.
  ddestruct H0. apply sing_elem in H5.
  psimpl. unfold mapRetPoss in H5. psimpl.
  destruct H2, done_ready0, ready_inv0.
  constructor.
  {
    constructor.
    {
      setoid_rewrite <- H4.
      setoid_rewrite H10.
      easy.
    }
    {
      intros.
      rewrite <- H4 in H2 at 1.
      rewrite <- H4 in H11 at 1.
      apply wait_inv0 in H2. 2: easy.
      dec_eq_nats i0 i.
      {
        destruct v0; destruct H2;
        now rewrite H5 in call_waiting.
      }
      {
        destruct v0; destruct H2;
        constructor; now rewrite ?H8, ?H9.
      }
    }
  }
  { now setoid_rewrite <- H4. }
}
{
  intros. destruct m.
  {
    eapply weakenPost.
    apply push_correct.
    {
      unfold sub, subRelt, LiftSPrec.
      intros. psimpl. eexists. split. easy.
      destruct v0. easy.
    }
  }
  {
    eapply weakenPost.
    apply pop_correct.
    {
      unfold sub, subRelt, LiftSPrec.
      intros. psimpl. eexists. easy.
    }
  }
}
{
  unfold ReturnStep, LiftSPrec.
  intros. psimpl. exists (eq x1).
  split. recons.
  split. intros. subst. recons.
  split.
  {
    intros. subst. destruct H2.
    now destruct ready_done0.
  }
  split.
  {
    unfold TReturn.
    split.
    {
      unfold Returned.
      intros. subst. destruct H2.
      now destruct ready_done0.
    }
    split.
    {
      split; cbn.
      {
        rewrite H0, eqb_id.
        now constructor.
      }
      { intros. now rewrite eqb_nid. }
    }
    easy.
  }
  {
    unfold LiftSRelt.
    intros. eq_inj H.
    exists (retPoss i x0).
    split.
    {
      set_ext y.
      unfold mapRetPoss, retPoss.
      split; intros; psimpl.
      {
        destruct y, x1. cbn in *.
        f_equal.
        { easy. }
        {
          extensionality j.
          dec_eq_nats i j.
          now rewrite eqb_id.
          now rewrite eqb_nid, H7.
        }
        {
          extensionality j.
          dec_eq_nats i j.
          now rewrite eqb_id.
          now rewrite eqb_nid, H8.
        }
      }
      {
        exists x0. cbn.
        rewrite eqb_id. destruct H2, ready_done0.
        repeat split; (easy || apply differ_pointwise_trivial).
      }
    }
    {
      apply StkReturn.
      exists _, m, v.
      {
        unfold TReturn.
        split.
        {
          unfold Returned.
          intros. subst. destruct H2.
          now destruct ready_done0.
        }
        split.
        {
          split; cbn.
          {
            rewrite H0, eqb_id.
            now constructor.
          }
          { intros. now rewrite eqb_nid. }
        }
        split.
        { easy. }
        {
          set_ext y.
          unfold mapRetPoss, retPoss.
          split; intros; psimpl.
          {
            exists x0. cbn.
            rewrite eqb_id. destruct H2, ready_done0.
            repeat split; (easy || apply differ_pointwise_trivial).
          }
          {
            destruct y, x1. cbn in *.
            f_equal.
            { easy. }
            {
              extensionality j.
              dec_eq_nats i j.
              now rewrite eqb_id.
              now rewrite eqb_nid, H7.
            }
            {
              extensionality j.
              dec_eq_nats i j.
              now rewrite eqb_id.
              now rewrite eqb_nid, H8.
            }
          }
        }
      }
    }
  }
}
Qed.

Require Import LHL.Core.Linearizability.

Theorem EBStackLin T A :
  Lin (overObj (VE T A :> EBStack A)) (VF T A).
eapply soundness.
apply EBStackCorrect.
Qed.