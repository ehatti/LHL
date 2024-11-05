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

From Coq Require Import
  Lists.List
  Logic.FunctionalExtensionality
  Logic.PropExtensionality.
Import ListNotations.

Unset Printing Records.

Definition E A :=
  ExchSig (option A) |+| WaitFreeStackSig A.

Definition VE T A : Spec T (E A) :=
  tensorSpec exchSpec wfStackSpec.

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
    forall (seq :
      exchSt s = ExchDef {i => Some v, j => Some w} {}
    ),
    IStep s i (RetEv (inl (Exch (Some v))) (Some (Some w))) t ->
    EBTran i s x t x
| StkPopAccept (s : ISt) x t y i j v :
    forall (seq :
      exchSt s = ExchDef {i => None, j => Some v} {}
    ),
    IStep s i (RetEv (inl (Exch None)) (Some (Some v))) t ->
    VisPossSteps
      x
      [(i, CallEv (Push v)); (i, RetEv (Push v) tt);
       (j, CallEv Pop); (j, RetEv Pop (Some v))]
      y ->
    EBTran i s x t y
| StkPopConflict (s : ISt) x t i j :
    forall (seq :
      exchSt s = ExchDef {i => None, j => None} {}
    ),
    IStep s i (RetEv (inl (Exch None)) (Some None)) t ->
    EBTran i s x t x
| StkFinish (s : ISt) x t i j (v w : option A) :
    forall (seq :
      exchSt s = ExchDef {j => w} {i => v}
    ),
    IStep s i (RetEv (inl (Exch v)) (Some w)) t ->
    EBTran i s x t x
| StkNoOp s x t i :
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
      stkSt s = WaitFreeStackDef vs pu /\
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

Record ReadyDoneExch {T A} (i : Name T) {R} (m : F A R) (r : R)
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
:= {
  exch_ready : ReadyDone i m r s x;
  ready_proper :
    match m with
    | Push v => exists j, exchSt s = ExchDef {j => None} {i => Some v}
    | Pop => exists j v, exchSt s = ExchDef {j => Some v} {i => None}
    end
}.

Lemma foldProg {E A} :
  forall p : Prog E A,
  match p with
  | Return v => Return v
  | Bind m k => Bind m k
  | NoOp p => NoOp p
  end = p.
intros.
destruct p; easy.
Qed.

Lemma stepLoopBind {E E' A B} e `{SigCoercion E' E} :
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
  loopAux e (ret (E:=E) (Continue (A:=A))) = NoOp (loop e).
intros. now rewrite frobProgId at 1.
Qed.

Lemma stepCall {E E' A B} {m : E' A} {k : A -> Prog E B} `{SigCoercion E' E} :
  (x <- call m; k x) = Bind (coerceOp _ m) k.
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
  unfold Stable, stablePost, stableRelt, sub, subRelt, subPrec;
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
  | [ H : WaitFreeStackStep ?s ?m ?t |- _ ] =>
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
        setoid_rewrite <- x at 1.
        recons. easy.
      }
      { now setoid_rewrite <- H6. }
    }
    {
      constructor.
      {
        setoid_rewrite <- x at 1.
        recons. easy.
      }
      { now setoid_rewrite <- H6. }
    }
  }
  {
    dsteps; simp_eqs.
    drecs. psimpl. simp_eqs.
    constructor.
    {
      setoid_rewrite <- x at 1.
      destruct_big_steps. dsteps.
      simp_eqs. rewrite H2 in x5.
      ddestruct x5. recons. easy.
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
  {
    dsteps; simp_eqs.
    drecs. psimpl. simp_eqs.
    constructor.
    {
      setoid_rewrite <- x at 1.
      recons. easy.
    }
    { now setoid_rewrite <- H7. }
  }
  {
    dsteps; simp_eqs.
    {
      drecs. psimpl. simp_eqs.
      constructor.
      {
        setoid_rewrite <- x at 1.
        recons. easy.
      }
      { now setoid_rewrite <- H6. }
    }
    {
      drecs. psimpl. simp_eqs.
      constructor.
      {
        setoid_rewrite <- x at 1.
        recons. easy.
      }
      { now setoid_rewrite <- H6. }
    }
  }
  {
    dsteps; simp_eqs;
    drecs; psimpl; simp_eqs.
    {
      constructor.
      {
        setoid_rewrite <- x at 1.
        destruct_big_steps. dsteps.
        {
          simp_eqs. rewrite H2 in x4.
          ddestruct x4. recons. easy.
        }
        {
          simp_eqs. rewrite H2 in x4.
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
          simp_eqs. rewrite H2 in x4.
          ddestruct x4.
        }
        {
          simp_eqs. rewrite H2 in x4.
          ddestruct x4. recons. easy.
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
      recons. easy.
    }
    { now setoid_rewrite <- H7. }
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
        setoid_rewrite H0.
        recons.
        rewrite <- x in x8.
        ddestruct x8. 
        rewrite <- x12 in x14.
        ddestruct x14.
        rewrite H9 in x4.
        ddestruct x4.
        rewrite <- x9 in x11.
        ddestruct x11.
        easy.
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
    rewrite H8 in H7. dsteps. simp_eqs.
    constructor.
    {
      setoid_rewrite <- H6.
      setoid_rewrite H.
      recons.
      rewrite <- x10 in x7.
      ddestruct x7.
      easy.
    }
    {
      intros.
      rewrite <- x4 in H7 at 1.
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
    now setoid_rewrite <- H7.
    now setoid_rewrite <- H5.
  }
  { dsteps. now setoid_rewrite <- H6. }
  { dsteps; now setoid_rewrite <- H5. }
  {
    dsteps.
    now setoid_rewrite <- H7.
    now setoid_rewrite <- H5.
    now setoid_rewrite <- H5.
  }
  { dsteps. now setoid_rewrite <- H6. }
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
Admitted.

Lemma ready_done_stable {T A} (i : Name T) {R} (m : F A R) (r : R) :
  SStable Rely (ReadyDone i m r).
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
Admitted.

Lemma ready_done_exch_stable {T A} (i : Name T) {R} (m : F A R) (r : R) :
  SStable Rely (ReadyDoneExch i m r).
begin_stable.
eapply SRTC_stable.
2: exact H. 2: exact H0.
clear. intros.
destruct H.
constructor.
{
  eapply ready_done_stable.
  psplit. exact exch_ready0.
  econstructor.
  2: constructor.
  easy.
}
Admitted.

Lemma complete_tran {T A} (i : Name T) (v : option A) {R} (m : F A R) (r : R) :
  forall s x t y,
  Complete i v s x ->
  Rely s x t y ->
  Complete i v t y \/ ReadyDoneExch i m r t y.
Admitted.

Lemma push_correct {T A} {i : Name T} {v : A} :
  VerifyProg i (LiftSRelt Rely) (LiftSRelt Guar)
    (prComp (LiftSPrec (Ready i))
            (TInvoke (EBStack A) i _ (Push v)) ->>
     LiftSRelt Rely)
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
    VerifyProg i (LiftSRelt Rely) (LiftSRelt Guar)
      P
      (push v)
      (fun _ _ _ => LiftSPrec (ReadyDone i (Push v) tt))
).
{ intros. now apply H. }
cofix rec. intros P impH. unfold push, loop.
rewrite stepLoopBind, stepCall.
eapply SafeBind with
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
          rewrite H in x3.
          ddestruct x3. eexists _, _.
          split. symmetry. exact x. easy.
        }
        {
          rewrite H in x3.
          ddestruct x3. eexists _, _.
          split. symmetry. exact x. easy.
        }
        { now setoid_rewrite <- H6. }
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
      clear - H2 x2.
      eassert _ by (eapply projT2_eq with (p:=H2)).
      simpl in *.
      assert (projT1_eq H2 = x2) by apply proof_irrelevance.
      rewrite H in X. clear H2 H.
      assert (RN = unit) by now apply StkRet_inj.
      subst. ddestruct x2.
      easy.
    }
    destruct H3, wait_ready0.
    destruct ready_wait0, ready_inv0.
    destruct_all. rewrite H in x1 at 1.
    ddestruct x1. rename x2 into vs.
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
      eapply erase_vis. exact H7.
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
          cbn. rewrite H, <- x at 1.
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
    psimpl. rewrite <- x1 in H3 at 1. ddestruct H3.
    ddestruct H2.
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
            exists x2, (Some (None, MkWFSPend i0 mo)).
            easycons.
          }
          { now setoid_rewrite <- H7. }
        }
        { now setoid_rewrite <- H7. }
      }
      { constructor; easy. }
    }
    {
      eexists. split. easy. eq_inj H2.
      eapply StkPushFail with
        (i:=i) (v:=v).
      constructor.
      {
        constructor; cbn. easy.
        intros. now rewrite H0.
      }
      {
        cbn. rewrite <- x1, <- x at 1.
        easycons.
      }
    }
  }
  {
    rewrite stepLoopBind, stepCall.
    eapply SafeBind with
      (QI:=fun _ _ => LiftSPrec (fun s x =>
        Complete i (Some v) s x \/
        ReadyDoneExch i (Push v) tt s x))
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
        eapply complete_tran.
        exact H. easy.
      }
      {
        right.
        eapply ready_done_exch_stable.
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
            now rewrite <- H6 at 1.
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
                  now rewrite <- H6 at 1.
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
        {
          exists (eq x3).
          split.
          { recons. }
          split.
          { intros. subst. recons. }
          split.
          {
            exists x3. split. easy.
            destruct H3, exch_ready0.
            destruct done_ready0, ready_inv0.
            constructor.
            {
              constructor.
              {
                constructor.
                { now setoid_rewrite <- H6 at 1. }
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
            destruct H3. psimpl.
            eapply StkFinish with
              (i:=i) (v:= Some v).
            { exact H3. }
            constructor.
            {
              constructor; cbn. easy.
              intros. now rewrite H0.
            }
            { easy. }
          }
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
        2:{
          destruct H4, exch_ready0.
          destruct done_ready0, ready_inv0.
          psimpl.
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
                  { now setoid_rewrite <- H7 at 1. }
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
                (i:=i) (v:=v) (w:=w).
              { symmetry. exact x1. }
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
        apply SafeNoOp with
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
            eapply StkNoOp with (i:=i).
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
  VerifyProg i (LiftSRelt Rely) (LiftSRelt Guar)
    (prComp (LiftSPrec Inv) (TInvoke (EBStack A) i _ Pop) ->> LiftSRelt Rely)
    pop
    (fun r _ _ => LiftSPrec (fun s x =>
      Inv s x /\
      Returned i Pop r s (eq x))).
eapply weakenPrec with
  (P:=fun _ _ => LiftSPrec (fun s x =>
    Inv s x /\
    Waiting i Pop x)).
2:{
  unfold sub, subRelt.
  intros. psimpl.
  admit.
}
cut (
  forall P,
  P ==> (fun _ _ => LiftSPrec (fun s x =>
    Inv s x /\
    Waiting i Pop x)) ->
    VerifyProg i (LiftSRelt (Rely (A:=A))) (LiftSRelt Guar)
      P
      pop
      (fun r _ _ => LiftSPrec (fun s x =>
        Inv s x /\
        Returned i Pop r s (eq x)))
).
{ intros. now apply H. }
cofix rec. intros P impH. unfold pop, loop.
rewrite stepLoopBind, stepCall.
eapply SafeBind with
  (QI:=fun _ _ => LiftSPrec (fun s x =>
    Inv s x /\
    Waiting i Pop x))
  (QR:=fun r _ _ => LiftSPrec (fun s x =>
    Inv s x /\
    match r with
    | PASS v => Done i Pop v x
    | FAIL => Waiting i Pop x
    end)).
{
  admit.
}
{
  admit.
}
{
  clear rec. begin_commit.
  psimpl. apply impH in H.
  clear impH. psimpl.
  unfold LiftSPrec in H. psimpl.
  exists (eq x).
  split.
  { now exists x. }
  split.
  {
    intros. subst. exists σ.
    repeat (constructor || easy).
  }
  split.
  {
    exists x. split. easy.
    split.
    {
      destruct H7. psimpl.
      ddestruct H2.
      {
        constructor.
        {
          eexists vs, _.
          split. symmetry. exact x.
          rewrite <- x3 in H. ddestruct H.
          exact H7.
        }
        { now setoid_rewrite <- H6 at 1. }
      }
      {
        constructor.
        {
          eexists vs, _.
          split. symmetry. exact x.
          rewrite <- x3 in H. ddestruct H.
          exact H7.
        }
        { now setoid_rewrite <- H6 at 1. }
      }
    }
    { easy. }
  }
  {
    exists x. split. easy.
    eq_inj H. apply StkCallPop with
      (i:=i).
    constructor.
    {
      constructor; cbn.
      easy. intros. now rewrite H0.
    }
    { easy. }
  }
}
intros. destruct v.
{
  split.
  {
    begin_commit. do 5 destruct H.
    clear H. psimpl. psimpl.
    remember (PASS v).
    move Heqs0 at bottom.
    ddestruct H.
    {
      subst.
      exfalso.
      clear - H2 x2.
      eassert _ by (eapply projT2_eq with (p:=H2)). simpl in *.
      assert (projT1_eq H2 = x2) by apply proof_irrelevance.
      rewrite H in X. clear H2 H.
      assert (RN = option A) by now apply StkRet_inj. subst.
      assert (x2 = eq_refl) by apply proof_irrelevance. subst.
      easy.
    }
    {
      ddestruct Heqs0.
      set (x3' :=
        comRetPoss i
          (comInvPoss i
            x3
            Pop
            (AtomicStackDef (v0 :: vs) (Some (MkStkPend i Pop))))
          Pop
          (AtomicStackDef vs None)
          (Some v0)
      ).
      exists (eq x3').
      assert (
        VisPossSteps
          x3
          ([(i, CallEv Pop)] ++ [(i, RetEv Pop (Some v0))])
          x3'
      ).
      {
        apply retStep.
        apply callStep with (p:=[]).
        constructor.
        {
          destruct H3, H4. psimpl.
          rewrite <- x1 in H. ddestruct H.
          rewrite H3. repeat (constructor || easy).
        }
        {
          cbn. rewrite eqb_id.
          destruct H4, H3. psimpl.
          repeat (constructor || easy).
        }
      }
      split.
      { repeat eexists. }
      split.
      {
        intros. subst.
        eexists. split. easy.
        eapply erase_vis. exact H.
      }
      split.
      {
        eexists. split. easy.
        split.
        {
          destruct H3. psimpl.
          constructor.
          {
            exists vs, None. cbn.
            repeat (constructor || easy).
          }
          {
            setoid_rewrite <- H7.
            intros. apply pop_offer_waiting0
              with (i:=i0) in H9. all: try easy.
            admit.
          }
        }
        {
          constructor; cbn;
          now rewrite eqb_id.
        }
      }
      {
        eexists. split. easy.
        apply StkPopPass with
          (i:=i) (v:= Some v0).
        {
          constructor.
          {
            constructor; cbn.
            easy. intros. now rewrite H0.
          }
          {
            cbn. split. 2: easy.
            rewrite <- x1, <- x at 1.
            constructor.
          }
        }
        { now eq_inj H8. }
      }
    }
    {
      ddestruct Heqs0.
      set (x3' :=
        comRetPoss i
          (comInvPoss i
            x3
            Pop
            (AtomicStackDef [] (Some (MkStkPend i Pop))))
          Pop
          (AtomicStackDef [] None)
          None
      ).
      exists (eq x3').
      assert (
        VisPossSteps
          x3
          ([(i, CallEv Pop)] ++ [(i, RetEv Pop None)])
          x3'
      ).
      {
        apply retStep.
        apply callStep with (p:=[]).
        constructor.
        {
          destruct H3, H4. psimpl.
          rewrite <- x1 in H. ddestruct H.
          rewrite H3. repeat (constructor || easy).
        }
        {
          cbn. rewrite eqb_id.
          destruct H4, H3. psimpl.
          repeat (constructor || easy).
        }
      }
      split.
      { repeat eexists. }
      split.
      {
        intros. subst.
        eexists. split. easy.
        eapply erase_vis. exact H.
      }
      split.
      {
        eexists. split. easy.
        split.
        {
          destruct H3. psimpl.
          constructor.
          {
            exists [], None. cbn.
            repeat (constructor || easy).
          }
          {
            setoid_rewrite <- H7.
            intros. apply pop_offer_waiting0
              with (i:=i0) in H9. all: try easy.
            admit.
          }
        }
        {
          constructor; cbn;
          now rewrite eqb_id.
        }
      }
      {
        eexists. split. easy.
        apply StkPopPass with
          (i:=i) (v:=None).
        {
          constructor.
          {
            constructor; cbn.
            easy. intros. now rewrite H0.
          }
          {
            cbn. split. 2: easy.
            rewrite <- x1, <- x at 1.
            constructor.
          }
        }
        { now eq_inj H8. }
      }
    }
  }
  {
    rewrite stepLoopBreak. apply SafeReturn.
    unfold sub, subRelt, LiftSPrec. intros. psimpl.
    exists x3. split. easy. split.
    { easy. }
    {
      destruct H3. unfold Returned.
      intros. subst. easy.
    }
  }
}
{
  split.
  {
    clear rec. begin_commit.
    do 5 destruct H. clear H.
    psimpl. psimpl. exists (eq x3).
    split.
    { now exists x3. }
    split.
    {
      intros. subst. eexists.
      repeat (constructor || easy).
    }
    split.
    {
      exists x3. split. easy.
      split.
      {
        destruct H3. psimpl.
        constructor. ddestruct H.
        {
          eexists vs, _. split.
          symmetry. exact x.
          rewrite <- x4 in H3.
          ddestruct H3. exact H8.
        }
        { now setoid_rewrite <- H7 at 1. }
      }
      { easy. }
    }
    {
      eexists. split. easy.
      eq_inj H8. apply StkPopFail with
        (i:=i).
      constructor.
      {
        constructor; cbn.
        easy. intros. now rewrite H0.
      }
      { easy. }
    }
  }
  {
    rewrite stepLoopBind, stepCall.
    eapply SafeBind with
      (QI:=fun _ _ => LiftSPrec (fun s x =>
        Inv s x /\
        ((Waiting i Pop x /\
          (Offered1 i None s x \/
           exists j v, i <> j /\ Offered2 i j None v s x)) \/
         (exists v j, i <> j /\
            Done i Pop (Some v) x /\
            PopAccepted i j v s x))))
      (QR:=fun r _ _ => LiftSPrec (fun s x =>
        Inv s x /\
        (match r with
         | Some (Some v) => Done i Pop (Some v) x
         | _ => Waiting i Pop x
         end))).
    {
      clear rec. begin_stable.
      specialize (H0 x1 eq_refl). psimpl.
      exists x0. split. easy.
      split.
      {
        apply Inv_stable.
        psplit. exact H1.
        easy.
      }
      {
        admit.
      }
    }
    {
      clear rec. begin_stable.
      specialize (H0 x1 eq_refl). psimpl.
      exists x0. split. easy. split.
      {
        apply Inv_stable.
        psplit. exact H1.
        easy.
      }
      {
        admit.
      }
    }
    {
      clear rec. begin_commit.
      rewrite <- reltCompAssoc in H.
      do 5 destruct H. clear H. do 2 psimpl.
      ddestruct H.
      {
        exists (eq x3).
        split.
        { recons. }
        split.
        {
          intros. subst.
          recons.
        }
        split.
        {
          exists x3. split. easy.
          split.
          {
            destruct H3. psimpl.
            constructor.
            {
              exists x2, x4.
              rewrite <- H7 at 1. easy.
            }
            {
              intros.
              rewrite <- x in H8 at 1.
              ddestruct H8. apply contains_invert in H9.
              destruct H9. now ddestruct H8.
              now apply contains_contr in H8.
            }
          }
          {
            left. split. easy.
            left. easy.
          }
        }
        {
          exists x3. split. easy.
          eq_inj H. eapply StkOffer.
          constructor; cbn.
          {
            constructor; cbn.
            exact H1. intros. now rewrite H0.
          }
          {
            rewrite <- x1, <- x at 1.
            repeat (easy || constructor).
          }
        }
      }
      {
        exists (eq x3).
        split.
        { recons. }
        split.
        {
          intros. subst.
          recons.
        }
        split.
        {
          exists x3. split. easy.
          split.
          {
            destruct H3. psimpl.
            constructor.
            {
              exists x4, x5.
              now rewrite <- H7 at 1.
            }
            {
              intros.
              rewrite <- x in H9 at 1. ddestruct H9.
              apply contains_invert in H10.
              destruct H10. now ddestruct H9.
              apply contains_invert in H9.
              destruct H9. ddestruct H9.
              eapply pop_offer_waiting0.
              symmetry. exact x2.
              apply contains_triv. easy.
              now apply contains_contr in H9.
            }
          }
          {
            left. split. easy.
            right. exists i0, x1.
            easy.
          }
        }
        {
          exists x3. split. easy.
          eq_inj H8. eapply StkOffer.
          constructor; cbn.
          {
            constructor; cbn.
            exact H1. intros. now rewrite H0.
          }
          {
            rewrite <- x2, <- x at 1.
            repeat (easy || constructor).
          }
        }
      }
    }
    intros.
    rename v into r.
    assert (
      (exists v, r = Some (Some v)) \/
      forall v, r <> Some (Some v)).
    {
      destruct r. destruct o.
      left. repeat econstructor.
      right. easy.
      right. easy.
    }
    destruct H. subst.
    {
      psimpl. clear rec.
      rename x into v.
      split.
      {
        begin_commit. do 5 destruct H.
        clear H. do 2 psimpl.
        destruct H3. psimpl. rename x into vs.
        repeat match goal with
        | [ H : ?P \/ ?Q |- _ ] =>
            destruct H
        | [ H : ?P /\ ?Q |- _ ] =>
            destruct H
        end; psimpl.
        {
          (*
          revoke case is impossible here because
          we have assumed the return value is
          Some None. the revoke case is handled
          in the v0 <> Some None branch
          *)
          destruct H9.
          rewrite exch_offered0 in H at 1.
          ddestruct H; simp_sets.
        }
        {
          (* accept *)
          destruct H10.
          rewrite exchs_offered0 in H at 1.
          remember (Some (Some v)). move Heqo at bottom.
          ddestruct H; simp_sets. ddestruct Heqo.
          rename x5 into j.
          set (x3' :=
            comRetPoss i
              (comInvPoss i
                (comRetPoss j
                  (comInvPoss j
                    x3
                    (Push v)
                    (AtomicStackDef vs (Some (MkStkPend j (Push v)))))
                  (Push v)
                  (AtomicStackDef (v :: vs) None)
                  tt)
                Pop
                (AtomicStackDef (v :: vs) (Some (MkStkPend i Pop))))
              Pop
              (AtomicStackDef vs None)
              (Some v)
          ).
          assert (
            VisPossSteps
              x3
              ([] ++
               [(i, CallEv (Push v))] ++ [(i, RetEv (Push v) tt)] ++
               [(j, CallEv Pop)]      ++ [(j, RetEv Pop (Some v))])
              x3'
          ).
          {
            (* apply pop_offer_waiting0
              with (i:=j)
              in exchs_offered0.
            2:{ rewrite insert_perm. apply contains_triv. }
            destruct exchs_offered0.
            repeat rewrite app_assoc.
            apply retStep. apply callStep.
            apply retStep. apply callStep.
            constructor.
            {
              destruct H4. rewrite H8.
              repeat (easy || constructor).
            }
            {
              cbn. rewrite eqb_id. destruct H4.
              repeat (easy || constructor).
            }
            {
              cbn. rewrite eqb_nid; try easy.
              repeat (easy || constructor).
            }
            {
              cbn. rewrite eqb_id, eqb_nid.
              repeat (easy || constructor).
              easy.
            }  *)
            admit.
          }
          exists (eq x3').
          split.
          { repeat econstructor. }
          split.
          {
            intros. subst.
            exists x3. split. easy.
            eapply erase_vis.
            exact H10.
          }
          split.
          {
            exists x3'. split. easy.
            split.
            {
              constructor.
              {
                exists vs, x1.
                now rewrite <- H7 at 1.
              }
              {
                setoid_rewrite <- x.
                intros. ddestruct H11.
                apply contains_invert in H12.
                destruct H12. ddestruct H11.
                exfalso. apply H13.
                repeat econstructor.
                apply contains_triv.
                exfalso. apply H13.
                repeat econstructor.
                apply contains_triv.
              }
            }
            {
              subst x3'.
              constructor; cbn;
              now rewrite eqb_id.
            }
          }
          {
            exists x3'. split. easy.
            eq_inj H11. eapply StkPopAccept
              with (i:=i) (v:=v).
            {
              constructor; cbn.
              {
                constructor; cbn. easy.
                intros. now rewrite H0.
              }
              {
                rewrite exchs_offered0, <- x at 1.
                repeat (easy || constructor).
              }
            }
            { exact H10. }
          }
        }
        {
          (* finish *)
          destruct H10.
          exists (eq x3).
          split.
          { repeat econstructor. }
          split.
          {
            intros. subst. eexists.
            repeat constructor.
          }
          split.
          {
            exists x3. split. easy.
            split.
            {
              constructor.
              {
                exists vs, x1.
                now rewrite <- H7 at 1.
              }
              {
                intros.
                rewrite paccepted0 in H at 1.
                ddestruct H; simp_sets.
                rewrite <- x in H10 at 1.
                ddestruct H10.
                now apply contains_contr in H11.
              }
            }
            {
              remember (Some (Some v)).
              move Heqo at bottom.
              ddestruct H.
              {
                ddestruct Heqo.
                rewrite paccepted0 in x4 at 1.
                ddestruct x4. simp_sets.
              }
              {
                ddestruct Heqo.
                rewrite paccepted0 in x6 at 1.
                ddestruct x6. now simp_sets.
              }
              { ddestruct Heqo. }
            }
          }
          {
            exists x3. split. easy.
            eq_inj H10. eapply StkPopFinish
              with (i:=i) (v:=v).
            constructor.
            {
              constructor; cbn.
              easy. intros. now rewrite H0.
            }
            { easy. }
          }
        }
      }
      {
        rewrite stepLoopBreak.
        apply SafeReturn.
        unfold sub, subRelt.
        intros. unfold LiftSPrec in H.
        psimpl. exists x4. destruct H3.
        repeat (easy || constructor).
        all: (subst; easy).
      }
    }
    {
      split.
      {
        begin_commit.
        repeat rewrite <- reltCompAssoc in H0.
        do 5 destruct H0. clear H0. psimpl.
        destruct H4. psimpl. rename x into vs.
        destruct H5; destruct H5; psimpl.
        {
          destruct H10.
          {
            destruct H10. ddestruct H0.
            {
              rewrite exch_offered0 in x2 at 1.
              ddestruct x2. simp_sets.
            }
            {
              rewrite exch_offered0 in x4 at 1.
              ddestruct x4. simp_sets.
            }
            {
              clear x2. symmetry in x.
              exists (eq x3).
              split.
              { repeat econstructor. }
              split.
              {
                intros. subst.
                repeat econstructor.
              }
              split.
              {
                exists x3. split. easy.
                split.
                {
                  constructor.
                  {
                    exists vs, x1.
                    now rewrite <- H7 at 1.
                  }
                  {
                    intros.
                    rewrite x in H0 at 1. ddestruct H0.
                    now apply contains_contr in H10.
                  }
                }
                { easy. }
              }
              {
                exists x3. split. easy.
                eq_inj H0. eapply StkRevoke
                  with (i:=i) (v:=None).
                constructor.
                {
                  constructor; cbn. easy.
                  intros. now rewrite H1.
                }
                {
                  cbn. rewrite exch_offered0, x at 1.
                  repeat (easy || constructor).
                }
              }
            }
          }
          {
            psimpl. destruct H11.
            ddestruct H0.
            {
              rewrite exchs_offered0 in x4 at 1.
              ddestruct x4. simp_sets.
              rename x5 into j. rename x2 into w.
              destruct w as [v | ].
              {
                pose (x3' :=
                  comRetPoss i
                    (comInvPoss i
                      (comRetPoss j
                        (comInvPoss j
                          x3
                          (Push v)
                          (AtomicStackDef vs (Some (MkStkPend j (Push v)))))
                        (Push v)
                        (AtomicStackDef (v :: vs) None)
                        tt)
                      Pop
                      (AtomicStackDef (v :: vs) (Some (MkStkPend i Pop))))
                    Pop
                    (AtomicStackDef vs None)
                    (Some v)
                ).
                assert (
                  VisPossSteps
                    x3
                    ([] ++
                    [(i, CallEv (Push v))] ++ [(i, RetEv (Push v) tt)] ++
                    [(j, CallEv Pop)]      ++ [(j, RetEv Pop (Some v))])
                    x3'
                ).
                {
                  admit.
                }
                exists (eq x3').
                split.
                { repeat econstructor. }
                split.
                {
                  intros. subst.
                  eexists. split. easy.
                  eapply erase_vis.
                  exact H11.
                }
                split.
                {
                  exists x3'. split. easy.
                  split.
                  {
                    constructor.
                    {
                      exists vs, x1.
                      now rewrite <- H7 at 1.
                    }
                    {
                      setoid_rewrite <- x4 at 1.
                      intros. ddestruct H12.
                      exfalso. apply H14.
                      repeat econstructor.
                      apply contains_triv.
                    }
                  }
                  {
                    constructor; cbn;
                    now rewrite eqb_id.
                  }
                }
                {
                  exists x3'. split. easy.
                  eq_inj H12. apply StkPopAccept
                    with (i:=i) (j:=j) (v:=v).
                  {
                    constructor.
                    {
                      constructor; cbn. easy.
                      intros. now rewrite H1.
                    }
                    {
                      cbn. rewrite exchs_offered0, <- x4 at 1.
                      repeat (easy || constructor).
                    }
                  }
                  { easy. }
                }
              }
              {
                exists (eq x3).
                split.
                { repeat econstructor. }
                split.
                {
                  intros. subst.
                  repeat econstructor.
                }
                split.
                {
                  exists x3. split. easy.
                  split.
                  {
                    constructor.
                    {
                      exists vs, x1.
                      now rewrite <- H7 at 1.
                    }
                    {
                      setoid_rewrite <- x4 at 1.
                      intros. ddestruct H11.
                      apply contains_invert in H12.
                      destruct H12. now ddestruct H11.
                      now apply contains_contr in H11.
                    }
                  }
                  { easy. }
                }
                {
                  exists x3. split. easy.
                  eq_inj H11. apply StkPopConflict
                    with (i:=i).
                  constructor.
                  {
                    constructor; cbn. easy.
                    intros. now rewrite H1.
                  }
                  {
                    cbn. rewrite exchs_offered0, <- x4 at 1.
                    repeat (easy || constructor).
                  }
                }
              }
            }
            {
              rewrite exchs_offered0 in x6 at 1.
              ddestruct x6. simp_sets.
            }
            {
              rewrite exchs_offered0 in x4 at 1.
              ddestruct x4. simp_sets.
            }
          }
        }
        {
          destruct H11.
          ddestruct H0.
          {
            rewrite paccepted0 in x4 at 1.
            ddestruct x4. simp_sets.
          }
          {
            rewrite paccepted0 in x6 at 1.
            ddestruct x6. simp_sets.
            exists (eq x3).
            split.
            { repeat econstructor. }
            split.
            {
              intros. subst.
              repeat econstructor.
            }
            split.
            {
              exists x3. split. easy.
              split.
              {
                constructor.
                {
                  exists vs, x1.
                  now rewrite <- H7 at 1.
                }
                {
                  setoid_rewrite <- x6 at 1.
                  intros. ddestruct H11.
                  now apply contains_contr in H12.
                }
              }
              { easy. }
            }
            {
              exists x3. split. easy.
              eq_inj H11. eapply StkPopFinish
                with (i:=i).
              constructor.
              {
                constructor; cbn. exact H2.
                intros. now rewrite H1.
              }
              {
                cbn. rewrite paccepted0, <- x6 at 1.
                repeat (easy || constructor).
              }
            }
          }
          {
            subst.
            rewrite paccepted0 in x4 at 1.
            ddestruct x4. simp_sets.
          }
        }
      }
      {
        eassert (
          match r with
          | Some (Some v) => ret (Break (Some v))
          | _ => ret Continue
          end = ret Continue
        ).
        {
          destruct r.
          destruct o.
          now specialize (H a).
          easy.
          easy.
        }
        rewrite H0. clear H0.
        rewrite stepLoopCont.
        apply SafeNoOp with
          (QS:=fun _ _ => LiftSPrec (fun s x =>
            Inv s x /\
            Waiting i Pop x)).
        {
          (* Inv and Waiting stable *)
          clear rec. begin_stable.
          specialize (H1 x1 eq_refl). psimpl.
          exists x0. split. easy. split.
          {
            apply Inv_stable.
            psplit. exact H2.
            easy.
          }
          {
            admit.
          }
        }
        {
          unfold SilentStep. intros.
          unfold LiftSPrec in H0.
          repeat rewrite <- reltCompAssoc in H0.
          do 5 destruct H0. clear H0. psimpl.
          split.
          {
            exists x3. split. easy.
            ddestruct H2. destruct H3. psimpl.
            split.
            {
              constructor.
              {
                exists x4, x5.
                easy.
              }
              { easy. }
            }
            {
              destruct r. destruct o.
              now specialize (H a).
              easy.
              easy.
            }
          }
          {
            exists x3. split. easy.
            eq_inj H0. eapply StkNoOp.
            split. 2: easy.
            constructor; cbn.
            exact H2. intros. now rewrite H1.
          }
        }
        {
          eapply rec.
          unfold sub, subRelt.
          intros. psimpl. easy.
        }
      }
    }
  }
}