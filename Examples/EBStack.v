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

Notation IStep s i e t :=
  (InterStep (EBStack _) s (i, UEvent (Some e)) t).

Variant EBTran {T A} : Relt T A :=
| StkCallPush s x t i v :
    IStep s i (CallEv (inr (WFPush v))) t ->
    EBTran s x t x
| StkPushPass s x t y i v :
    IStep s i (RetEv (inr (WFPush v)) (PASS tt)) t ->
    VisPossSteps x [(i, CallEv (Push v)); (i, RetEv (Push v) tt)] y ->
    EBTran s x t y
| StkPushFail s x t i v :
    IStep s i (RetEv (inr (WFPush v)) FAIL) t ->
    EBTran s x t x
| StkCallPop s x t i :
    IStep s i (CallEv (inr WFPop)) t ->
    EBTran s x t x
| StkPopPass s x t y i v :
    IStep s i (RetEv (inr WFPop) (PASS v)) t ->
    VisPossSteps x [(i, CallEv Pop); (i, RetEv Pop v)] y ->
    EBTran s x t y
| StkPopFail s x t i :
    IStep s i (RetEv (inr WFPop) FAIL) t ->
    EBTran s x t x
| StkOffer s x t i v :
    IStep s i (CallEv (inl (Exch v))) t ->
    EBTran s x t x
| StkRevoke s x t i v :
    IStep s i (RetEv (inl (Exch v)) None) t ->
    EBTran s x t x
| StkPushAccept s x t y i j v :
    IStep s i (RetEv (inl (Exch (Some v))) (Some None)) t ->
    VisPossSteps
      x
      [(i, CallEv (Push v)); (i, RetEv (Push v) tt);
       (j, CallEv Pop); (j, RetEv Pop (Some v))]
      y ->
    EBTran s x t y
| StkPopAccept s x t y i j v :
    IStep s i (RetEv (inl (Exch None)) (Some (Some v))) t ->
    VisPossSteps
      x
      [(i, CallEv (Push v)); (i, RetEv (Push v) tt);
       (j, CallEv Pop); (j, RetEv Pop (Some v))]
      y ->
    EBTran s x t y
| StkPushFinish s x t i v :
    IStep s i (RetEv (inl (Exch (Some v))) (Some None)) t ->
    EBTran s x t x
| StkPushConflict s x t i v w :
    IStep s i (RetEv (inl (Exch (Some v))) (Some (Some w))) t ->
    EBTran s x t x
| StkPopFinish s x t i v :
    IStep s i (RetEv (inl (Exch None)) (Some (Some v))) t ->
    EBTran s x t x
| StkPopConflict s x t i :
    IStep s i (RetEv (inl (Exch None)) (Some None)) t ->
    EBTran s x t x
| StkNoOp s x t i :
    InterStep (EBStack _) s (i, UEvent None) t ->
    EBTran s x t x.

Definition Guar {T A} : Relt T A :=
  EBTran.

Definition Rely {T A} : Relt T A :=
  SRTC EBTran.

Record Waiting {T A R} (i : Name T) (m : F A R)
  (x : Poss (VF T A))
:= {
  call_waiting : PCalls x i = CallPoss m;
  ret_waiting : PRets x i = RetIdle;
}.

Record Done {T A R} (i : Name T) (m : F A R) (v : R)
  (x : Poss (VF T A))
:= {
  call_done : PCalls x i = CallDone m;
  ret_done : PRets x i = RetPoss m v
}.

Record Offered1 {T A} (i : Name T) (v : option A)
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
:= {
  exch_offered : exchSt s = ExchDef {i => v} {};
}.

Record Offered2 {T A} (i j : Name T) (v w : option A)
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
:= {
  exchs_offered : exchSt s = ExchDef {i => v, j => w} {};
}.

Record Accepted {T A} (i j : Name T) (v : A)
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
:= {
  accepted : exchSt s = ExchDef {j => None} {i => Some v};
  push_done : Done i (Push v) tt x;
  (* pop_done : Done i Pop (Some v) x *)
}.

Record PopAccepted {T A} (i j : Name T) (v : A)
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
:= {
  paccepted : exchSt s = ExchDef {j => Some v} {i => None};
  pop_done : Done i Pop (Some v) x
}.


Record Conflicted {T A} (i j : Name T) (v w : A)
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
:= {
  conflicted : exchSt s = ExchDef {i => Some v} {j => Some w}
}.

Record Inv {T A}
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
:= {
  state_consistent :
    exists vs pu,
      stkSt s = WaitFreeStackDef vs pu /\
      PState x = AtomicStackDef vs None;
  pop_offer_waiting :
    forall i os cs,
      exchSt s = ExchDef os cs ->
      (i, None) ∈ os ->
      ~(exists v j,
        (j, Some v) ∈ cs) ->
      Waiting i Pop x
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
Admitted.

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

Ltac eq_inj H :=
  apply eq_inj in H; subst.

Ltac begin_commit :=
  unfold Commit, LiftSPrec; intros.

Ltac inst_eqs :=
  repeat match goal with
  | [ H : forall (x : Poss (VF _ _)), eq ?y = eq x -> _ |- _ ] =>
      specialize (H ?y eq_refl); psimpl
  end.

Ltac begin_stable :=
  unfold Stable, stablePost, stableRelt, sub, subRelt;
  unfold ReltToPrec, LiftSPrec, LiftSRelt;
  intros; psimpl.

Ltac simp_sets :=
  repeat match goal with
  | [ H : {?i => ?v} = {} |- _ ] =>
      now apply disj_cons in H
  | [ H : {} = {?i => ?v} |- _ ] =>
      symmetry in H;
      now apply disj_cons in H
  | [ H : insert ?x ?xs = insert ?y ?ys |- _ ] =>
      let H2 := fresh in
      let H3 := fresh in
      apply insert_cong in H;
      destruct H as [H2 H3];
      ddestruct H2
  | [ H : emp = emp |- _ ] =>
      clear H
  end.

(* Lemma Waiting_tran {T A} :
  forall (i : Name T) R (m : F A R),
  forall s x t y,
  Waiting i m x ->
  Rely s x t y ->
  (Waiting i m y \/
   exists).
Admitted. *)

Lemma Done_stable {T A} :
  forall (i : Name T) R (m : F A R),
  forall s x t y v,
  Done i m v x ->
  Rely s x t y ->
  Done i m v y.
Admitted.

Lemma Inv_stable {T A} :
  SStable (T:=T) Rely (Inv (A:=A)).
Admitted.

Axiom StkRet_inj : forall A B, StkRet A = StkRet B -> A = B.

Lemma push_correct {T A} {i : Name T} {v : A} :
  VerifyProg i (LiftSRelt Rely) (LiftSRelt Guar)
    (prComp (LiftSPrec Inv) (TInvoke (EBStack A) i _ (Push v)) ->> LiftSRelt Rely)
    (push v)
    (fun _ _ _ => LiftSPrec (fun s x =>
      Inv s x /\
      Returned i (Push v) tt s (eq x))).
eapply weakenPrec with
  (P:=fun _ _ => LiftSPrec (fun s x =>
    Inv s x /\
    Waiting i (Push v) x)).
2:{
  unfold sub, subRelt.
  intros. psimpl.
  admit.
}
cut (
  forall P,
  P ==> (fun _ _ => LiftSPrec (fun s x =>
    Inv s x /\
    Waiting i (Push v) x)) ->
    VerifyProg i (LiftSRelt Rely) (LiftSRelt Guar)
      P
      (push v)
      (fun _ _ _ => LiftSPrec (fun s x =>
        Inv s x /\
        Returned i (Push v) tt s (eq x)))
).
{ intros. now apply H. }
cofix rec. intros P impH. unfold push, loop.
rewrite stepLoopBind, stepCall.
eapply SafeBind with
  (QI:=fun _ _ => LiftSPrec (fun s x =>
    Inv s x /\
    Waiting i (Push v) x))
  (QR:=fun r _ _ => LiftSPrec (fun s x =>
    Inv s x /\
    match r with
    | PASS tt => Done i (Push v) tt x
    | FAIL => Waiting i (Push v) x
    end)).
{
  clear rec impH. begin_stable.
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
  clear rec impH. begin_stable.
  specialize (H0 x1 eq_refl). psimpl.
  exists x0. split. easy.
  split.
  {
    apply Inv_stable.
    psplit. exact H1.
    easy.
  }
  {
    destruct v0.
    {
      destruct v0.
      eapply Done_stable.
      exact H2. exact H0.
    }
    {
      admit.
    }
  }
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
    eq_inj H. apply StkCallPush with
      (i:=i) (v:=v).
    constructor.
    {
      constructor; cbn.
      easy. intros. now rewrite H0.
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
        ([(i, CallEv (Push v))] ++ [(i, RetEv (Push v) tt)])
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
          exists (v :: vs), None.
          cbn. repeat (constructor || easy).
        }
        {
          setoid_rewrite <- H7.
          intros. apply pop_offer_waiting0
            with (i:=i0) in H9. 2: easy.
          assert (i <> i0).
          {
            unfold not. intros. subst.
            destruct H4, H9.
            rewrite call_waiting0 in call_waiting1.
            ddestruct call_waiting1.
          }
          destruct H9.
          constructor; cbn;
          now rewrite eqb_nid.
          easy.
        }
      }
      {
        constructor; cbn;
        now rewrite eqb_id.
      }
    }
    {
      eexists. split. easy.
      apply StkPushPass with
        (i:=i) (v:=v).
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
    rewrite stepLoopBreak. apply SafeReturn.
    unfold sub, subRelt. intros. psimpl.
    unfold LiftSPrec in H1. psimpl.
    exists x3. destruct H3.
    repeat (easy || constructor).
    all: (subst; easy).
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
      eq_inj H8. apply StkPushFail with
        (i:=i) (v:=v).
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
        ((Waiting i (Push v) x /\
          (Offered1 i (Some v) s x \/
           exists j w, i <> j /\ Offered2 i j (Some v) w s x)) \/
         (Done i (Push v) tt x /\
          exists j, i <> j /\ Accepted i j v s x))))
      (QR:=fun r _ _ => LiftSPrec (fun s x =>
        Inv s x /\
        (match r with
         | Some None => Done i (Push v) tt x
         | _ => Waiting i (Push v) x
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
      ddestruct H. 2: destruct x1.
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
              destruct H9. easy. now apply contains_contr in H8.
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
            destruct H3. psimpl.
            constructor.
            {
              exists x1, x4.
              rewrite <- H7 at 1. easy.
            }
            {
              intros.
              rewrite <- x in H9 at 1. ddestruct H9.
              apply contains_invert in H10.
              destruct H10. easy.
              apply contains_invert in H9.
              destruct H9. easy.
              now apply contains_contr in H9.
            }
          }
          {
            left. split. easy.
            right. exists i0, (Some a).
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
            destruct H3. psimpl.
            constructor.
            {
              exists x1, x4.
              rewrite <- H7 at 1. easy.
            }
            {
              intros.
              symmetry in x2.
              dec_eq_nats i1 i0.
              {
                apply pop_offer_waiting0 with (i:=i0) in x2.
                2: apply contains_triv. easy.
                unfold not. intros. psimpl. now apply contains_contr in H12.
              }
              {
                rewrite <- x in H9 at 1. ddestruct H9.
                apply contains_invert in H10.
                destruct H10. ddestruct H9.
                apply contains_invert in H9.
                destruct H9. now ddestruct H9.
                now apply contains_contr in H9.
              }
            }
          }
          {
            left. split. easy.
            right. exists i0, None.
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
          remember (Some None). move Heqo at bottom.
          ddestruct H; simp_sets. ddestruct Heqo.
          rename x5 into j.
          set (x3' :=
            comRetPoss j
              (comInvPoss j
                (comRetPoss i
                  (comInvPoss i
                    x3
                    (Push v)
                    (AtomicStackDef vs (Some (MkStkPend i (Push v)))))
                  (Push v)
                  (AtomicStackDef (v :: vs) None)
                  tt)
                Pop
                (AtomicStackDef (v :: vs) (Some (MkStkPend j Pop))))
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
            apply pop_offer_waiting0
              with (i:=j)
              in exchs_offered0.
            2:{ rewrite insert_perm. apply contains_triv. }
            2:{
              unfold not. intros. psimpl.
              now apply contains_contr in H10.
            }
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
            } 
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
                intros. rewrite <- x in H11 at 1.
                ddestruct H11. apply contains_invert in H12.
                destruct H12. ddestruct H11.
                now apply contains_contr in H11.
              }
            }
            {
              subst x3'.
              constructor; cbn;
              now rewrite eqb_id, eqb_nid.
            }
          }
          {
            exists x3'. split. easy.
            eq_inj H11. eapply StkPushAccept
              with (i:=i) (v:=v).
            {
              constructor; cbn.
              {
                constructor; cbn.
                easy. intros. now rewrite H0.
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
                rewrite accepted0 in H at 1.
                ddestruct H; simp_sets.
                rewrite <- x in H10 at 1.
                ddestruct H10.
                now apply contains_contr in H11.
              }
            }
            { easy. }
          }
          {
            exists x3. split. easy.
            eq_inj H10. eapply StkPushFinish
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
          ddestruct H0; simp_sets.
          {
            assert (exists z, y = Some z).
            {
              clear - H. destruct y.
              repeat econstructor.
              easy.
            }
            psimpl. rename x4 into w.
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
                  rewrite <- x in H11 at 1.
                  ddestruct H11.
                  apply contains_invert in H12.
                  destruct H12. ddestruct H11.
                  now apply contains_contr in H11.
                }
              }
              { easy. }
            }
            {
              exists x3. split. easy.
              eq_inj H11. eapply StkPushConflict
                with (i:=i) (v:=v) (w:=w).
              constructor; cbn.
              {
                constructor; cbn. easy.
                intros. now rewrite H1.
              }
              {
                rewrite <- x, <- x2 at 1.
                repeat (easy || constructor).
              }
            }
          }
          {
            assert (exists z, x2 = Some z).
            {
              clear - H. destruct x2.
              repeat econstructor.
              easy.
            }
            psimpl.
            rename i0 into j.
            rename x5 into w.
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
                  rewrite <- x in H11 at 1. ddestruct H11.
                  now apply contains_contr in H12.
                }
              }
              { easy. }
            }
            {
              exists x3. split. easy.
              eq_inj H11. eapply StkPushConflict
                with (i:=i) (v:=v) (w:=w).
              constructor.
              {
                constructor; cbn. easy.
                intros. now rewrite H1.
              }
              {
                cbn. rewrite <- x4, <- x at 1.
                repeat (easy || constructor).
              }
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
                  intros.
                  rewrite <- x in H0 at 1.
                  ddestruct H0.
                  now apply contains_contr in H11.
                }
              }
              { easy. }
            }
            {
              exists x3. split. easy.
              eq_inj H0. eapply StkRevoke with
                (i:=i) (v:= Some v).
              constructor.
              {
                constructor; cbn. easy.
                intros. now rewrite H1.
              }
              {
                cbn. rewrite <- x2, <- x at 1.
                repeat (easy || constructor).
              }
            }
          }
        }
        {
          destruct H11.
          remember v0.
          move Heqo at bottom.
          ddestruct H0.
          {
            rewrite accepted0 in x2 at 1.
            ddestruct x2. simp_sets.
          }
          {
            rewrite accepted0 in x5 at 1.
            ddestruct x5. simp_sets. subst.
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
                  rewrite <- x5 in H11 at 1.
                  ddestruct H11.
                  now apply contains_contr in H12.
                }
              }
              { easy. }
            }
            {
              exists x3. split. easy.
              eq_inj H11. eapply StkPushFinish
                with (i:=i) (v:=v).
              constructor.
              {
                constructor; cbn. easy.
                intros. now rewrite H1.
              }
              {
                cbn. rewrite accepted0, <- x5 at 1.
                repeat (easy || constructor).
              }
            }
          }
          {
            subst.
            rewrite accepted0 in x2 at 1.
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
        apply SafeNoOp with
          (QS:=fun _ _ => LiftSPrec (fun s x =>
            Inv s x /\
            Waiting i (Push v) x)).
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
              destruct v0. destruct o.
              all: easy.
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
Admitted.

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