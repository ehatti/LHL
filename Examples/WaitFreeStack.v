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
  CASSpec
  MemSpec
  WaitFreeStackSpec.
Import WriteRacyMem.

From Coq Require Import
  Lists.List
  Logic.FunctionalExtensionality
  Logic.PropExtensionality.
Import ListNotations.

Require Import Coq.Program.Equality.

Unset Printing Records.

Definition E A :=
  CASSig (Addr) |+| MemSig (A * option Addr).

Definition F A := WaitFreeStackSig A.

Definition wfpush {A} (v : A) : Prog (E A) (StkRet unit) :=
  old <- call Get;
  new <- call MAlloc;
  call (MWrite new (v, old));;
  b <- call (CAS old (Some new));
  if b : bool then ret (PASS tt) else ret FAIL.

Definition wfpop {A} : Prog (E A) (StkRet (option A)) :=
  old <- call Get;
  match old : option Addr with
  | Some addr =>
      head <- call (MRead addr);
      b <- call (CAS old (snd head));
      if b : bool then ret (PASS (Some (fst head))) else ret FAIL
  | None => ret (PASS None)
  end.

Definition WFStack A : Impl (E A) (F A) :=
  fun _ m => match m with
  | WFPush v => wfpush v
  | WFPop => wfpop
  end.

Module AtomicWFStackProof.
  Import AtomicWFStack.
  Parameter T:nat.
  Parameter A:Type.

  Definition VE : Spec T (E A) := tensorSpec casSpec memSpec.
  Definition VF : Spec T (F A) := WFStackSpec.
  
  Definition Prec := SPrec VE VF.
  Definition Relt := SRelt VE VF.
  Definition Post R := R -> SRelt VE VF.

  Definition ISt := InterState (F A) VE.

  Definition casSt (s:ISt) := (LState (snd s)).
  Definition memSt (s:ISt) := (RState (snd s)).
  Notation casEv e := (inl e).
  Notation memEv e := (inr e).

  Inductive list_seg (s:option Heap) : option Addr (*head*) -> option Addr (*tail*) -> list A (*list value*) -> Prop :=
  | ListSegNil l h :
      s = Some h ->
      list_seg s l l nil
  | ListSegCons h l l1 l2 l3 v vs:
      l1 = Some l ->
      s = Some h ->
      h l = Some (v, l2) ->
      list_seg s l2 l3 vs ->
      list_seg s l1 l3 (v :: vs)
  .
  
  Definition eval_stack_und (s:ISt) (vs : list A) : Prop :=
    list_seg (eval_heap (memSt s)) (eval_cas (casSt s)) None vs.
  
  Section EvalStackLemma.
    Lemma EvalStackSameUndState: forall (s1 s2:ISt) vs,
      snd s1 = snd s2 ->
      eval_stack_und s1 vs ->
      eval_stack_und s2 vs.
    Proof.
      destruct s1, s2.
      unfold eval_stack_und.
      unfold casSt, memSt.
      simpl. intros. subst. auto.
    Qed.

    
    Lemma ListSegFrame: forall h l v hd tl vs,
      h l = None ->
      list_seg (Some h) hd tl vs ->
      list_seg (Some (heap_update l v h)) hd tl vs.
    Proof.
      intros.
      remember (Some h) as s.
      generalize dependent h.
      induction H0; intros.
      - eapply ListSegNil; eauto.
      - specialize (IHlist_seg _ H3 Heqs).
        econstructor; [|reflexivity| |apply IHlist_seg];
        eauto. unfold heap_update.
        destruct (Nat.eqb l l0) eqn:eq.
        + apply EqNat.beq_nat_true_stt in eq. congruence.
        + rewrite H0 in Heqs; inversion Heqs; subst.
          rewrite H1; auto.
    Qed.
  End EvalStackLemma.
  

  Notation IStep s i e t :=
    (InterStep (WFStack _) s (i, UEvent (Some e)) t).

  Variant WFSTran : Name T -> Relt :=
    | StkInvoke i s1 s2 ρ1 ρ2:
      InvokeAny (WFStack A) i s1 (eq ρ1) s2 (eq ρ2) ->
      WFSTran i s1 ρ1 s2 ρ2
    | StkReturn i s1 s2 ρ1 ρ2:
      ReturnAny (WFStack A) i s1 (eq ρ1) s2 (eq ρ2) ->
      WFSTran i s1 ρ1 s2 ρ2
    (* get *)
    | StkGetCall i s1 ρ s2:
      IStep s1 i (CallEv (casEv Get)) s2 ->
      WFSTran i s1 ρ s2 ρ
    | StkGetRetId i s1 ρ s2 old:
      IStep s1 i (RetEv (casEv Get) old) s2 ->
      WFSTran i s1 ρ s2 ρ
    | StkGetRetEmp i s1 ρ1 s2 ρ2:
      IStep s1 i (RetEv (casEv Get) None) s2 ->
      VisPossSteps ρ1 [(i, CallEv WFPop); (i, RetEv WFPop (PASS None))] ρ2 ->
      WFSTran i s1 ρ1 s2 ρ2
    (* alloc *)
    | StkAllocCall i s1 ρ s2:
      IStep s1 i (CallEv (memEv MAlloc)) s2 ->
      WFSTran i s1 ρ s2 ρ
    | StkAllocRet i s1 ρ s2 new:
      IStep s1 i (RetEv (memEv MAlloc) new) s2 ->
      WFSTran i s1 ρ s2 ρ
    (* write *)
    | StkWriteCall i s1 ρ s2 new data:
      IStep s1 i (CallEv (memEv (MWrite new data))) s2 ->
      WFSTran i s1 ρ s2 ρ
    | StkWriteRet i s1 ρ s2 new data:
      IStep s1 i (RetEv (memEv (MWrite new data)) tt) s2 ->
      WFSTran i s1 ρ s2 ρ
    (* read *)
    | StkReadCall i s1 ρ s2 addr:
      IStep s1 i (CallEv (memEv (MRead addr))) s2 ->
      WFSTran i s1 ρ s2 ρ
    | StkReadRet i s1 ρ s2 addr v:
      IStep s1 i (RetEv (memEv (MRead addr)) v) s2 ->
      WFSTran i s1 ρ s2 ρ
    (* cas *)
    | StkCASCall i s1 ρ s2 old new:
      IStep s1 i (CallEv (casEv (CAS old new))) s2 ->
      WFSTran i s1 ρ s2 ρ
    | StkCASRetPushPass i s1 s2 ρ1 ρ2 old new v:
      (* TODO: side condition: new points to (v, old) *)
      IStep s1 i (RetEv (casEv (CAS old new)) true) s2 ->
      VisPossSteps ρ1 [(i, CallEv (WFPush v)); (i, RetEv (WFPush v) (PASS tt))] ρ2 ->
      WFSTran i s1 ρ1 s2 ρ2
    | StkCASRetPushFail i s1 s2 ρ1 ρ2 old new v:
      IStep s1 i (RetEv (casEv (CAS old new)) false) s2 ->
      VisPossSteps ρ1 [(i, CallEv (WFPush v)); (i, RetEv (WFPush v) FAIL)] ρ2 ->
      WFSTran i s1 ρ1 s2 ρ2
    | StkCASRetPopPass i s1 s2 ρ1 ρ2 old new v:
      (* TODO: side condition: old points to (v, new) *)
      IStep s1 i (RetEv (casEv (CAS old new)) true) s2 ->
      VisPossSteps ρ1 [(i, CallEv WFPop); (i, RetEv WFPop (PASS (Some v)))] ρ2 ->
      WFSTran i s1 ρ1 s2 ρ2
    | StkCASRetPopFail i s1 s2 ρ1 ρ2 old new:
      IStep s1 i (RetEv (casEv (CAS old new)) false) s2 ->
      VisPossSteps ρ1 [(i, CallEv WFPop); (i, RetEv WFPop FAIL)] ρ2 ->
      WFSTran i s1 ρ1 s2 ρ2
  .

  Definition Guar (i : Name T) : Relt := WFSTran i.

  Definition Rely (i : Name T) : Relt :=
    SRTC (fun s x t y => exists j, i <> j /\ WFSTran j s x t y).

  Record Inv (s : ISt) (x : Poss VF) := {
    stack_consistent :
      eval_stack_und s (eval_stack (PState x))
  }.

  Record Ready (i : Name T) (s : ISt) (x : Poss VF) := {
    ready_inv : Inv s x;
  }.

  Record ReadyDone (i : Name T) {R} (m : F A R) (r : R) (s : ISt) (x : Poss VF) := {
    done_ready : Ready i s x;
    ready_done : Done i m r x;
  }.

  Section SideConditions.
    Lemma RelyReflexive:
      forall (i : Name T) (s : @InterState T (E A) (F A) VE) (ρ : @PossSet T (F A) VF), @LiftSRelt T (E A) (F A) VE VF (Rely i) s ρ s ρ.
    Proof.
      intros.
      eexists. subst.
      split. easy.
      constructor.
    Qed.

    Lemma RelyClosed:
      forall i : Name T,
      @sub (@Logic.Relt T (E A) (F A) VE VF) (@subRelt T (E A) (F A) VE VF)
        (@ReltCompose T (E A) (F A) VE VF (@LiftSRelt T (E A) (F A) VE VF (Rely i))
          (@LiftSRelt T (E A) (F A) VE VF (Rely i))) (@LiftSRelt T (E A) (F A) VE VF (Rely i)).
    Proof.
      unfold sub, subRelt, LiftSRelt.
      intros. psimpl.
      specialize (H x eq_refl). psimpl.
      specialize (H1 x2 eq_refl). psimpl.
      eexists. split. easy.
      eapply srtcTrans.
      psplit. exact H0. easy.
    Qed.

    Lemma GuarInRely:
      forall (i j : Name T) (_ : not (@eq (Name T) i j)),
      @sub (@Logic.Relt T (E A) (F A) VE VF) (@subRelt T (E A) (F A) VE VF)
        (@LiftSRelt T (E A) (F A) VE VF (Guar i)) (@LiftSRelt T (E A) (F A) VE VF (Rely j)).
    Proof.
      unfold sub, subRelt, LiftSRelt.
      intros. psimpl.
      specialize (H0 x eq_refl). psimpl.
      eexists. split. easy.
      econstructor.
      2: constructor.
      now exists i.
    Qed.

    Lemma Invoke_pres_single {R} :
      forall (m : F A R) i s ρ t σs,
      TInvoke (VE:= VE) (VF:= VF) (WFStack A) i R m s (eq ρ) t σs ->
      exists σ, σs = eq σ.
    Proof.
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

    Lemma InvokeInRely:
      forall (i j : Name T) (_ : not (@eq (Name T) i j)),
      @sub (@Logic.Relt T (E A) (F A) VE VF) (@subRelt T (E A) (F A) VE VF)
        (@InvokeAny T (E A) (F A) VE VF (WFStack A) i)
        (@LiftSRelt T (E A) (F A) VE VF (Rely j)).
    Proof.
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
    Qed.

    Lemma Return_pres_single {R} :
      forall (m : F A R) v i s ρ t σs,
      TReturn (VE:= VE) (VF:= VF) (WFStack A) i m v s (eq ρ) t σs ->
      exists σ, σs = eq σ.
    Proof.
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

    Lemma ReturnInRely:
      forall (i j : Name T) (_ : not (@eq (Name T) i j)),
      @sub (@Logic.Relt T (E A) (F A) VE VF) (@subRelt T (E A) (F A) VE VF)
        (@ReturnAny T (E A) (F A) VE VF (WFStack A) i)
        (@LiftSRelt T (E A) (F A) VE VF (Rely j)).
    Proof.
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
    Qed.

    Lemma InitialReady:
      forall (i : Name T) (A0 : Type) (_ : F A A0),
      @LiftSPrec T (E A) (F A) VE VF (Ready i)
        (@pair (ThreadsSt T (E A) (F A)) (@State T (E A) VE) (@allIdle T (E A) (F A))
          (@Init T (E A) VE)) (@eq (@Poss T (F A) VF) (@initPoss T (F A) VF)).
    Proof.
      unfold LiftSPrec.
      intros. eexists.
      split. easy.
      constructor.
      {
        constructor. simpl eval_stack.
        unfold eval_stack_und.
        simpl. eapply ListSegNil. eauto.
      }
    Qed.
    
    Ltac begin_stable :=
      unfold Stable, stablePost, stableRelt, stablePrec, sub, subRelt, subPrec;
      unfold SStable, stableSRelt, stableSPrec, ssub, subSRelt, subSPrec;
      unfold ReltToPrec, LiftSPrec, LiftSRelt;
      intros; psimpl.

    Lemma sing_elem {A} {P : A -> Prop} :
      forall x : A,
      eq x = P ->
      P x.
    Proof.
    intros. now rewrite <- H.
    Qed.

    Ltac forward_istep_cas stack_consistent0 :=
    match goal with
      | H : IStep ?s1 _ _ ?s2 |- _ =>
        destruct H as [_ [H ?]]; psimpl;
        unfold eval_stack_und, casSt, memSt in *;
        inversion H; subst; clear H;
        match goal with
        | Hs1 : _ = LState (snd s1),
          Hs2R : _ = RState (snd s2),
          Hs2L : _ = LState (snd s2) |- _ =>
          setoid_rewrite <- Hs2R;
          setoid_rewrite <- Hs2L;
          setoid_rewrite <- Hs1 in stack_consistent0
        end
      end.

    Ltac forward_pstep p1 p2 :=
      match goal with
      | H : VisPossStep p1 _ p2 |- _ =>
        inversion H; subst; clear H;
        match goal with
        | H1 : Step _ (PState p1) _ (PState p2) |- _ =>
          inversion H1; subst; clear H1
        end
      end.
    
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
        | [ H : existT ?F ?A ?x = existT ?F ?A ?y |- _ ] =>
          ddestruct H
        end
      ).

    Lemma InvStable: forall i (s1 s2:InterState (F A) VE) p1 p2,
      Ready i s1 p1 ->
      (exists j, i <> j /\ WFSTran j s1 p1 s2 p2) ->
      Ready i s2 p2.
    Proof.
      intros.
      destruct H0 as [j [? ?]].
      constructor; constructor.
      inversion_clear H.
      inversion_clear ready_inv0.
      inversion H1; subst; clear H1;
      (* irrelevant cas events *)
      try (forward_istep_cas stack_consistent0; now auto).
      (* invoke any *)
      {
        unfold InvokeAny, TInvoke, TIdle in H.
        psimpl. apply sing_elem in H3. psimpl.
        rewrite H5.
        eapply EvalStackSameUndState; eauto.
      }
      (* return any *)
      {
        unfold ReturnAny, TReturn, mapRetPoss in H.
        psimpl. apply sing_elem in H3. psimpl.
        rewrite H10.
        eapply EvalStackSameUndState; eauto.
      }
      (* fail pop *)
      {
        forward_istep_cas stack_consistent0.
        inversion H2; subst; clear H2.
        inversion H16; subst; clear H16.
        inversion H19; subst; clear H19.
        forward_pstep p1 y.
        setoid_rewrite <- H2 in stack_consistent0.
        forward_pstep y p2;
        simp_eqs; simpl in *; auto.
      }
      (* malloc call *)
      {
        destruct H as [_ [H ?]]; psimpl;
        unfold eval_stack_und, casSt, memSt in *;
        inversion H; subst; clear H;
        match goal with
        | Hs1 : _ = RState (snd s1) |- _ =>
          setoid_rewrite <- Hs1 in stack_consistent0
        end; simpl in *;
        [|inversion stack_consistent0; congruence].
        setoid_rewrite <- H4.
        setoid_rewrite <- H8.
        auto.
      }
      (* malloc ret *)
      {
        destruct H as [_ [H ?]]; psimpl;
        unfold eval_stack_und, casSt, memSt in *;
        inversion H; subst; clear H;
        match goal with
        | Hs1 : _ = RState (snd s1) |- _ =>
          setoid_rewrite <- Hs1 in stack_consistent0
        end; simpl in *;
        [|inversion stack_consistent0; congruence
         |inversion stack_consistent0; congruence].
        setoid_rewrite <- H4.
        setoid_rewrite <- H9.
        simpl in *.
        apply ListSegFrame; auto.
      }
      {
        destruct H as [_ [H ?]]; psimpl;
        unfold eval_stack_und, casSt, memSt in *;
        inversion H; subst; clear H.
        - (*provable*)
          admit.
        - (*unprovable*)
          (* different threads should not be able to write to the same location *)
          (* TODO: add extra field in mem state to record TID that allocates each location, and ensure in the rely that each thread only write to the one it allocates *)
          admit.
        - (*provable*)
          admit.
      }

        2:{
          
          setoid_rewrite <- H6 in stack_consistent0.
        match goal with
        | H : IStep ?s1 _ _ ?s2 |- _ =>
          destruct H as [_ [H ?]]; psimpl;
          unfold eval_stack_und, casSt, memSt in *;
          inversion H; subst; clear H
        end.
          match goal with
          | Hs1 : _ = LState (snd s1),
            Hs2R : _ = RState (snd s2),
            Hs2L : _ = LState (snd s2) |- _ =>
            setoid_rewrite <- Hs2R;
            setoid_rewrite <- Hs2L;
            setoid_rewrite <- Hs1 in stack_consistent0
          end
        end.
      }


    Lemma InitialStable:
      forall (i : Name T) (A0 : Type) (_ : F A A0),
      @Stable T (E A) (F A) VE VF (@Logic.Prec T (E A) (F A) VE VF)
        (@stablePrec T (E A) (F A) VE VF) (@LiftSRelt T (E A) (F A) VE VF (Rely i))
        (@LiftSPrec T (E A) (F A) VE VF (Ready i)).
    Proof.
      begin_stable.
      specialize (H0 x1 eq_refl). psimpl.
      eexists. split. easy.
      induction H0; auto; clear H0.
      apply IHSRTC; clear IHSRTC.
      clear - H H1.
      constructor; constructor.
      inversion_clear H1.
      inversion_clear ready_inv0.
      

      destruct H as [j [? ?]].

          (* {
            
          }
          {
            
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
          } *)


    (* Lemma RelyReflective :
    forall (i : Name T) (s : InterState (F A) VE) (ρ : PossSet VF), Rely i s ρ s ρ.
    2/10
    forall i : Name T, Rely i ->> Rely i ==> Rely i
    3/10
    forall i j : Name T, i <> j -> Guar i ==> Rely j
    4/10
    forall i j : Name T, i <> j -> InvokeAny (WFStack A) i ==> Rely j
    5/10
    forall i j : Name T, i <> j -> ReturnAny (WFStack A) i ==> Rely j
    6/10
    forall (i : Name T) (A0 : Type), F A A0 -> Ready i (allIdle, Init VE) (eq initPoss)
    7/10
    forall (i : Name T) (A0 : Type), F A A0 -> Stable (Rely i) (Ready i) *)

  End SideConditions.
  

  Theorem WFStackCorrect:
    VerifyImpl VE VF
    (fun i => LiftSRelt (Rely i))
    (fun i => LiftSRelt (Guar i))
    (fun i _ _ => LiftSPrec (Ready i))
    (WFStack A)
    (fun i _ m r _ _ => LiftSPrec (ReadyDone i m r))
    (TReturn (WFStack A)).
  Proof.
    constructor.
    7:{
    Set Printing All.
  Qed.
End AtomicWFStackProof.





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


Theorem EBStackCorrect T A :
  VerifyImpl (VE T A) (VF T A)
  (fun i => LiftSRelt (Rely i))
  (fun i => LiftSRelt (Guar i))
  (fun i _ _ => LiftSPrec (Ready i))
  (EBStack A)
  (fun i _ m r _ _ => LiftSPrec (ReadyDone i m r))
  (TReturn (EBStack A)).
Proof.
Qed.

Require Import LHL.Core.Linearizability.

Theorem EBStackLin T A :
  Lin (overObj (VE T A :> EBStack A)) (VF T A).
eapply soundness.
apply EBStackCorrect.
Qed.