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
  Util
  Heap.

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

Axiom StkRet_inj : forall A B, StkRet A = StkRet B -> A = B.

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

  Section EvalStack.
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
    
    Lemma ListSegSomeHeap: forall h l1 l2 vs,
      list_seg h l1 l2 vs -> h <> None.
    Proof.
      destruct 1; congruence.
    Qed.

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

    Lemma ListSegUnique: forall h hd tl vs1,
      list_seg h hd tl vs1 ->
      forall vs2, list_seg h hd tl vs2 ->
      tl = None ->
      vs1 = vs2.
    Proof.
      induction 1; intros; subst.
      - inversion_clear H0; subst; auto.
        congruence.
      - inversion H3; subst.
        inversion H0; subst.
        inversion H; subst.
        rewrite H1 in H4.
        inversion H4; subst.
        apply IHlist_seg in H5; subst; auto.
    Qed.
  End EvalStack.

  Section OffChain.
    Inductive off_chain_aux (s:option Heap) (l:Addr) : option Addr (*head*) -> option Addr (*tail*) -> Prop :=
    | OffChainNil l1:
      off_chain_aux s l l1 l1
    | OffChainCons h l' l1 l2 l3 (v:A):
        s = Some h ->
        l1 = Some l' ->
        h l' = Some (v, l2) ->
        l <> l' ->
        off_chain_aux s l l2 l3 ->
        off_chain_aux s l l1 l3
    .

    Definition off_chain (s:ISt) (l:Addr) := off_chain_aux (eval_heap (memSt s)) l (eval_cas (casSt s)) None.

    Lemma OffChainFrame: forall h hd tl vs new v,
      list_seg (Some h) hd tl vs ->
      h new = None ->
      off_chain_aux (Some (heap_update new v h)) new hd tl.
    Proof.
      intros.
      remember (Some h) as sh.
      generalize dependent h.
      induction H; intros; subst; try constructor.
      inversion Heqsh; subst; clear Heqsh.
      assert (new <> l).
      {
        unfold not; intros; subst.
        congruence.
      }
      eapply OffChainCons with (v:=v0); eauto.
      rewrite HeapUpdateOther; auto.
    Qed.
      
    Lemma ListSegUpdateOffChain: forall h l1 vs new data,
      list_seg (Some h) l1 None vs ->
      off_chain_aux (Some h) new l1 None ->
      list_seg (Some (heap_update new data h)) l1 None vs.
    Proof.
      intros.
      remember None as l2.
      revert H Heql2.
      induction 1; intros; subst.
      - eapply ListSegNil with (h:=(heap_update new data h)); auto.
      - inversion H0; subst.
        inversion H; inversion H1; subst.
        inversion H4; subst.
        rewrite H2 in H5. inversion H5; subst.
        eapply ListSegCons with (l2:=l0); eauto.
        rewrite HeapUpdateOther; auto.
    Qed.
  End OffChain.
  

  Definition location_allocated (s:ISt) (l:Addr) : Prop :=
    exists heap, eval_heap (memSt s) = Some heap /\ heap l <> None.

  Definition location_owned (i:Name T) (s:ISt) (l:Addr) : Prop :=
    location_allocated s l /\
    exists loc, eval_loc (memSt s) = Some loc /\ loc l = Some i.
  
  
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
    | StkWriteCall i s1 ρ s2 new data
      (H_owned: location_owned i s1 new):
      IStep s1 i (CallEv (memEv (MWrite new data))) s2 ->
      WFSTran i s1 ρ s2 ρ
    | StkWriteRet i s1 ρ s2 new data
      (H_alloc: location_allocated s1 new)
      (H_off_chain: off_chain s1 new):
      IStep s1 i (RetEv (memEv (MWrite new data)) tt) s2 ->
      WFSTran i s1 ρ s2 ρ
    (* read *)
    | StkReadCall i s1 ρ s2 addr:
      IStep s1 i (CallEv (memEv (MRead addr))) s2 ->
      WFSTran i s1 ρ s2 ρ
    | StkReadRet i s1 ρ s2 addr v
      (H_alloc: location_allocated s1 addr):
      IStep s1 i (RetEv (memEv (MRead addr)) v) s2 ->
      WFSTran i s1 ρ s2 ρ
    (* cas *)
    | StkCASCall i s1 ρ s2 old new:
      IStep s1 i (CallEv (casEv (CAS old new))) s2 ->
      WFSTran i s1 ρ s2 ρ
    | StkCASRetPushPass i s1 s2 ρ1 ρ2 old new v h
      (* new points to (v, old) *)
      (H_heap: eval_heap (memSt s1) = Some h)
      (H_new: h new = Some (v, old)):
      IStep s1 i (RetEv (casEv (CAS old (Some new))) true) s2 ->
      VisPossSteps ρ1 [(i, CallEv (WFPush v)); (i, RetEv (WFPush v) (PASS tt))] ρ2 ->
      WFSTran i s1 ρ1 s2 ρ2
    | StkCASRetPushFail i s1 s2 ρ1 ρ2 old new v:
      IStep s1 i (RetEv (casEv (CAS old new)) false) s2 ->
      VisPossSteps ρ1 [(i, CallEv (WFPush v)); (i, RetEv (WFPush v) FAIL)] ρ2 ->
      WFSTran i s1 ρ1 s2 ρ2
    | StkCASRetPopPass i s1 s2 ρ1 ρ2 old new v h
      (* side condition: old points to (v, new) *)
      (H_heap: eval_heap (memSt s1) = Some h)
      (H_new: h old = Some (v, new)):
      IStep s1 i (RetEv (casEv (CAS (Some old) new)) true) s2 ->
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

  Definition wfs_idle (x : Poss VF) : Prop := exists vs, PState x = WFSsIdle vs.

  Record Inv (s : ISt) (x : Poss VF) := {
    (* overlay stack matches underlay stack *)
    same_stack:
      eval_stack_und s (eval_stack (PState x));
    always_atomic:
      wfs_idle x;
    (* only write to location allocated by self *)
    write_excl:
      forall j h loc l v, MsWritePend j h loc l v = memSt s ->
        loc l = Some j
    (* loc_heap_match:
      exists heap loc,
        eval_heap (memSt s) = Some heap /\
        eval_loc (memSt s) = Some loc /\
        forall l, heap l <> None <-> loc l <> None *)
  }.

  Record Ready (i : Name T) (s : ISt) (x : Poss VF) := {
    ready_inv : Inv s x;
  }.

  Record ReadyWaiting (i : Name T) {R} (m : F A R)
  (s : InterState (F A) VE) (x : Poss VF)
  := {
    wait_ready : Ready i s x;
    ready_wait : Waiting i m x
  }.

  Record ReadyDone (i : Name T) {R} (m : F A R) (r : R) (s : ISt) (x : Poss VF) := {
    done_ready : Ready i s x;
    ready_done : Done i m r x;
  }.

  Ltac begin_stable :=
    unfold Stable, stablePost, stableRelt, stablePrec, sub, subRelt, subPrec;
    unfold SStable, stableSRelt, stableSPrec, ssub, subSRelt, subSPrec;
    unfold ReltToPrec, LiftSPrec, LiftSRelt;
    intros; psimpl.
    

  Ltac subst_ist s :=
    unfold eval_stack_und, casSt, memSt in *;
    try match goal with
    | HRewrite : _ = LState (snd s) |- _ =>
      (repeat match goal with
      | H : context[LState (snd s)] |- _ => 
        lazymatch H with
        | HRewrite => fail
        | _ => setoid_rewrite <- HRewrite in H
        end
      end;
      try match goal with
      | |- context[LState (snd s)] =>
        setoid_rewrite <- HRewrite
      end)
    end;
    try match goal with
    | HRewrite : LState (snd s) = _ |- _ =>
      (* let x:= constr:(LState (snd s)) in  *)
      (repeat match goal with
      | H : context[LState (snd s)] |- _ => 
        lazymatch H with
        | HRewrite => fail
        | _ => setoid_rewrite HRewrite in H
        end
      end;
      try match goal with
      | |- context[LState (snd s)] =>
        setoid_rewrite HRewrite
      end)
    end;
    try match goal with
    | HRewrite : _ = RState (snd s) |- _ =>
      (repeat match goal with
      | H : context[RState (snd s)] |- _ => 
        lazymatch H with
        | HRewrite => fail
        | _ => setoid_rewrite <- HRewrite in H
        end
      end;
      try match goal with
      | |- context[RState (snd s)] =>
        setoid_rewrite <- HRewrite
      end)
    end;
    try match goal with
    | HRewrite : RState (snd s) = _ |- _ =>
      (repeat match goal with
      | H : context[RState (snd s)] |- _ => 
        lazymatch H with
        | HRewrite => fail
        | _ => setoid_rewrite HRewrite in H
        end
      end;
      try match goal with
      | |- context[RState (snd s)] =>
        setoid_rewrite HRewrite
      end)
    end.

    Ltac forward_istep_cas_aux s1 s2 :=
      match goal with
      | same_stack0 : eval_stack_und _ _ |- _ =>
        subst_ist s1; subst_ist s2;
        simpl in *
      end.

    Ltac forward_istep_cas :=
      match goal with
        | H : IStep ?s1 _ _ ?s2 |- _ =>
          destruct H as [_ [H ?]]; psimpl;
          inversion H; subst; clear H;
          forward_istep_cas_aux s1 s2
      end.

    (* Ltac mem_rewrite s1 s2 :=
      unfold eval_stack_und, casSt, memSt in *;
      subst_ist s1 s2. *)
      (* try match goal with
        | Hs1 : _ = LState (snd s1) |- _ =>
          setoid_rewrite <- Hs1 in same_stack0
        | Hs1 : LState (snd s1) = _ |- _ =>
          setoid_rewrite Hs1 in same_stack0 end;
        try match goal with
        | Hs1 : _ = RState (snd s1) |- _ =>
          setoid_rewrite <- Hs1 in same_stack0
        | Hs1 : RState (snd s1) = _ |- _ =>
          setoid_rewrite Hs1 in same_stack0 end;
        try match goal with
        | Hs2R : _ = RState (snd s2) |- _ =>
          setoid_rewrite <- Hs2R
        | Hs2R : RState (snd s2) = _ |- _ =>
          setoid_rewrite Hs2R end;
        try match goal with
        | Hs2L : _ = LState (snd s2) |- _ =>
          setoid_rewrite <- Hs2L 
        | Hs2L : LState (snd s2) = _ |- _ =>
          setoid_rewrite Hs2L
          end. *)

    Ltac forward_istep_mem_aux s1 s2 :=
      match goal with
      | same_stack0 : eval_stack_und _ _ |- _ =>
        subst_ist s1; subst_ist s2;
        simpl in *; try (inversion same_stack0; congruence)
      end.
  
    Ltac forward_istep_mem :=
      match goal with
      | H: IStep ?s1 _ _ ?s2 |- _ =>
        destruct H as [_ [H ?]]; psimpl;
        inversion H; subst; clear H;
        forward_istep_mem_aux s1 s2
      end.
  
      Ltac unfold_possteps :=
        repeat match goal with
        | H:VisPossSteps _ _ _ |- _ =>
          inversion H; subst; clear H
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
  
    Ltac drecs :=
      do 10 try (
        match goal with
        | [ H : Inv ?s ?x |- _ ] =>
          destruct H
        | [ H : Ready ?i ?s ?x |- _ ] =>
          destruct H
        end
      ).
  

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
      constructor; constructor.
      {
        unfold eval_stack_und.
        simpl. eapply ListSegNil. eauto.
      }
      {
        unfold wfs_idle. simpl; eauto.
      }
      {
        unfold memSt; simpl.
        inversion 1.
      }
    Qed.

    Lemma sing_elem {A} {P : A -> Prop} :
      forall x : A,
      eq x = P ->
      P x.
    Proof.
    intros. now rewrite <- H.
    Qed.

    Lemma InvStable: forall i (s1 s2:InterState (F A) VE) p1 p2,
      Inv s1 p1 ->
      WFSTran i s1 p1 s2 p2 ->
      Inv s2 p2.
    Proof.
      intros.
      (* destruct H0 as [j [? ?]]. *)
      constructor.
      {
        inversion_clear H.
        (* inversion_clear ready_inv0. *)
        inversion H0; subst; clear H0;
        (* irrelevant cas events *)
        try (forward_istep_cas; now auto);
        try (forward_istep_mem; now auto).
        (* invoke any *)
        {
          unfold InvokeAny, TInvoke, TIdle in H.
          psimpl. apply sing_elem in H2. psimpl.
          rewrite H4.
          eapply EvalStackSameUndState; eauto.
        }
        (* return any *)
        {
          unfold ReturnAny, TReturn, mapRetPoss in H.
          psimpl. apply sing_elem in H2. psimpl.
          rewrite H9.
          eapply EvalStackSameUndState; eauto.
        }
        (* fail pop *)
        {
          forward_istep_cas.
          unfold_possteps.
          forward_pstep p1 y.
          setoid_rewrite <- H1 in same_stack0.
          forward_pstep y p2;
          simp_eqs; simpl in *; auto.
        }
        (* malloc ret *)
        {
          forward_istep_mem.
          apply ListSegFrame; auto.
        }
        (* write call *)
        {
          (* use write_excl, prevent concurrent writes *)
          destruct H_owned as [_ [? [? ?]]].
          forward_istep_mem.
          inversion H0; subst x; clear H0.
          specialize (write_excl0 _ _ _ _ _ eq_refl).
          congruence.
        }
        (* write ret *)
        {
          forward_istep_mem.
          {
            destruct H_alloc as [? [? ?]].
            setoid_rewrite <- H4 in H.
            inversion H; subst x. congruence.
          }
          {
            unfold off_chain in H_off_chain.
            subst_ist s1. simpl in *.
            apply ListSegUpdateOffChain; auto.
          }
        }
        (* read ret *)
        {
          forward_istep_mem.
          destruct H_alloc as [? [? ?]].
          setoid_rewrite <- H4 in H.
          simpl in H. congruence.
        }
        (* cas push succ *)
        {
          unfold_possteps.
          forward_pstep p1 y.
          setoid_rewrite <- H1 in same_stack0.
          ddestruct H2. ddestruct H13.
          forward_pstep y p2; simpl in *; simp_eqs.
          - apply StkRet_inj in H13; subst. ddestruct H5.
          (* this is the right branch *)
          - forward_istep_cas.
            + econstructor; eauto.
            + apply pair_equal_spec in H17 as [_ H].
              ddestruct H.
        }
        (* cas push fail *)
        {
          unfold_possteps.
          forward_pstep p1 y.
          setoid_rewrite <- H1 in same_stack0.
          ddestruct H2. ddestruct H13.
          forward_pstep y p2; simpl in *; simp_eqs.
          forward_istep_cas; auto.
          apply pair_equal_spec in H24 as [_ H].
          ddestruct H.
        }
        (* cas pop succ *)
        {
          unfold_possteps.
          forward_pstep p1 y.
          setoid_rewrite <- H1 in same_stack0.
          ddestruct H2. ddestruct H13.
          forward_pstep y p2; simpl in *; simp_eqs.
          - apply StkRet_inj in H13; subst. ddestruct H5.
          - forward_istep_cas.
            + inversion same_stack0; subst.
              inversion H13; subst.
              setoid_rewrite H_heap in H14.
              inversion H14; subst.
              rewrite H_new in H18.
              inversion H18; subst; auto.
            + apply pair_equal_spec in H13 as [_ H].
              ddestruct H.
        }
        (* cas pop fail *)
        {
          unfold_possteps.
          forward_pstep p1 y.
          setoid_rewrite <- H1 in same_stack0.
          ddestruct H2. ddestruct H13.
          forward_pstep y p2; simpl in *; simp_eqs.
          forward_istep_cas; auto.
          apply pair_equal_spec in H24 as [_ H].
          ddestruct H.
        }
      }
      {
        inversion_clear H.
        inversion H0; subst; clear H0.
        admit.
      }
      {
        inversion_clear H.
        inversion H0; subst; clear H0;
        (* irrelevant cas events *)
        try (forward_istep_cas; now auto);
        try (forward_istep_mem; now auto).
        (* invoke any *)
        {
          unfold InvokeAny, TInvoke, TIdle in H.
          psimpl. psimpl. unfold memSt in *.
          setoid_rewrite H1 in write_excl0. auto.
        }
        (* return any *)
        {
          unfold ReturnAny, TReturn, mapRetPoss in H.
          psimpl. unfold memSt in *.
          setoid_rewrite H1 in write_excl0. auto.
        }
        {
          forward_istep_mem.
          inversion_clear 1.
          destruct H_owned as [_ [? [? ?]]].
          setoid_rewrite <- H5 in H.
          inversion_clear H. auto.
        }
      }
    Admitted.

    Lemma ReadyStable:
      forall (i : Name T) (A0 : Type) (_ : F A A0),
      @Stable T (E A) (F A) VE VF (@Logic.Prec T (E A) (F A) VE VF)
        (@stablePrec T (E A) (F A) VE VF) (@LiftSRelt T (E A) (F A) VE VF (Rely i))
        (@LiftSPrec T (E A) (F A) VE VF (Ready i)).
    Proof.
      begin_stable.
      specialize (H0 x1 eq_refl). psimpl.
      eexists. split. easy.
      induction H0; auto; clear H0.
      destruct H as [? [_ ?]].
      apply IHSRTC; clear IHSRTC.
      inversion_clear H1.
      constructor.
      eapply InvStable; eauto.
    Qed.
  End SideConditions.
  
    Lemma SRTC_stable {P : Prec} {R : Relt} :
      (forall s x t y,
        P s x ->
        R s x t y ->
        P t y) ->
      forall s x t y,
        P s x ->
        SRTC R s x t y ->
        P t y.
    Proof.
      intros. induction H1. easy.
      eapply IHSRTC, H. exact H0. easy.
    Qed.

    Lemma WaitingStable (i j : Name T) {R} (m : F A R) (s t : InterState (F A) VE) (x y : Poss VF) :
      i <> j ->
      Waiting i m x ->
      WFSTran j s x t y ->
      Waiting i m y.
    Proof.
      intros.
      inversion H1; subst; clear H1;
      auto; inversion_clear H0;
      try (unfold_possteps;
          repeat match goal with
          | Hdf: differ_pointwise _ _ _ |- _ =>
            specialize (Hdf _ H)
          end; now simp_eqs).
      {
        unfold InvokeAny, TInvoke, TIdle in *.
        psimpl.
        apply sing_elem in H3. psimpl.
        repeat match goal with
        | Hdf: differ_pointwise _ _ _ |- _ =>
          specialize (Hdf _ H) end;
        constructor;
        simp_eqs;
        match goal with
        | H: ?x = _ |- ?x = _ =>
          rewrite H
        end; auto.
      }
      {
        unfold ReturnAny, TReturn, Returned, mapRetPoss in *.
        psimpl.
        apply sing_elem in H3. psimpl.
        repeat match goal with
        | Hdf: differ_pointwise _ _ _ |- _ =>
          specialize (Hdf _ H) end;
        constructor;
        simp_eqs;
        match goal with
        | H: ?x = _ |- ?x = _ =>
          rewrite H
        end; auto.
      }
    Qed.

    Lemma ready_waiting_stable (i : Name T) {R} (m : F A R) :
      SStable (Rely i) (ReadyWaiting i m).
    Proof.
      begin_stable.
      eapply SRTC_stable.
      2: exact H. 2: exact H0.
      clear. intros.
      destruct H.
      constructor;
      destruct H0 as [j [? ?]].
      {
        inversion_clear wait_ready0.
        constructor. eapply InvStable; eauto.
      }
      {
        eapply WaitingStable; eauto.
      }
    Qed.

    Lemma push_old_listseg_stable (i : Name T) v old:
      SStable (Rely i) (fun s x =>
        ReadyWaiting i (WFPush v) s x /\
        exists vs, list_seg (eval_heap (memSt s)) old None vs
      ).
    Proof.
      begin_stable.
      remember (fun s (ρ:Poss VF) => ReadyWaiting i (WFPush v) s ρ /\
      (exists vs : list A, list_seg (eval_heap (memSt s)) old None vs)) as P.
      replace (ReadyWaiting i (WFPush v) s ρ /\
      (exists vs : list A, list_seg (eval_heap (memSt s)) old None vs))
      with (P s ρ); [|subst; auto].
      eapply SRTC_stable;
      subst; eauto.
      clear. intros; simpl in *.
      destruct H0 as [j [? ?]].
      destruct H.
      split.
      {
        eapply ready_waiting_stable.
        psplit; eauto.
        econstructor; eauto.
        constructor.
      }
      
      inversion H1; subst; clear H1;
      try (match goal with
      | H : IStep _ ?s1 _ ?s2 |- _ =>
        inversion H; subst; clear H;
        try match goal with
        | H1 : StateStep _ _ _ |- _ =>
          inversion H1; psimpl
        end;
        subst_ist s1; subst_ist s2
      end; eauto).
      {
        unfold InvokeAny, TInvoke, TIdle in *. psimpl.
        apply sing_elem in H5. psimpl.
        unfold memSt in *.
        setoid_rewrite <- H4. eauto.
      }
      {
        unfold ReturnAny, TReturn, Returned, mapRetPoss in *. psimpl.
        apply sing_elem in H5. psimpl.
        unfold memSt in *.
        setoid_rewrite <- H4. eauto.
      }
      {
        inversion H3; subst; clear H3;
        subst_ist s; subst_ist t; eauto.
      }
      {
        inversion H3; subst; clear H3;
        subst_ist s; subst_ist t;
        simpl in *; eauto.
        eapply ListSegFrame in H2; eauto.
      }
      {
        destruct H_owned as [[? ?] [? [? ?]]].
        inversion H3; subst; clear H3;
        subst_ist s; subst_ist t;
        simpl in *; eauto.
        destruct H as [[[?]] _].
        eapply write_excl0 in H12.
        inversion H10; subst.
        congruence.
      }
      {
        destruct H_alloc as [? [? ?]].
        inversion H3; subst; clear H3;
        subst_ist s; subst_ist t;
        simpl in *; eauto; try congruence.
        inversion H9; subst x0.

        destruct H as [[[?]] _].
        eapply write_excl0 in H1.
        eapply ListSegUpdateOffChain in H2; eauto.
        
        congruence.
      }
      3:{
        inversion H2.
        2:{}
        (* inversion_clear ready_inv0. *)
        (* inversion H2; subst; clear H2; *)
        (* irrelevant cas events *)
        try (forward_istep_cas; now eauto);
        try (forward_istep_mem; now eauto).

        

        inversion H3
        .

        destruct H2 as [_ [H2 ?]]; psimpl;
        inversion H2; subst; clear H2;
        forward_istep_mem_aux s1 s2.
        forward_istep_mem.
      }
    Admitted.

    Lemma stepCall {E E' A B} {m : E' A} {k : A -> Prog E B} `{SigCoercion E' E} : (x <- call m; k x) = Bind (coerceOp _ m) k.
    Proof.
      rewrite frobProgId at 1. cbn.
      f_equal. extensionality x.
      rewrite frobProgId at 1. simpl.
      apply foldProg.
    Qed.

    Ltac begin_commit :=
      unfold Commit, LiftSPrec; intros.

    Lemma eq_inj {A} :
      forall x y : A,
      eq x = eq y ->
      x = y.
    intros. now rewrite H.
    Qed.

  Lemma PushCorrect: forall (i:Name T) (v:A),
    @VerifyProg T (E A) (F A) VE VF (StkRet unit) i
    (@LiftSRelt T (E A) (F A) VE VF (Rely i))
    (@LiftSRelt T (E A) (F A) VE VF (Guar i))
    (@ReltCompose T (E A) (F A) VE VF
      (@prComp T (E A) (F A) VE VF
        (@LiftSPrec T (E A) (F A) VE VF (Ready i))
        (@TInvoke T (E A) (F A) VE VF (WFStack A) i  (StkRet unit) (@WFPush A v)))
      (@LiftSRelt T (E A) (F A) VE VF (Rely i)))
    (WFStack A (StkRet unit) (@WFPush A v))
    (fun r _ _ => LiftSPrec (ReadyDone i (WFPush v) r)).
  Proof.
    intros.

    eapply weakenPrec with (P:=fun _ _ => LiftSPrec (ReadyWaiting i (WFPush v))).
    2:{
      unfold sub, subRelt, LiftSPrec, LiftSRelt.
      intros. psimpl.
      assert (x0 = eq (invPoss i x1 (WFPush v))).
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
      assert (ReadyWaiting i (WFPush v) x (invPoss i x1 (WFPush v))).
      {
        assert (snd s = snd x).
        { unfold TInvoke in H1. now psimpl. }
        drecs.
        constructor.
        {
          constructor.
          constructor; cbn;
          unfold wfs_idle, eval_stack_und, memSt, casSt in *;
          auto; try now setoid_rewrite <- H.
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
      P ==> (fun _ _ => LiftSPrec (ReadyWaiting i (WFPush v))) ->
        VerifyProg i (LiftSRelt (Rely i)) (LiftSRelt (Guar i))
          P
          (wfpush v)
          (fun r _ _ => LiftSPrec (ReadyDone i (WFPush v) r))
    ).
    { intros. now apply H. }
    cofix rec. intros P impH. unfold wfpush.

    (* step get call *)
    rewrite stepCall.
    eapply SafeBind with
      (QI:=fun _ _ => LiftSPrec (ReadyWaiting i (WFPush v)))
      (QR:=fun r _ _ => LiftSPrec (fun s x =>
          ReadyWaiting i (WFPush v) s x /\
          exists vs, list_seg (eval_heap (memSt s)) r None vs
        )).
    (* stable QI *)
    {
      begin_stable.
      specialize (H0 x1 eq_refl) as [? [? ?]].
      eexists; split; eauto.
      apply ready_waiting_stable.
      psplit; eauto.
    }
    (* stable QR *)
    {
      begin_stable.
      specialize (H0 x1 eq_refl) as [? [? ?]].
      eexists; split; eauto.
      split.
      - apply ready_waiting_stable.
        psplit; eauto.
      - eapply push_old_listseg_stable.
        psplit; eauto.
    }
    (* commit *)
    {
      clear rec. begin_commit.
      psimpl. apply impH in H.
      clear impH. psimpl.
      unfold LiftSPrec in H. psimpl.
      exists (eq x).
      split; [repeat econstructor|].
      split; [intros; subst; repeat econstructor|].
      split.
      {
        exists x. split; auto.
        destruct H7, wait_ready0, ready_inv0.
        constructor; [repeat constructor|auto].
        - inversion H2; subst.
          now forward_istep_cas_aux s t.
        - admit.
        - now setoid_rewrite <- H6.
      }
      {
        exists x. split. easy. apply eq_inj in H; subst.
        eapply StkGetCall with (i:=i).
        constructor; [|easy].
        constructor; cbn. easy.
        intros. now rewrite H0.
      }
    }

    (* step get ret *)
    clear impH. intro old. split.
    {
      clear rec. begin_commit.
      exists ρs.
      psimpl. psimpl.
      split; [repeat econstructor|].
      split; [econstructor; split; [eauto|constructor]|].
      split.
      {
        exists x3. split; auto.
        destruct H4, wait_ready0, ready_inv0.
        split.
        {
          constructor; [repeat constructor|auto].
          - inversion H2; subst.
            now forward_istep_cas_aux s t.
          - admit.
          - now setoid_rewrite <- H7.
        }
        {
          unfold eval_stack_und in same_stack0.
          exists (eval_stack (PState x3)).
          setoid_rewrite <- H7.
          inversion H2; subst.
          setoid_rewrite <- H8 in same_stack0.
          psimpl. now ddestruct H10.
        }
      }
      {
        exists x3. split. easy. apply eq_inj in H8; subst.
        eapply StkGetRetId with (i:=i).
        constructor.
        - constructor; simpl; eauto.
          now apply differ_pointwise_comm.
        - constructor; auto.
      }
    }

    (* step malloc call *)
    rewrite stepCall.
    eapply SafeBind with
      (QI:=fun _ _ => LiftSPrec (fun s x =>
          ReadyWaiting i (WFPush v) s x /\
          exists vs, list_seg (eval_heap (memSt s)) old None vs
        ))
      (QR:=fun new _ _ => LiftSPrec (fun s x =>
          ReadyWaiting i (WFPush v) s x /\
          location_owned i s new /\
          off_chain_aux (eval_heap (memSt s)) new (eval_cas (casSt s)) None /\
          off_chain_aux (eval_heap (memSt s)) new old None /\
          exists vs, list_seg (eval_heap (memSt s)) old None vs
        )).
    (* QI stable *)
    { admit. }
    (* QR stable *)
    { admit. }
    (* commit *)
    {
      clear rec. begin_commit.
      psimpl. psimpl.
      exists (eq x5).
      split; [repeat econstructor|].
      split; [intros; subst; repeat econstructor|].
      split.
      {
        exists x5. split; auto.
        destruct H5, wait_ready0, ready_inv0.
        split.
        {
          constructor; [repeat constructor|auto];
          inversion H2; subst; forward_istep_mem_aux s t.
        }
        {
          inversion H2; subst; forward_istep_mem_aux s t.
          eexists; eauto.
        }
      }
      {
        exists x5. split. easy. apply eq_inj in H10; subst.
        eapply StkAllocCall with (i:=i).
        constructor; [|easy].
        constructor; cbn. easy.
        intros. now rewrite H0.
      }
    }

    (* step malloc ret *)
    intro new. split.
    {
      clear rec. begin_commit.
      exists ρs.
      psimpl. psimpl.
      split; [repeat econstructor|].
      split; [econstructor; split; [eauto|constructor]|].
      split.
      {
        exists x4. split; auto.
        destruct H4, wait_ready0, ready_inv0.
        split; [|split; [split|split;[|split]]].
        {
          constructor; [repeat constructor|auto];
          inversion H2; subst; forward_istep_mem_aux s t.
          eapply ListSegFrame; eauto.
        }
        {
          inversion H2; subst; forward_istep_mem_aux s t.
          exists (heap_update l v0 h).
          setoid_rewrite <- H15.
          split; auto.
          ddestruct H14.
          rewrite HeapUpdateSelf; congruence.
        }
        {
          unfold location_owned.
          inversion H2; subst; forward_istep_mem_aux s t.
          eexists; split; [reflexivity|].
          ddestruct H14. apply HeapUpdateSelf.
        }
        {
          inversion H2; subst; forward_istep_mem_aux s t.
          ddestruct H14.
          eapply OffChainFrame; eauto.
        }
        {
          inversion H2; subst; forward_istep_mem_aux s t.
          ddestruct H14.
          eapply OffChainFrame; eauto.
        }
        {
          inversion H2; subst; forward_istep_mem_aux s t.
          eapply ListSegFrame in H5; eauto.
        }
      }
      {
        exists x4. split. easy. apply eq_inj in H12; subst.
        eapply StkAllocRet with (i:=i).
        constructor.
        - constructor; simpl; eauto.
          now apply differ_pointwise_comm.
        - constructor; auto.
      }
    }

    (* step write call *)
    rewrite stepCall.
    eapply SafeBind with
      (QI:=fun _ _ => LiftSPrec (fun s x =>
          ReadyWaiting i (WFPush v) s x /\
          location_owned i s new /\
          off_chain_aux (eval_heap (memSt s)) new (eval_cas (casSt s)) None /\
          off_chain_aux (eval_heap (memSt s)) new old None /\
          exists vs, list_seg (eval_heap (memSt s)) old None vs
        ))
      (QR:=fun _ _ _ => LiftSPrec (fun s x =>
          ReadyWaiting i (WFPush v) s x /\
          (exists h, (eval_heap (memSt s)) = Some h /\ h new = Some (v, old)) /\
          exists vs, list_seg (eval_heap (memSt s)) old None vs
          (* /\
          list_seg (eval_heap (memSt s)) (Some new) None (v :: vs) *)
        )).
    (* QI stable *)
    { admit. }
    (* QR stable *)
    { admit. }
    (* commit *)
    {
      clear rec. begin_commit.
      psimpl. psimpl.
      exists (eq x6).
      split; [repeat econstructor|].
      split; [intros; subst; repeat econstructor|].
      split.
      {
        exists x6. split; auto.
        destruct H5, wait_ready0, ready_inv0.
        inversion H2; subst; forward_istep_mem_aux s t.
        {
          split; [|split;[|split]]; auto.
          {
            constructor; [repeat constructor|auto];
            subst_ist s; subst_ist t; auto.
            inversion_clear 1.
            destruct H6 as [_ [? [? ?]]].
            subst_ist s.
            now inversion_clear H5.
          }
          {
            unfold location_owned in *.
            destruct H6 as [? [? [? ?]]].
            subst_ist s; subst_ist t.
            inversion H6; subst x2.
            split; eauto.
            unfold location_allocated in *.
            now subst_ist s; subst_ist t.
          }
          {
            eexists; eauto.
          }
        }
        {
          exfalso.
          unfold location_owned in *.
          destruct H6 as [_ [? [? ?]]].
          subst_ist s; subst_ist t.
          inversion H6; subst x2.
          specialize write_excl0 with (1:=eq_refl).
          congruence.
        }
      }
      {
        exists x6. split. easy. apply eq_inj in H17; subst.
        eapply StkWriteCall with (i:=i) (data:=(v,old)); [exact H6|].
        constructor; [|easy].
        constructor; cbn. easy.
        intros. now rewrite H0.
      }
    }

    (* step write ret *)
    intros. destruct v0. split.
    {
      clear rec. begin_commit.
      exists ρs.
      psimpl. psimpl.
      split; [repeat econstructor|].
      split; [econstructor; split; [eauto|constructor]|].
      split.
      {
        exists x4. split; auto.
        destruct H4, wait_ready0, ready_inv0.
        inversion H2; subst; forward_istep_mem_aux s t.
        {
          exfalso.
          destruct H5 as [[? [? ?]] _].
          setoid_rewrite <- H4 in H5.
          simpl in H5. congruence.
        }
        split; [|split].
        {
          constructor; [repeat constructor|auto];
          subst_ist s; subst_ist t; psimpl; auto.
          - eapply ListSegUpdateOffChain; eauto.
          - inversion 1.
        }
        {
          eexists; split; eauto.
          apply HeapUpdateSelf.
        }
        {
          eapply ListSegUpdateOffChain in H7; eauto.
        }
      }
      {
        exists x4. split. easy. apply eq_inj in H19; subst.
        eapply StkWriteRet with (i:=i) (data:=(v, old)); eauto.
        - destruct H5 as [? _]. auto.
        - constructor.
          + constructor; simpl; eauto.
            now apply differ_pointwise_comm.
          + constructor; auto.
      }
    }

    (* step cas call *)
    rewrite stepCall.
    eapply SafeBind with
      (QI:=fun _ _ => LiftSPrec (fun s x =>
          ReadyWaiting i (WFPush v) s x /\
          (exists h, (eval_heap (memSt s)) = Some h /\ h new = Some (v, old)) /\
          exists vs, list_seg (eval_heap (memSt s)) old None vs
        ))
      (QR:=fun r _ _ => 
          if r : bool
          then LiftSPrec (ReadyDone i (WFPush v) (PASS tt))
          else LiftSPrec (ReadyDone i (WFPush v) FAIL)).
    (* QI stable *)
    { admit. }
    (* QR stable *)
    { admit. }
    (* commit *)
    {
      clear rec. begin_commit.
      psimpl. psimpl.
      exists (eq x6).
      split; [repeat econstructor|].
      split; [intros; subst; repeat econstructor|].
      split.
      {
        exists x6. split; auto.
        destruct H5, wait_ready0, ready_inv0.
        inversion H2; subst; forward_istep_cas_aux s t.
        split; auto.
        {
          constructor; [repeat constructor|auto];
          subst_ist s; subst_ist t; auto.
        }
        {
          eexists; eauto.
        }
      }
      {
        exists x6. split. easy. apply eq_inj in H23; subst.
        eapply StkCASCall with (i:=i) (old:=old) (new:=Some new).
        constructor; [|easy].
        constructor; cbn. easy.
        now apply differ_pointwise_comm.
      }
    }

    (* step cas ret *)
    intros. split.
    {
      clear rec. begin_commit.
      psimpl.
      destruct H4, wait_ready0, ready_inv0.
      destruct always_atomic0 as [vs ?].
      destruct x4; simpl in *.
      destruct ready_wait0.
      psimpl. psimpl.
      inversion H2; subst; forward_istep_cas_aux s t;
      ddestruct H34; psimpl.
      (* cas succ *)
      {
        exists (eq (
          comRetPoss i
            (comInvPoss i
              (MkPoss T (F A) VF (WFSsIdle vs) PCalls PRets)
              (WFPush v)
              (WFSsPend i vs (WFPush v))
            )
            (WFPush v)
            (WFSsIdle (v :: vs))
            (PASS tt)
        )).
        split; [repeat econstructor|].
        split; [econstructor; split; [now eauto|]|split].
        (* poss step *)
        {
          subst.
          (* commit call *)
          eapply PossStepsStep with (i := i) (σ := (comInvPoss i
            (MkPoss T (F A) VF (WFSsIdle vs) PCalls PRets)
            (WFPush v)
            (WFSsPend i vs (WFPush v))
          )); psimpl; auto.
          {
             eapply PCommitCall with (m := WFPush v); psimpl; auto;
             [constructor|now rewrite eqb_id].
          }
          {
            intros; rewrite eqb_nid; auto.
          }
          (* commit ret *)
          eapply PossStepsStep with (i := i);
          [| | |apply PossStepsRefl];
          psimpl; auto.
          {
            eapply PCommitRet with (m := WFPush v) (v := PASS tt);
            psimpl; auto; try now rewrite eqb_id.
            constructor.
          }
          {
            intros; rewrite eqb_nid; auto.
          }
        }
        (* post condition *)
        {
          assert (vs = x5) by (eapply ListSegUnique; eauto); subst x5.
          eexists; split; eauto.
          constructor; constructor; [constructor| |]; psimpl;
          try now rewrite eqb_id.
          - subst_ist s; subst_ist t; psimpl; auto.
            econstructor; eauto.
          - unfold wfs_idle in *; psimpl; eauto.
          - subst_ist s; subst_ist t; auto.
        }
        (* guarantee *)
        {
          exists (comRetPoss i
          (comInvPoss i (MkPoss T (F A) VF (WFSsIdle vs) PCalls PRets) 
             (WFPush v) (WFSsPend i vs (WFPush v))) (WFPush v) (WFSsIdle (v :: vs)) 
          (PASS tt)).
          split. easy. apply eq_inj in H20; subst.
          (* inversion H6; subst; clear H6. *)
          eapply StkCASRetPushPass with (i:=i) (v:=v) (new:=new) (old:=old); eauto.
          constructor.
          - constructor; simpl; eauto.
            now apply differ_pointwise_comm.
          - constructor; psimpl; auto.
            subst_ist s; subst_ist t; auto.
          - eapply VStep with (y:=comInvPoss i
              (MkPoss T (F A) VF (WFSsIdle vs) PCalls PRets)
              (WFPush v)
              (WFSsPend i vs (WFPush v))); psimpl; auto;
              [
                constructor; psimpl; auto;
                [constructor|now rewrite eqb_id]|
                apply differ_pointwise_trivial|
                unfold differ_pointwise; auto|
              ].
            eapply VStep; [| | |apply VRefl];
            psimpl; auto;
            try apply differ_pointwise_trivial;
            try (unfold differ_pointwise; auto).
            constructor; psimpl; auto;
            try now rewrite eqb_id.
            constructor.
        }
      }
      (* cas fail *)
      {
        exists (eq (
          comRetPoss i
            (comInvPoss i
              (MkPoss T (F A) VF (WFSsIdle vs) PCalls PRets)
              (WFPush v)
              (WFSsPend i vs (WFPush v))
            )
            (WFPush v)
            (WFSsIdle vs)
            (FAIL)
        )).
        split; [repeat econstructor|].
        split; [econstructor; split; [now eauto|]|split].
        (* poss step *)
        {
          subst.
          (* commit call *)
          eapply PossStepsStep with (i := i) (σ := (comInvPoss i
            (MkPoss T (F A) VF (WFSsIdle vs) PCalls PRets)
            (WFPush v)
            (WFSsPend i vs (WFPush v))
          )); psimpl; auto.
          {
             eapply PCommitCall with (m := WFPush v); psimpl; auto;
             [constructor|now rewrite eqb_id].
          }
          {
            intros; rewrite eqb_nid; auto.
          }
          (* commit ret *)
          eapply PossStepsStep with (i := i);
          [| | |apply PossStepsRefl];
          psimpl; auto.
          {
            eapply PCommitRet with (m := WFPush v) (v := FAIL);
            psimpl; auto; try now rewrite eqb_id.
            constructor.
          }
          {
            intros; rewrite eqb_nid; auto.
          }
        }
        (* post condition *)
        {
          eexists; split; eauto.
          constructor; constructor; [constructor| |]; psimpl;
          try (now rewrite eqb_id);
          subst_ist s; subst_ist t; psimpl; auto.
          unfold wfs_idle in *; psimpl; eauto.
        }
        (* guarantee *)
        {
          exists (comRetPoss i
          (comInvPoss i (MkPoss T (F A) VF (WFSsIdle vs) PCalls PRets) 
             (WFPush v) (WFSsPend i vs (WFPush v))) (WFPush v) 
          (WFSsIdle vs) FAIL).
          split. easy. apply eq_inj in H20; subst.
          (* inversion H6; subst; clear H6. *)
          eapply StkCASRetPushFail with (i:=i) (v:=v) (new:=Some new) (old:=old); eauto.
          constructor.
          - constructor; simpl; eauto.
            now apply differ_pointwise_comm.
          - constructor; psimpl; auto.
            subst_ist s; subst_ist t; auto.
          - eapply VStep with (y:=comInvPoss i
              (MkPoss T (F A) VF (WFSsIdle vs) PCalls PRets)
              (WFPush v)
              (WFSsPend i vs (WFPush v))); psimpl; auto;
              [
                constructor; psimpl; auto;
                [constructor|now rewrite eqb_id]|
                apply differ_pointwise_trivial|
                unfold differ_pointwise; auto|
              ].
            eapply VStep; [| | |apply VRefl];
            psimpl; auto;
            try apply differ_pointwise_trivial;
            try (unfold differ_pointwise; auto).
            constructor; psimpl; auto;
            try now rewrite eqb_id.
            constructor.
        }
      }
    }

    (* ret *)
    destruct v0; psimpl.
    {
      apply SafeReturn.
      unfold sub, subRelt.
      intros. unfold LiftSPrec in H.
      psimpl. exists x4. now destruct H3.
    }
    {
      apply SafeReturn.
      unfold sub, subRelt.
      intros. unfold LiftSPrec in H.
      psimpl. exists x4. now destruct H3.
    }
  Admitted.

  Lemma PopCorrect: forall (i : Name T),
    @VerifyProg T (E A) (F A) VE VF (StkRet (option A)) i
      (@LiftSRelt T (E A) (F A) VE VF (Rely i))
      (@LiftSRelt T (E A) (F A) VE VF (Guar i))
      (@ReltCompose T (E A) (F A) VE VF
        (@prComp T (E A) (F A) VE VF (@LiftSPrec T (E A) (F A) VE VF (Ready i))
            (@TInvoke T (E A) (F A) VE VF (WFStack A) i (StkRet (option A)) (@WFPop A)))
        (@LiftSRelt T (E A) (F A) VE VF (Rely i)))
      (WFStack A (StkRet (option A)) (@WFPop A))
      (fun (r : StkRet (option A)) (_ : @InterState T (E A) (F A) VE)
        (_ : @PossSet T (F A) VF) =>
      @LiftSPrec T (E A) (F A) VE VF (@ReadyDone i (StkRet (option A)) (@WFPop A) r)).
  Proof.
    intros.
    eapply weakenPrec with (P:=fun _ _ => LiftSPrec (ReadyWaiting i WFPop)).
    2:{
      unfold sub, subRelt, LiftSPrec, LiftSRelt.
      intros. psimpl.
      assert (x0 = eq (invPoss i x1 WFPop)).
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
      assert (ReadyWaiting i WFPop x (invPoss i x1 WFPop)).
      {
        assert (snd s = snd x).
        { unfold TInvoke in H1. now psimpl. }
        drecs.
        constructor.
        {
          constructor.
          constructor; cbn;
          unfold wfs_idle, eval_stack_und, memSt, casSt in *;
          auto; try now setoid_rewrite <- H.
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
      P ==> (fun _ _ => LiftSPrec (ReadyWaiting i WFPop)) ->
        VerifyProg i (LiftSRelt (Rely i)) (LiftSRelt (Guar i))
          P
          wfpop
          (fun r _ _ => LiftSPrec (ReadyDone i WFPop r))
    ).
    { intros. now apply H. }
    cofix rec. intros P impH. unfold wfpop.

    (* step get call *)
    rewrite stepCall.
    eapply SafeBind with
      (QI:=fun _ _ => LiftSPrec (ReadyWaiting i WFPop))
      (QR:=fun old _ _ => LiftSPrec (fun s x =>
          match old with
          | Some _ =>
            ReadyWaiting i WFPop s x /\
            exists vs, list_seg (eval_heap (memSt s)) old None vs
          | None =>
            ReadyDone i WFPop (PASS None) s x
          end
        )).
    (* stable QI *)
    { admit. }
    (* stable QR *)
    { admit. }
    (* commit *)
    {
      clear rec. begin_commit.
      psimpl. apply impH in H.
      clear impH. psimpl.
      unfold LiftSPrec in H. psimpl.
      exists (eq x).
      split; [repeat econstructor|].
      split; [intros; subst; repeat econstructor|].
      split.
      {
        exists x. split; auto.
        destruct H7, wait_ready0, ready_inv0.
        constructor; [repeat constructor|auto].
        - inversion H2; subst.
          now forward_istep_cas_aux s t.
        - admit.
        - now setoid_rewrite <- H6.
      }
      {
        exists x. split. easy. apply eq_inj in H; subst.
        eapply StkGetCall with (i:=i).
        constructor; [|easy].
        constructor; cbn. easy.
        intros. now rewrite H0.
      }
    }

    (* step get ret *)
    clear impH. intro old. split.
    {
      clear rec. begin_commit.
      
      inversion H2; psimpl; psimpl.
      inversion H2; subst.
      ddestruct H6.

      destruct H9, wait_ready0, ready_inv0.
      subst_ist s; subst_ist t; psimpl.
      
      destruct old.
      (* non-empty stack *)
      {
        exists (eq x3).
        psimpl. psimpl.
        split; [repeat econstructor|].
        split; [econstructor; split; [eauto|constructor]|].
        split.
        {
          exists x3. split; auto.
          split.
          - constructor; [repeat constructor|auto]; auto;
            try now subst_ist s; subst_ist t.
          - subst_ist s; subst_ist t.
            eexists; eauto.
        }
        {
          exists x3. split. easy. apply eq_inj in H3; subst.
          eapply StkGetRetId with (i:=i) (old:=Some a).
          constructor.
          - constructor; simpl; eauto.
            now apply differ_pointwise_comm.
          - constructor; auto.
            subst_ist s; subst_ist t.
            constructor.
        }
      }  
      (* empty stack *)
      {
        destruct ready_wait0.
        destruct x3; subst; psimpl.
        inversion always_atomic0; psimpl.
        inversion same_stack0; try congruence.
        subst_ist s; psimpl.

        exists (eq (
          comRetPoss i
            (comInvPoss i
              (MkPoss T (F A) VF (WFSsIdle []) PCalls PRets)
              WFPop
              (WFSsPend i [] WFPop)
            )
            WFPop
            (WFSsIdle [])
            (PASS None)
        )).
        split; [repeat econstructor|].
        split; [econstructor; split; [now eauto|]|split].
        (* poss step *)
        {
          subst.
          (* commit call *)
          eapply PossStepsStep with (i := i) (σ := (comInvPoss i
            (MkPoss T (F A) VF (WFSsIdle []) PCalls PRets)
            WFPop
            (WFSsPend i [] WFPop)
          )); psimpl; auto.
          {
            eapply PCommitCall with (m := WFPop); psimpl; auto;
            [constructor|now rewrite eqb_id].
          }
          {
            intros; rewrite eqb_nid; auto.
          }
          (* commit ret *)
          eapply PossStepsStep with (i := i);
          [| | |apply PossStepsRefl];
          psimpl; auto.
          {
            eapply PCommitRet with (m := WFPop) (v := PASS None);
            psimpl; auto; try now rewrite eqb_id.
            constructor.
          }
          {
            intros; rewrite eqb_nid; auto.
          }
        }
        (* post condition *)
        {
          eexists; split; eauto.
          constructor; constructor; [constructor| |]; psimpl;
          try now rewrite eqb_id.
          - subst_ist s; subst_ist t; psimpl; auto.
          - unfold wfs_idle in *; psimpl; eauto.
          - subst_ist s; subst_ist t; auto.
        }
        (* guarantee *)
        {
          exists (comRetPoss i
          (comInvPoss i (MkPoss T (F A) VF (WFSsIdle []) PCalls PRets) WFPop
             (WFSsPend i [] WFPop)) WFPop (WFSsIdle []) (PASS None)).
          split. easy. apply eq_inj in H5; subst.
          (* inversion H6; subst; clear H6. *)
          eapply StkGetRetEmp with (i:=i).
          constructor.
          - constructor; simpl; eauto.
            now apply differ_pointwise_comm.
          - constructor; psimpl; auto.
            subst_ist s; subst_ist t; auto.
          - eapply VStep with (y:=comInvPoss i
            (MkPoss T (F A) VF (WFSsIdle []) PCalls PRets)
            WFPop
            (WFSsPend i [] WFPop)); psimpl; auto;
              [
                constructor; psimpl; auto;
                [constructor|now rewrite eqb_id]|
                apply differ_pointwise_trivial|
                unfold differ_pointwise; auto|
              ].
            eapply VStep; [| | |apply VRefl];
            psimpl; auto;
            try apply differ_pointwise_trivial;
            try (unfold differ_pointwise; auto).
            constructor; psimpl; auto;
            try now rewrite eqb_id.
            constructor.
        }
      }
    }

    destruct old as [old |].
    (* handle empty stack return case first *)
    2:{
      apply SafeReturn.
      unfold sub, subRelt.
      intros. unfold LiftSPrec in H.
      psimpl. exists x3. now destruct H2.
    }

    (* step read call *)
    rewrite stepCall.
    eapply SafeBind with
      (QI:=fun _ _ => LiftSPrec (fun s x =>
          ReadyWaiting i WFPop s x /\
          exists vs, list_seg (eval_heap (memSt s)) (Some old) None vs))
      (QR:=fun r _ _ => LiftSPrec (fun s x =>
          match r with (v, next) =>
          ReadyWaiting i WFPop s x /\
          (exists h, (eval_heap (memSt s)) = Some h /\ h old = Some (v, next)) /\
          exists vs, list_seg (eval_heap (memSt s)) (Some old) None (v :: vs)
          end
        )).
    (* QI stable *)
    { admit. }
    (* QR stable *)
    { admit. }
    (* commit *)
    {
      clear rec. begin_commit.
      do 2 psimpl.
      destruct H5 as [Hready Hwait];
      destruct Hready as [Hinv]; destruct Hinv.

      exists (eq x5).
      split; [repeat econstructor|].
      split; [intros; subst; repeat econstructor|].
      split.
      {
        inversion H2; subst; subst_ist s; subst_ist t;
        psimpl; [|inversion same_stack0; congruence].
        exists x5. split; auto.
        split; eauto.
        constructor; [do 2 constructor|auto];
        try now subst_ist s; subst_ist t.
      }
      {
        exists x5. split. easy. apply eq_inj in H5; subst.
        eapply StkReadCall with (i:=i) (addr:=old).
        constructor; [|easy].
        constructor; cbn. easy.
        intros. now rewrite H0.
      }
    }

    (* step read ret *)
    intros [v next]. split.
    {
      clear rec. begin_commit. psimpl. psimpl.
      destruct H4, wait_ready0, ready_inv0.

      exists (eq x4).
      split; [repeat econstructor|].
      split; [intros; subst; repeat econstructor|].
      split.
      {
        inversion H2; subst; forward_istep_mem_aux s t.
        (* old must be non-empty *)
        2:{
          exfalso.
          inversion H5; subst.
          congruence.
        }
        exists x4; split; auto.
        split.
        {
          constructor; [do 2 constructor|auto];
          try now subst_ist s; subst_ist t.
        }
        {
          ddestruct H15.
          inversion H5; subst.
          inversion H14; subst h0.
          inversion H12; subst l.
          rewrite H13 in H15; inversion H15; subst.
          eauto.
        }
      }
      {
        exists x4. split. easy. apply eq_inj in H4; subst.
        eapply StkReadRet with (i:=i) (addr:=old) (v:=(v, next)).
        - inversion H5; subst.
          inversion H4; subst.
          unfold location_allocated.
          subst_ist s.
          eexists; split; eauto.
          congruence.
        - constructor; [|easy].
          constructor; cbn. easy.
          intros. now rewrite H0.
      }
    }

    (* step cas call *)
    rewrite stepCall.
    eapply SafeBind with
      (QI:=fun _ _ => LiftSPrec (fun s x =>
          ReadyWaiting i WFPop s x /\
          (exists h, (eval_heap (memSt s)) = Some h /\ h old = Some (v, next)) /\
          exists vs, list_seg (eval_heap (memSt s)) (Some old) None (v :: vs)
        ))
      (QR:=fun b _ _ => LiftSPrec (fun s x =>
          if b : bool
          then ReadyDone i WFPop (PASS (Some v)) s x
          else ReadyDone i WFPop FAIL s x
        )).
    (* QI stable *)
    { admit. }
    (* QR stable *)
    { admit. }
    (* commit *)
    {
      clear rec. begin_commit.
      do 2 psimpl.
      destruct H5 as [Hready Hwait];
      destruct Hready as [Hinv]; destruct Hinv.

      exists (eq x6).
      split; [repeat econstructor|].
      split; [intros; subst; repeat econstructor|].
      split.
      {
        inversion H2; subst; subst_ist s; subst_ist t.
        exists x6. split; auto.
        split; eauto.
        constructor; [do 2 constructor|auto];
        try now subst_ist s; subst_ist t.
      }
      {
        exists x6. split. easy. apply eq_inj in H5; subst.
        eapply StkCASCall with (i:=i) (old:=Some old) (new:=next).
        constructor; [|easy].
        constructor; cbn. easy.
        intros. now rewrite H0.
      }
    }
    
    split.
    {
      clear rec. begin_commit.
      psimpl.
      destruct H4, wait_ready0, ready_inv0.
      destruct always_atomic0 as [vs0 ?].
      destruct x4; simpl in *.
      destruct ready_wait0.
      psimpl. psimpl.
      inversion H2; subst; forward_istep_cas_aux s t;
      ddestruct H24; psimpl.
      (* cas succ *)
      {
        rename x5 into vs.
        assert (vs0 = v :: vs) by (eapply ListSegUnique; eauto); subst.

        exists (eq (
          comRetPoss i
            (comInvPoss i
              (MkPoss T (F A) VF (WFSsIdle (v :: vs)) PCalls PRets)
              WFPop
              (WFSsPend i (v :: vs) WFPop)
            )
            WFPop
            (WFSsIdle vs)
            (PASS (Some v))
        )).
        split; [repeat econstructor|].
        split; [econstructor; split; [now eauto|]|split].
        (* poss step *)
        {
          subst.
          (* commit call *)
          eapply PossStepsStep with (i := i) (σ := (comInvPoss i
            (MkPoss T (F A) VF (WFSsIdle (v :: vs)) PCalls PRets)
            WFPop
            (WFSsPend i (v :: vs) WFPop)
          )); psimpl; auto.
          {
            eapply PCommitCall with (m := WFPop); psimpl; auto;
            [constructor|now rewrite eqb_id].
          }
          {
            intros; rewrite eqb_nid; auto.
          }
          (* commit ret *)
          eapply PossStepsStep with (i := i);
          [| | |apply PossStepsRefl];
          psimpl; auto.
          {
            eapply PCommitRet with (m := WFPop) (v := PASS (Some v));
            psimpl; auto; try now rewrite eqb_id.
            constructor.
          }
          {
            intros; rewrite eqb_nid; auto.
          }
        }
        (* post condition *)
        {
          eexists; split; eauto.
          constructor; constructor; [constructor| |]; psimpl;
          try now rewrite eqb_id.
          - inversion same_stack0; subst.
            subst_ist s; subst_ist t; psimpl; auto.
            inversion H21; subst l.
            rewrite H5 in H22; inversion H22; subst x6.
            rewrite H7 in H26; inversion H26; subst l2.
            auto.
          - unfold wfs_idle in *; psimpl; eauto.
          - subst_ist s; subst_ist t; auto.
        }
        (* guarantee *)
        {
          exists (
            comRetPoss i
              (comInvPoss i
                (MkPoss T (F A) VF (WFSsIdle (v :: vs)) PCalls PRets)
                WFPop
                (WFSsPend i (v :: vs) WFPop)
              )
              WFPop
              (WFSsIdle vs)
              (PASS (Some v))
          ).
          split. easy. apply eq_inj in H17; subst.
          (* inversion H6; subst; clear H6. *)
          eapply StkCASRetPopPass with (i:=i) (v:=v) (new:=next) (old:=old); eauto.
          constructor.
          - constructor; simpl; eauto.
            now apply differ_pointwise_comm.
          - constructor; psimpl; auto.
            subst_ist s; subst_ist t; auto.
          - eapply VStep with (y:=(comInvPoss i
              (MkPoss T (F A) VF (WFSsIdle (v :: vs)) PCalls PRets)
              WFPop
              (WFSsPend i (v :: vs) WFPop)
            )); psimpl; auto;
              [
                constructor; psimpl; auto;
                [constructor|now rewrite eqb_id]|
                apply differ_pointwise_trivial|
                unfold differ_pointwise; auto|
              ].
            eapply VStep; [| | |apply VRefl];
            psimpl; auto;
            try apply differ_pointwise_trivial;
            try (unfold differ_pointwise; auto).
            constructor; psimpl; auto;
            try now rewrite eqb_id.
            constructor.
        }
      }
      (* cas fail *)
      {
        exists (eq (
          comRetPoss i
            (comInvPoss i
              (MkPoss T (F A) VF (WFSsIdle vs0) PCalls PRets)
              WFPop
              (WFSsPend i vs0 WFPop)
            )
            WFPop
            (WFSsIdle vs0)
            FAIL
        )).
        split; [repeat econstructor|].
        split; [econstructor; split; [now eauto|]|split].
        (* poss step *)
        {
          subst.
          (* commit call *)
          eapply PossStepsStep with (i := i) (σ := (comInvPoss i
            (MkPoss T (F A) VF (WFSsIdle vs0) PCalls PRets)
            WFPop
            (WFSsPend i vs0 WFPop)
          )); psimpl; auto.
          {
            eapply PCommitCall with (m := WFPop); psimpl; auto;
            [constructor|now rewrite eqb_id].
          }
          {
            intros; rewrite eqb_nid; auto.
          }
          (* commit ret *)
          eapply PossStepsStep with (i := i);
          [| | |apply PossStepsRefl];
          psimpl; auto.
          {
            eapply PCommitRet with (m := WFPop) (v := FAIL);
            psimpl; auto; try now rewrite eqb_id.
            constructor.
          }
          {
            intros; rewrite eqb_nid; auto.
          }
        }
        (* post condition *)
        {
          eexists; split; eauto.
          constructor; constructor; [constructor| |]; psimpl;
          try (now rewrite eqb_id);
          subst_ist s; subst_ist t; psimpl; auto.
          unfold wfs_idle in *; psimpl; eauto.
        }
        (* guarantee *)
        {
          exists (comRetPoss i
            (comInvPoss i
              (MkPoss T (F A) VF (WFSsIdle vs0) PCalls PRets)
              WFPop
              (WFSsPend i vs0 WFPop)
            )
            WFPop
            (WFSsIdle vs0)
            FAIL).
          split. easy. apply eq_inj in H17; subst.
          (* inversion H6; subst; clear H6. *)
          eapply StkCASRetPopFail with (i:=i) (new:=next) (old:=Some old); eauto.
          constructor.
          - constructor; simpl; eauto.
            now apply differ_pointwise_comm.
          - constructor; psimpl; auto.
            subst_ist s; subst_ist t; auto.
          - eapply VStep with (y:=comInvPoss i
              (MkPoss T (F A) VF (WFSsIdle vs0) PCalls PRets)
              WFPop
              (WFSsPend i vs0 WFPop)); psimpl; auto;
              [
                constructor; psimpl; auto;
                [constructor|now rewrite eqb_id]|
                apply differ_pointwise_trivial|
                unfold differ_pointwise; auto|
              ].
            eapply VStep; [| | |apply VRefl];
            psimpl; auto;
            try apply differ_pointwise_trivial;
            try (unfold differ_pointwise; auto).
            constructor; psimpl; auto;
            try now rewrite eqb_id.
            constructor.
        }
      }
    }
    
    (* ret *)
    destruct v0;
    apply SafeReturn;
    unfold sub, subRelt;
    intros; unfold LiftSPrec in H;
    psimpl; exists x4; now destruct H3.
  Admitted.

  Theorem WFStackCorrect:
    VerifyImpl VE VF
    (fun i => LiftSRelt (Rely i))
    (fun i => LiftSRelt (Guar i))
    (fun i _ _ => LiftSPrec (Ready i))
    (WFStack A)
    (fun i _ m r _ _ => LiftSPrec (ReadyDone i m r))
    (TReturn (WFStack A)).
  Proof.
    constructor;
    [
      apply RelyReflexive|
      apply RelyClosed|
      apply GuarInRely|
      apply InvokeInRely|
      apply ReturnInRely|
      apply InitialReady|
      apply ReadyStable|
      | |
    ].
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
      constructor; constructor.
      {
        unfold eval_stack_und, memSt, casSt in *.
        setoid_rewrite <- H4.
        setoid_rewrite H10.
        easy.
      }
      {
        unfold wfs_idle in *.
        now setoid_rewrite H10.
      }
      {
        intros.
        unfold eval_stack_und, memSt, casSt in *.
        setoid_rewrite <- H4 in H2. 
        eapply write_excl0; eauto.
      }
    }
    {
      intros. destruct m.
      {
        eapply weakenPost.
        apply PushCorrect.
        {
          unfold sub, subRelt, LiftSPrec.
          intros. psimpl. eexists. split. easy.
          destruct v0; easy.
        }
      }
      {
        eapply weakenPost.
        apply PopCorrect.
        {
          unfold sub, subRelt, LiftSPrec.
          intros. psimpl. eexists. easy.
        }
      }
    }
    {
      unfold ReturnStep, LiftSPrec.
      intros. psimpl. exists (eq x1).
      split. do 2 econstructor.
      split. intros. subst.
      do 3 econstructor.
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
        intros. apply eq_inj in H; subst.
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
End AtomicWFStackProof.


