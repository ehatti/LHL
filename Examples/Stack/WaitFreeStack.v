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

Section AtomicWFStackProof.
  Import AtomicWFStack.

  Context {T : nat} {A : Type}.

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
    Inductive on_chain_written_aux {T} (s:option Heap) (loc:Heap) : option Addr (*head*) -> option Addr (*tail*) -> Prop :=
    | OCWNil l1:
        on_chain_written_aux s loc l1 l1
    | OCWCons h l l1 l2 l3 (v:A):
        s = Some h ->
        l1 = Some l ->
        h l = Some (v, l2) ->
        loc l = Some (@LWritten T) ->
        on_chain_written_aux s loc l2 l3 ->
        on_chain_written_aux s loc l1 l3
    .

    Definition on_chain_written (s:ISt) :=
      on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) (eval_cas (casSt s)) None.

    Lemma OCWAlloc {T1} : forall h l loc hd v (i:Name T1),
      h l = None ->
      on_chain_written_aux (Some h) loc hd None ->
      on_chain_written_aux
        (Some (heap_update l v h))
        (heap_update l (LAlloc i) loc)
        hd None.
    Proof.
      intros.
      remember None as tl.
      generalize dependent tl.
      induction H0; intros; subst.
      - constructor.
      - specialize (IHon_chain_written_aux _ eq_refl H4).
        inversion H; subst h0.
        assert (l <> l0) by congruence.
        eapply OCWCons; eauto;
        rewrite HeapUpdateOther; eauto.
    Qed.        

    Lemma OWCWrite {T1} : forall h loc hd (i:Name T1) data new,
      loc new = Some (LAlloc i) ->
      on_chain_written_aux (Some h) loc hd None ->
      on_chain_written_aux (Some (heap_update new data h)) (heap_update new LWritten loc) hd None.
    Proof.
      intros.
      remember None as tl.
      generalize dependent tl.
      induction 2; intros; subst.
      - constructor.
      - inversion H0; subst.
        assert (l <> new) by congruence.
        eapply OCWCons; eauto;
        rewrite HeapUpdateOther; eauto.
    Qed.

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

    Definition off_chain (s:ISt) (l:Addr) :=
        off_chain_aux (eval_heap (memSt s)) l (eval_cas (casSt s)) None.

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
    
    Lemma OwnedOffChain {T1}: forall h loc (i:Name T1) new hd,
      loc new = Some (LAlloc i) ->
      on_chain_written_aux (Some h) loc hd None ->
      off_chain_aux (Some h) new hd None.
    Proof.
      intros.
      remember None as tl.
      revert H Heqtl.
      induction H0; intros; subst.
      - constructor.
      - eapply OffChainCons; eauto.
        congruence.
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
    eval_loc (memSt s) l = Some (LAlloc i).
  
  (* Definition location_clean (s:ISt) (l:Addr) : Prop :=
    location_allocated s l /\
    exists loc, eval_loc (memSt s) = Some loc /\ loc l = Some LWritten. *)
  
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
      (* (H_alloc: location_allocated s1 new)
      (H_off_chain: off_chain s1 new) *)
      (H_owned: location_owned i s1 new):
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
      (H_loc: eval_loc (memSt s1) new = Some LWritten)
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
        loc l = Some (LAlloc j);
    ocw:
      on_chain_written s
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
    unfold on_chain_written in *;
    unfold location_owned, location_allocated in *;
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
    end; simpl in *.

    Ltac forward_istep_cas_aux s1 s2 :=
      (* match goal with
      | same_stack0 : eval_stack_und _ _ |- _ => *)
        subst_ist s1; subst_ist s2;
        simpl in *; eauto;
        try congruence.
      (* end. *)

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
      subst_ist s1; subst_ist s2;
      simpl in *; eauto;
      try match goal with
      | H : list_seg None _ _ _ |- _ =>
         try (inversion H; congruence)
      end;
      try congruence.
  
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
      {
        unfold on_chain_written, memSt; simpl.
        constructor.
      }
    Qed.

    Lemma sing_elem {B} {P : B -> Prop} :
      forall x : B,
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
          destruct H_owned as [_ ?].
          forward_istep_mem.
          specialize (write_excl0 _ _ _ _ _ eq_refl).
          congruence.
        }
        (* write ret *)
        {
          unfold on_chain_written in ocw0.
          destruct H_owned as [[? [? ?]] ?].
          forward_istep_mem.
          
          eapply ListSegUpdateOffChain; eauto.
          eapply OwnedOffChain; eauto.
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
            ddestruct H22.
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
        inversion H0; subst; clear H0;
        unfold wfs_idle in *; eauto;
        try (unfold_possteps;
        forward_pstep p1 y;
        setoid_rewrite <- H1 in always_atomic0;
        forward_pstep y p2;
        simp_eqs; simpl in *; now eauto).
        {
          unfold InvokeAny, TInvoke, TIdle in H.
          psimpl. apply sing_elem in H2. psimpl.
          setoid_rewrite H5. eauto.
        }
        (* return any *)
        {
          unfold ReturnAny, TReturn, mapRetPoss in H.
          psimpl. apply sing_elem in H2. psimpl.
          setoid_rewrite H10. eauto.
        }
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
          destruct H_owned as [_ ?].
          setoid_rewrite <- H5 in H.
          inversion_clear H. auto.
        }
      }
      {
        inversion_clear H.
        unfold on_chain_written in *.
        inversion H0; subst; clear H0;
        (* irrelevant cas events *)
        try (forward_istep_cas; now auto);
        try (forward_istep_mem; now auto).
        {
          unfold InvokeAny, TInvoke, TIdle in H.
          psimpl. unfold memSt, casSt in *.
          setoid_rewrite <- H1. auto.
        }
        {
          unfold ReturnAny, TReturn, mapRetPoss in H.
          psimpl. unfold memSt, casSt in *.
          setoid_rewrite <- H1. auto.
        }
        {
          forward_istep_mem.
          eapply OCWAlloc; auto.
        }
        {
          destruct H_owned.
          forward_istep_mem.
          specialize (write_excl0 _ _ _ _ _ eq_refl).
          congruence.
        }
        {
          destruct H_owned as [[? [? ?]]].
          forward_istep_mem.
          eapply OWCWrite; eauto.
        }
        {
          destruct H_alloc as [? [? ?]].
          forward_istep_mem. 
        }
        {
          forward_istep_cas; auto.
          rewrite H_heap in *.
          econstructor; eauto.
        }
        {
          forward_istep_cas; auto.
          ddestruct H7.
        }
        {
          forward_istep_cas; auto.
          rewrite H_heap in *.
          inversion ocw0; subst.
          inversion H; subst.
          inversion H6; subst.
          rewrite H_new in *.
          inversion H7; subst; auto.
        }
        {
          forward_istep_cas; auto.
          ddestruct H7.
        }
      }
    Qed.

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

    Ltac forward_inv_ret:=
      unfold InvokeAny, TInvoke, TIdle,
          ReturnAny, TReturn, Returned, mapRetPoss in *;
      psimpl;
      match goal with
      | H:eq _ = _ |- _ => 
        apply sing_elem in H
      end; psimpl;
      unfold memSt, casSt in *.

    Ltac solve_inv_ret:=
      forward_inv_ret;
      match goal with
      | H:snd _ = snd _ |- _ => 
        setoid_rewrite <- H
      end; eauto.

    Ltac solve_dp :=
      repeat match goal with
      | H:differ_pointwise _ ?y _ |- ?y _ = _ =>
        rewrite H; auto
      end.

    Lemma ready_done_stable (i : Name T) {R} (m : F A R) (r:R):
      SStable (Rely i) (ReadyDone i m r).
    Proof.
      begin_stable.
      eapply SRTC_stable.
      2: exact H. 2: exact H0.
      clear. intros.
      destruct H.
      constructor;
      destruct H0 as [j [? ?]].
      {
        destruct done_ready0.
        constructor. eapply InvStable; eauto.
      }
      {
        destruct ready_done0.
        inversion H0; subst; clear H0;
        try (constructor; now forward_istep_cas);
        try (constructor; now forward_istep_mem);
        try (constructor; solve_inv_ret);
        try (unfold_possteps; now (constructor; solve_dp)).
        {
          forward_inv_ret.
          constructor.
          - rewrite H8; auto.
          - rewrite H9; auto.
        }
        {
          forward_inv_ret.
          constructor.
          - rewrite H8; auto.
          - rewrite H9; auto.
        }
      }
    Qed.

    Lemma get_post_stable (i : Name T) old {R} (m : F A R) vs0:
      SStable (Rely i) (fun s x =>
        ReadyWaiting i m s x /\
        on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) old None /\
        exists vs, list_seg (eval_heap (memSt s)) old None (vs0 ++ vs)
      ).
    Proof.
      begin_stable.
      remember (fun s (ρ:Poss VF) => ReadyWaiting i m s ρ /\
      on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) old None /\
      (exists vs : list A, list_seg (eval_heap (memSt s)) old None (vs0 ++ vs))) as P.
      replace (ReadyWaiting i m s ρ /\
      on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) old None /\
      (exists vs : list A, list_seg (eval_heap (memSt s)) old None (vs0 ++ vs)))
      with (P s ρ); [|subst; auto].
      eapply SRTC_stable;
      subst; eauto.
      clear. intros; simpl in *.
      destruct H0 as [j [? ?]].
      destruct H.
      split; [|split].
      {
        eapply ready_waiting_stable.
        psplit; eauto.
        econstructor; eauto.
        constructor.
      }
      {
        destruct H2 as [? ?].
        inversion H1; subst; clear H1;
        try forward_istep_cas;
        try forward_istep_mem.
        {
          unfold InvokeAny, TInvoke, TIdle in *. psimpl.
          apply sing_elem in H6. psimpl.
          unfold memSt in *.
          setoid_rewrite <- H5. eauto.
        }
        {
          unfold ReturnAny, TReturn, Returned, mapRetPoss in *. psimpl.
          apply sing_elem in H6. psimpl.
          unfold memSt in *.
          setoid_rewrite <- H5. eauto.
        }
        {
          eapply OCWAlloc; eauto.
        }
        {
          destruct H as [[[?]]].
          subst_ist s.
          specialize (write_excl0 _ _ _ _ _ eq_refl).
          destruct H_owned.
          simpl in *.
          congruence.
        }
        {
          destruct H_owned as [[? [? ?]] ?].
          subst_ist s.
          congruence.
        }
        {
          destruct H_owned as [[? [? ?]] ?].
          subst_ist s.
          eapply OWCWrite; eauto.
        }
        {
          destruct H_alloc as [? [? ?]].
          subst_ist s; congruence.
        }
      }
      {
        destruct H2 as [Hocw H2].
        inversion H1; subst; clear H1;
        try (match goal with
        | H : IStep _ ?s1 _ ?s2 |- _ =>
          inversion H; subst; clear H;
          try match goal with
          | H1 : StateStep _ _ _ |- _ =>
            inversion H1; psimpl
          end;
          subst_ist s1; subst_ist s2
        end; simpl in *; eauto).
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
          destruct H_owned as [[? [? ?]] ?].
          inversion H3; subst; clear H3;
          subst_ist s; subst_ist t;
          simpl in *; eauto.
          destruct H as [[[?]] _].
          eapply write_excl0 in H12.
          inversion H9; subst.
          congruence.
        }
        {
          destruct H as [[[?]] _].
          destruct H_owned as [[? [? ?]] ?].
          inversion H3; subst; clear H3;
          subst_ist s; subst_ist t;
          simpl in *; eauto.
          - specialize (write_excl0 _ _ _ _ _ eq_refl).
            congruence.
          - eexists.
            eapply ListSegUpdateOffChain; eauto.
            eapply OwnedOffChain; eauto.
        }
        {
          inversion H3; subst; clear H3;
          subst_ist s; subst_ist t;
          simpl in *; eauto.
        }
        {
          inversion H3; subst; clear H3;
          subst_ist s; subst_ist t;
          simpl in *; eauto.
          destruct H_alloc as [? [? ?]].
          congruence.
        }
      }
    Qed.

    Lemma psuh_alloc_post_stable (i : Name T) v old new:
      SStable (Rely i) (fun s x =>
          ReadyWaiting i (WFPush v) s x /\
          location_owned i s new /\
          on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) old None /\
          (* off_chain_aux (eval_heap (memSt s)) new (eval_cas (casSt s)) None /\
          off_chain_aux (eval_heap (memSt s)) new old None /\ *)
          exists vs, list_seg (eval_heap (memSt s)) old None vs).
    Proof.
      begin_stable.
      remember (fun s x => ReadyWaiting i (WFPush v) s x /\
          location_owned i s new /\
          on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) old None /\
          (* off_chain_aux (eval_heap (memSt s)) new (eval_cas (casSt s)) None /\
          off_chain_aux (eval_heap (memSt s)) new old None /\ *)
          exists vs, list_seg (eval_heap (memSt s)) old None vs) as P.
      replace (ReadyWaiting i (WFPush v) s ρ /\
      location_owned i s new /\
      on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) old None /\
      (exists vs : list A, list_seg (eval_heap (memSt s)) old None vs))
      with (P s ρ); [|subst; auto].
      eapply SRTC_stable; subst; eauto.
      eauto.
      clear. intros; simpl in *.
      destruct H0 as [j [? ?]].
      destruct H.
      rewrite and_comm.
      rewrite and_assoc.
      split.
      {
        destruct H2 as [[[? [? ?]] ?] [? ?]].
        destruct H as [[[?]]].
        inversion H1; subst; clear H1;
        try (now forward_istep_cas);
        try (now forward_istep_mem);
        unfold location_owned, location_allocated in *;
        try solve_inv_ret.
        {
          forward_istep_mem.
          inversion H2; subst x0.
          split.
          - eexists; split; eauto.
            unfold heap_update.
            destruct (PeanoNat.Nat.eqb l new); auto.
            congruence.
          - assert (new <> l) by congruence.
            rewrite HeapUpdateOther; auto.
        }
        {
          forward_istep_mem.
          specialize (write_excl0 _ _ _ _ _ eq_refl).
          congruence.
        }
        {
          forward_istep_mem.
          inversion H10; subst x; clear H10.
          inversion H2; subst x0; clear H2.
          assert (new <> new0) by congruence.
          rewrite HeapUpdateOther; auto.
          split; auto.
          eexists; split; eauto.
          rewrite HeapUpdateOther; auto.
        }
        {
          forward_istep_mem.
        }
      }
      {
        rewrite and_comm.
        destruct H2 as [? [? ?]].
        eapply get_post_stable with (vs0:=[]).
        psplit; eauto.
        econstructor; eauto.
        constructor.
      }
    Qed.

    Lemma push_write_post_stable (i : Name T) v old new:
      SStable (Rely i) (fun s x =>
          ReadyWaiting i (WFPush v) s x /\
          (exists h, (eval_heap (memSt s)) = Some h /\ h new = Some (v, old)) /\
          (eval_loc (memSt s) new = Some LWritten) /\
          on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) old None /\
          exists vs, list_seg (eval_heap (memSt s)) old None vs).
    Proof.
      begin_stable.
      remember (fun s x =>
        ReadyWaiting i (WFPush v) s x /\
        (exists h, (eval_heap (memSt s)) = Some h /\ h new = Some (v, old)) /\
        (eval_loc (memSt s) new = Some LWritten) /\
        on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) old None /\
        exists vs, list_seg (eval_heap (memSt s)) old None vs) as P.
      replace (ReadyWaiting i (WFPush v) s ρ /\
      (exists h : Heap, eval_heap (memSt s) = Some h /\ h new = Some (v, old)) /\
      eval_loc (memSt s) new = Some LWritten /\
      on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) old None /\
      (exists vs : list A, list_seg (eval_heap (memSt s)) old None vs))
      with (P s ρ); [|subst; auto].
      eapply SRTC_stable;
      subst; eauto.
      2:{ split; auto. repeat split; eauto. }
      clear. intros; simpl in *.
      destruct H0 as [j [? ?]].
      assert (
        ((exists h : Heap, eval_heap (memSt t) = Some h /\ h new = Some (v, old)) /\
        eval_loc (memSt t) new = Some LWritten) /\
        ReadyWaiting i (WFPush v) t y /\
        on_chain_written_aux (eval_heap (memSt t)) (eval_loc (memSt t)) old None /\
        (exists vs : list A, list_seg (eval_heap (memSt t)) old None vs)
        ->
        (ReadyWaiting i (WFPush v) t y /\
        (exists h : Heap, eval_heap (memSt t) = Some h /\ h new = Some (v, old)) /\
        eval_loc (memSt t) new = Some LWritten /\
        on_chain_written_aux (eval_heap (memSt t)) (eval_loc (memSt t)) old None /\
        (exists vs : list A, list_seg (eval_heap (memSt t)) old None vs))
      ) as Htmp by tauto.
      apply Htmp; clear Htmp.
      split.
      {
        destruct H as [[[[?]]] [[? [? ?]] [? [? [? ?]]]]].
        inversion H1; subst; clear H1;
        try (now forward_istep_cas);
        try (now forward_istep_mem);
        unfold location_owned, location_allocated in *;
        try solve_inv_ret.
        {
          forward_istep_mem.
          inversion H; subst x0.
          assert (l <> new) by congruence.
          rewrite HeapUpdateOther; auto.
          split; auto.
          eexists; split; eauto.
          rewrite HeapUpdateOther; auto.
        }
        {
          forward_istep_mem.
          specialize (write_excl0 _ _ _ _ _ eq_refl).
          congruence.
        }
        {
          forward_istep_mem.
          inversion H; subst x0.
          inversion H10; subst x.
          assert (new <> new0) by congruence.
          split; [eexists; split; eauto|];
          rewrite HeapUpdateOther; auto.
        }
        {
          forward_istep_mem.
        }
      }
      {
        destruct H as (? & ? & ? & ?).
        eapply get_post_stable with (vs0:=[]).
        psplit; eauto.
        econstructor; eauto.
        constructor.
      }
    Qed.

    Lemma pop_read_post_stable (i : Name T) v next old:
      SStable (Rely i) (fun s x =>
          ReadyWaiting i WFPop s x /\
          on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) (Some old) None /\
          (exists h, (eval_heap (memSt s)) = Some h /\ h old = Some (v, next)) /\
          exists vs, list_seg (eval_heap (memSt s)) (Some old) None (v :: vs)).
    Proof.
      begin_stable.
      remember (fun s ρ =>
        ReadyWaiting i WFPop s ρ /\
        on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) (Some old) None /\
        (exists h : Heap, eval_heap (memSt s) = Some h /\ h old = Some (v, next)) /\
        (exists vs : list A, list_seg (eval_heap (memSt s)) (Some old) None (v :: vs))) as P.
      replace (ReadyWaiting i WFPop s ρ /\
      on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) (Some old) None /\
      (exists h : Heap, eval_heap (memSt s) = Some h /\ h old = Some (v, next)) /\
      (exists vs : list A, list_seg (eval_heap (memSt s)) (Some old) None (v :: vs)))
      with (P s ρ); [|subst; auto].
      eapply SRTC_stable;
      subst; eauto.
      2:{ split; auto. repeat split; eauto. }
      clear. intros; simpl in *.
      destruct H0 as [j [? ?]].
      rewrite and_comm.
      rewrite and_assoc.
      rewrite and_comm.
      rewrite and_assoc.
      rewrite and_assoc.
      split.
      {
        destruct H as [? [? [? ?]]].
        inversion H1; subst; clear H1;
        try (forward_istep_mem);
        try (forward_istep_cas);
        try (solve_inv_ret).
        {
          eexists; split; eauto.
          inversion H3; subst x0.
          assert (l <> old) by congruence.
          rewrite HeapUpdateOther; auto.
        }
        {
          destruct H as [[[?]]].
          destruct H_owned as [_ ?].
          subst_ist s.
          specialize (write_excl0 _ _ _ _ _ eq_refl).
          congruence.
        }
        {
          destruct H_owned as [[? [? ?]] _].
          subst_ist s.
          congruence.
        }
        {
          destruct H_owned as [_ ?].
          inversion H2; subst.
          inversion H11; inversion H13; subst h0 l.
          subst_ist s.
          assert (new <> old) by congruence.
          eexists; split; eauto.
          rewrite HeapUpdateOther; auto.
          inversion H3; auto.
        }
        {
          destruct H_alloc as [? [?]].
          subst_ist s. congruence.
        }
      }
      {
        rewrite and_comm.
        rewrite and_assoc.
        destruct H as [? [? [? ?]]].
        eapply get_post_stable with (vs0:=[v]); simpl.
        psplit; eauto.
        econstructor; eauto.
        constructor.
      }
    Qed.

    Lemma stepCall {E E' A' B} {m : E' A'} {k : A' -> Prog E B} `{SigCoercion E' E} : (x <- call m; k x) = Vis (coerceOp _ m) k.
    Proof.
      rewrite frobProgId at 1. cbn.
      f_equal. extensionality x.
      rewrite frobProgId at 1. simpl.
      apply foldProg.
    Qed.

    Ltac begin_commit :=
      unfold Commit, LiftSPrec; intros.

    Lemma eq_inj {A'} :
      forall x y : A',
      eq x = eq y ->
      x = y.
    intros. now rewrite H.
    Qed.

    Ltac eq_inj:=
      match goal with
      | H:eq _ = eq _ |- _ =>
        apply eq_inj in H
      end.

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
          unfold on_chain_written in *; subst_ist s; now rewrite H in *.
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
    eapply SafeVis with
      (QI:=fun _ _ => LiftSPrec (ReadyWaiting i (WFPush v)))
      (QR:=fun old _ _ => LiftSPrec (fun s x =>
          ReadyWaiting i (WFPush v) s x /\
          on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) old None /\
          exists vs, list_seg (eval_heap (memSt s)) old None vs
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
      eapply get_post_stable with (vs0:=[]).
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
        - inversion H2; subst.
          now forward_istep_cas_aux s t.
        - now setoid_rewrite <- H6.
        - inversion H2; subst.
          forward_istep_cas_aux s t.
          now subst_ist s.
      }
      {
        exists x. split. easy. eq_inj; subst.
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
        split;[|split].
        {
          constructor; [repeat constructor|auto].
          - inversion H2; subst.
            now forward_istep_cas_aux s t.
          - unfold wfs_idle in *. eauto.
          - now setoid_rewrite <- H7.
          - unfold on_chain_written in *.
            inversion H2; subst.
            now forward_istep_cas_aux s t.
        }
        {
          unfold on_chain_written in *.
          inversion H2; subst.
          forward_istep_cas_aux s t.
          now ddestruct H10.
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
        exists x3. split. easy. eq_inj; subst.
        eapply StkGetRetId with (i:=i).
        constructor.
        - constructor; simpl; eauto.
          now apply differ_pointwise_comm.
        - constructor; auto.
      }
    }

    (* step malloc call *)
    rewrite stepCall.
    eapply SafeVis with
      (QI:=fun _ _ => LiftSPrec (fun s x =>
          ReadyWaiting i (WFPush v) s x /\
          on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) old None /\
          exists vs, list_seg (eval_heap (memSt s)) old None vs
        ))
      (QR:=fun new _ _ => LiftSPrec (fun s x =>
          ReadyWaiting i (WFPush v) s x /\
          location_owned i s new /\
          on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) old None /\
          (* off_chain_aux (eval_heap (memSt s)) new (eval_cas (casSt s)) None /\
          off_chain_aux (eval_heap (memSt s)) new old None /\ *)
          exists vs, list_seg (eval_heap (memSt s)) old None vs
        )).
    (* QI stable *)
    {
      begin_stable.
      specialize (H0 x1 eq_refl) as [? [? ?]].
      eexists; split; eauto.
      eapply get_post_stable with (vs0:=[]).
      psplit; eauto.
    }
    (* QR stable *)
    {
      begin_stable.
      specialize (H0 x1 eq_refl) as [? [? ?]].
      eexists; split; eauto.
      apply psuh_alloc_post_stable.
      psplit; eauto.
    }
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
          unfold on_chain_written in *.
          subst_ist s; subst_ist t;
          simpl in *; auto.
        }
        {
          inversion H2; subst; forward_istep_mem_aux s t.
        }
      }
      {
        exists x5. split. easy. eq_inj; subst.
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
        split.
        {
          constructor; [repeat constructor|auto];
          unfold on_chain_written in *;
          inversion H2; subst; forward_istep_mem_aux s t.
          - eapply ListSegFrame; eauto.
          - eapply OCWAlloc; eauto.
        }
        split.
        {
          inversion H2; subst; forward_istep_mem_aux s t.
          ddestruct H16.
          constructor; subst_ist t; simpl;
          [|apply HeapUpdateSelf].
          exists (heap_update new v0 h).
          split; auto.
          rewrite HeapUpdateSelf; congruence.
        }
        split.
        {
          inversion H2; subst; forward_istep_mem_aux s t.
          eapply OCWAlloc; eauto.
        }
        {
          inversion H2; subst; forward_istep_mem_aux s t.
          eapply ListSegFrame in H6; eauto.
        }
      }
      {
        exists x4. split. easy. eq_inj; subst.
        eapply StkAllocRet with (i:=i).
        constructor.
        - constructor; simpl; eauto.
          now apply differ_pointwise_comm.
        - constructor; auto.
      }
    }

    (* step write call *)
    rewrite stepCall.
    eapply SafeVis with
      (QI:=fun _ _ => LiftSPrec (fun s x =>
          ReadyWaiting i (WFPush v) s x /\
          location_owned i s new /\
          on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) old None /\
          exists vs, list_seg (eval_heap (memSt s)) old None vs
        ))
      (QR:=fun _ _ _ => LiftSPrec (fun s x =>
          ReadyWaiting i (WFPush v) s x /\
          (exists h, (eval_heap (memSt s)) = Some h /\ h new = Some (v, old)) /\
          (eval_loc (memSt s) new = Some LWritten) /\
          on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) old None /\
          exists vs, list_seg (eval_heap (memSt s)) old None vs
          (* /\
          list_seg (eval_heap (memSt s)) (Some new) None (v :: vs) *)
        )).
    (* QI stable *)
    {
      begin_stable.
      specialize (H0 x1 eq_refl) as [? [? ?]].
      eexists; split; eauto.
      apply psuh_alloc_post_stable.
      psplit; eauto.
    }
    (* QR stable *)
    {
      begin_stable.
      specialize (H0 x1 eq_refl) as [? [? ?]].
      eexists; split; eauto.
      apply push_write_post_stable.
      psplit; eauto.
      split; eauto.
      repeat split; eauto.
    }
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
          split.
          {
            constructor; [repeat constructor|auto];
            subst_ist s; subst_ist t; auto.
            inversion_clear 1.
            destruct H6 as [_ ?].
            subst_ist s.
            now inversion_clear H5.
          }
          split.
          {
            destruct H6 as [[? [? ?]] ?].
            subst_ist s; subst_ist t.
            inversion H5; subst x2.
            split; eauto.
          }
          {
            eexists; eauto.
          }
        }
        {
          exfalso.
          destruct H6 as [_ ?].
          subst_ist s; subst_ist t; simpl in *.
          (* inversion H6; subst x2. *)
          specialize write_excl0 with (1:=eq_refl).
          congruence.
        }
      }
      {
        exists x6. split. easy. eq_inj; subst.
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
            eapply OwnedOffChain; eauto.
          - inversion 1.
          - eapply OWCWrite; eauto.
        }
        {
          eexists; split; eauto.
          apply HeapUpdateSelf.
        }
        split.
        {
          apply HeapUpdateSelf.
        }
        split.
        {
          eapply OWCWrite; eauto.
        }
        {
          eapply ListSegUpdateOffChain in H7; eauto.
          eapply OwnedOffChain; eauto.
        }
      }
      {
        exists x4. split. easy. eq_inj; subst.
        eapply StkWriteRet with (i:=i) (data:=(v, old)); eauto.
        constructor.
        + constructor; simpl; eauto.
          now apply differ_pointwise_comm.
        + constructor; auto.
      }
    }

    (* step cas call *)
    rewrite stepCall.
    eapply SafeVis with
      (QI:=fun _ _ => LiftSPrec (fun s x =>
          ReadyWaiting i (WFPush v) s x /\
          (exists h, (eval_heap (memSt s)) = Some h /\ h new = Some (v, old)) /\
          (eval_loc (memSt s) new = Some LWritten) /\
          on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) old None /\
          exists vs, list_seg (eval_heap (memSt s)) old None vs
        ))
      (QR:=fun r _ _ => 
          if r : bool
          then LiftSPrec (ReadyDone i (WFPush v) (PASS tt))
          else LiftSPrec (ReadyDone i (WFPush v) FAIL)).
    (* QI stable *)
    {
      begin_stable.
      specialize (H0 x1 eq_refl) as [? [? ?]].
      eexists; split; eauto.
      apply push_write_post_stable.
      psplit; eauto.
      split; eauto.
      repeat split; eauto.
    }
    (* QR stable *)
    { 
      begin_stable.
      destruct v0;
      destruct H as [? [Heq ?]];
      specialize (H0 x1 Heq) as [? [? ?]];
      eexists; split; eauto;
      eapply ready_done_stable;
      psplit; eauto.
    }
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
        exists x6. split. easy. eq_inj; subst.
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
      ddestruct H38; psimpl.
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
          - subst_ist s; subst_ist t.
            simpl in *.
            econstructor; eauto.
        }
        (* guarantee *)
        {
          exists (comRetPoss i
          (comInvPoss i (MkPoss T (F A) VF (WFSsIdle vs) PCalls PRets) 
             (WFPush v) (WFSsPend i vs (WFPush v))) (WFPush v) (WFSsIdle (v :: vs)) 
          (PASS tt)).
          split. easy. eq_inj; subst.
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
          split. easy. eq_inj; subst.
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
  Qed.

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
          unfold on_chain_written in *; subst_ist s; now rewrite H in *.
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
    eapply SafeVis with
      (QI:=fun _ _ => LiftSPrec (ReadyWaiting i WFPop))
      (QR:=fun old _ _ => LiftSPrec (fun s x =>
          match old with
          | Some _ =>
            ReadyWaiting i WFPop s x /\
            on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) old None /\
            exists vs, list_seg (eval_heap (memSt s)) old None vs
          | None =>
            ReadyDone i WFPop (PASS None) s x
          end
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
      destruct v.
      - specialize (H0 x1 eq_refl) as [? [? ?]].
        eexists; split; eauto.
        eapply get_post_stable with (vs0:=[]).
        psplit; eauto.
      - specialize (H0 x1 eq_refl) as [? [? ?]].
        eexists; split; eauto.
        eapply ready_done_stable.
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
        constructor; [repeat constructor|auto]; auto.
        - inversion H2; subst.
          now forward_istep_cas_aux s t.
        - now setoid_rewrite <- H6.
        - inversion H2; subst.
          forward_istep_cas_aux s t.
          now subst_ist s.
      }
      {
        exists x. split. easy. eq_inj; subst.
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
          exists x3. split. easy. eq_inj; subst.
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
          - subst_ist s; subst_ist t; auto.
        }
        (* guarantee *)
        {
          exists (comRetPoss i
          (comInvPoss i (MkPoss T (F A) VF (WFSsIdle []) PCalls PRets) WFPop
             (WFSsPend i [] WFPop)) WFPop (WFSsIdle []) (PASS None)).
          split. easy. eq_inj; subst.
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
    eapply SafeVis with
      (QI:=fun _ _ => LiftSPrec (fun s x =>
          ReadyWaiting i WFPop s x /\
            on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) (Some old) None /\
            exists vs, list_seg (eval_heap (memSt s)) (Some old) None vs))
      (QR:=fun r _ _ => LiftSPrec (fun s x =>
          match r with (v, next) =>
          ReadyWaiting i WFPop s x /\
          on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) (Some old) None /\
          (exists h, (eval_heap (memSt s)) = Some h /\ h old = Some (v, next)) /\
          exists vs, list_seg (eval_heap (memSt s)) (Some old) None (v :: vs)
          end
        )).
    (* QI stable *)
    {
      begin_stable.
      specialize (H0 x1 eq_refl) as [? [? ?]].
      eexists; split; eauto.
      eapply get_post_stable with (vs0:=[]).
      psplit; eauto.
    }
    (* QR stable *)
    {
      begin_stable.
      destruct v.
      specialize (H0 x1 eq_refl) as [? [? ?]].
      eexists; split; eauto.
      eapply pop_read_post_stable.
      psplit; eauto.
    }
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
        exists x5. split. easy. eq_inj; subst.
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
        split; auto.
        {
          ddestruct H17.
          inversion H6; subst.
          inversion H14; subst l.
          inversion H16; subst h0.
          rewrite H15 in H17; inversion H17; subst.
          eauto.
        }
      }
      {
        exists x4. split. easy. eq_inj; subst.
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
    eapply SafeVis with
      (QI:=fun _ _ => LiftSPrec (fun s x =>
          ReadyWaiting i WFPop s x /\
          on_chain_written_aux (eval_heap (memSt s)) (eval_loc (memSt s)) (Some old) None /\
          (exists h, (eval_heap (memSt s)) = Some h /\ h old = Some (v, next)) /\
          exists vs, list_seg (eval_heap (memSt s)) (Some old) None (v :: vs)
        ))
      (QR:=fun b _ _ => LiftSPrec (fun s x =>
          if b : bool
          then ReadyDone i WFPop (PASS (Some v)) s x
          else ReadyDone i WFPop FAIL s x
        )).
    (* QI stable *)
    {
      begin_stable.
      specialize (H0 x1 eq_refl) as [? [? ?]].
      eexists; split; eauto.
      eapply pop_read_post_stable.
      psplit; eauto.
      do 2 (split; eauto).
    }
    (* QR stable *)
    { 
      begin_stable.
      destruct v0;
      specialize (H0 x1 eq_refl) as [? [? ?]];
      eexists; split; eauto;
      eapply ready_done_stable;
      psplit; eauto.
    }
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
        do 2 (split; eauto).
        do 2 constructor;
        try now subst_ist s; subst_ist t.
      }
      {
        exists x6. split. easy. eq_inj; subst.
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
      ddestruct H28; psimpl.
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
            inversion H25; subst l.
            rewrite H6 in H26; inversion H26; subst x6.
            rewrite H8 in H30; inversion H30; subst l2.
            auto.
          - unfold wfs_idle in *; psimpl; eauto.
          - subst_ist s; subst_ist t; auto.
          - subst_ist s; subst_ist t; auto.
            inversion ocw0; subst.
            rewrite H6 in H7; inversion H7; subst x6.
            inversion H20; subst.
            rewrite H25 in H8; inversion H8; subst; auto.
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
          split. easy. eq_inj; subst.
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
          split. easy. eq_inj; subst.
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
  Qed.

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
      {
        unfold on_chain_written in *.
        subst_ist s.
        rewrite H4 in *; auto.
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
        intros. eq_inj; subst.
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