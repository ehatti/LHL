From LHL.Core Require Import
  Program
  Specs
  Logic
  LogicFacts
  Tensor
  Traces
  SingConds
  VisPoss
  UBLayer
  ProgramRules
  Linearizability.

From LHL.Util Require Import
  TransUtil
  Tactics
  Util.

From LHL.Examples Require Import
  AtomicSpec
  LockSpec.

From Coq Require Import
  Logic.FunctionalExtensionality
  Lists.List
  Unicode.Utf8.
Import ListNotations.

Module Type LOCK_AROUND_PARAMS.
  Parameter T : nat.
  Parameter U : ESig.
  Parameter V : AtomicSpec T U.
End LOCK_AROUND_PARAMS.

Module Lock_Around(Import Params : LOCK_AROUND_PARAMS).

Definition E := LockSig |+| U.
Definition F := U.

Definition LAImpl : Impl E F :=
  λ _ m,
    call Acq;;
    v <- call m;
    call Rel;;
    ret v.

Definition VE : Spec T E :=
  lockSpec ⊗ LiftRacy V.
Definition VF : Spec T F :=
  LiftAtomic V.

Notation lockSt s := (LState (snd s)).
Notation racySt s := (RState (snd s)).

Record Inv (i : Name T)
  (s : InterState F VE) (ρ : Poss VF)
:= {
  undl_cons :
    (racySt s).(racy_val) = Some ρ.(PState).(atom_val);
  undl_wait :
    ρ.(PState).(atom_pend) = None;
  lock_defn :
    (lockSt s).(lock_owner) ≠ None;
  racy_defn :
    (racySt s).(racy_val) ≠ None;
  resp_owns :
    (lockSt s).(lock_owner) ∈ [Some (Some i), Some None] ->
    ¬∃ j R (m : U R),
      i ≠ j /\
      (j, existT U R m) ∈ (racySt s).(racy_pend)
}.

Record Rely (i : Name T)
  (s : InterState F VE) (ρ : Poss VF)
  (t : InterState F VE) (σ : Poss VF)
:= {
  pres_inv :
    Inv i s ρ ->
    Inv i t σ;
  pres_call :
    PCalls ρ i = PCalls σ i;
  pres_ret :
    PRets ρ i = PRets σ i;
  pres_own :
    (lockSt s).(lock_owner) = Some (Some i) ->
    lockSt s = lockSt t;
  pres_nown :
    (lockSt s).(lock_owner) ≠ Some (Some i) ->
    (lockSt t).(lock_owner) ≠ Some (Some i);
  pres_pend :
    ¬(∃ R m, (i, existT _ R m) ∈ racy_pend (racySt s)) ->
    ¬(∃ R m, (i, existT _ R m) ∈ racy_pend (racySt t))
}.

Definition Guar i : SRelt VE VF :=
  λ s ρ t σ,
    ∀ j, i ≠ j ->
      Rely j s ρ t σ.

Lemma eq_inj {A} :
  forall x y : A,
  eq x = eq y ->
  x = y.
Proof.
  intros.
  now rewrite H.
Qed.

Lemma eq_sing {A} :
  forall (x : A) (P : A -> Prop),
  P = eq x ->
  P x.
Proof.
  intros. now rewrite H.
Qed.

Lemma Invoke_pres_single {R} :
  forall (m : F R) i s ρ t σs,
  TInvoke (VE:= VE) (VF:= VF) LAImpl i R m s (eq ρ) t σs ->
  σs = eq (invPoss i ρ m).
intros.
unfold TInvoke in H. psimpl.
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

Definition Precs (i : Name T) {R} (m : F R) : SPrec VE VF :=
  (λ (s : InterState F VE) ρ,
        (lockSt s).(lock_owner) ≠ Some (Some i) /\
        Inv i s ρ).

Definition Posts (i : Name T) {R} (m : F R) : Post VE VF R :=
  (λ v _ _, LiftSPrec (λ (s : InterState F VE) ρ,
        (lockSt s).(lock_owner) ≠ Some (Some i) /\
        PCalls ρ i = CallDone m /\
        PRets ρ i = RetPoss m v /\
        Inv i s ρ)).

Lemma liftCorrect :
  ∀ (i : Name T) (A : Type) (m : F A),
    VerifyProg i (LiftSRelt (Rely i)) (LiftSRelt (Guar i))
      (prComp (LiftSPrec (Precs i m)) (TInvoke LAImpl i A m) ->> LiftSRelt (Rely i))
      (LAImpl A m)
      (Posts i m).
Proof.
  intros.
  eapply weakenPrec with
    (P:=λ _ _, LiftSPrec (λ (s : InterState F VE) ρ,
      (lockSt s).(lock_owner) ≠ Some (Some i) /\
      PCalls ρ i = CallPoss m /\
      PRets ρ i = RetIdle /\
      Inv i s ρ)).
  2:{
    unfold sub, subRelt, LiftSPrec, LiftSRelt, Precs.
    intros. psimpl. assert (H1' := H1).
    apply Invoke_pres_single in H1'. psimpl.
    specialize (H0 (invPoss i x1 m) eq_refl).
    psimpl. unfold TInvoke in H1. psimpl.
    clear H5. eexists. split. easy. destruct H0.
    split.
    { apply pres_nown0. now rewrite <- H4 at 1. }
    unfold invPoss in *. cbn in *.
    rewrite eqb_id in *.
    split.
    { easy. }
    split.
    { easy. }
    {
      destruct H3.
      apply pres_inv0.
      constructor; cbn;
      try setoid_rewrite <- H4.
      all: easy.
    }
  }
  unfold LAImpl.
  eapply lemBind.
  {
    eapply (lemCall
      (Q:=λ _ _, LiftSPrec (λ (s : InterState F VE) ρ,
        (lockSt s).(lock_owner) = Some (Some i) /\
        PCalls ρ i = CallPoss m /\
        PRets ρ i = RetIdle /\
        Inv i s ρ))
      (S:=λ _ _ _, LiftSPrec (λ (s : InterState F VE) ρ,
        (lockSt s).(lock_owner) = Some (Some i) /\
        PCalls ρ i = CallPoss m /\
        PRets ρ i = RetIdle /\
        Inv i s ρ))).
    {
      unfold
        Stable, stableRelt,
        sub, subRelt,
        LiftSPrec, LiftSRelt.
      intros. psimpl.
      specialize (H0 x1 eq_refl). psimpl.
      destruct H0. eexists. split. easy.
      split.
      { now rewrite <- pres_own0 at 1. }
      split.
      { now rewrite <- pres_call0. }
      split.
      { now rewrite <- pres_ret0. }
      { now apply pres_inv0. }
    }
    {
      unfold
        Stable, stablePost, stableRelt,
        sub, subRelt,
        LiftSPrec, LiftSRelt.
      intros. psimpl.
      specialize (H0 x1 eq_refl). psimpl.
      destruct H0. eexists. split. easy.
      split.
      { now rewrite <- pres_own0 at 1. }
      split.
      { now rewrite <- pres_call0. }
      split.
      { now rewrite <- pres_ret0. }
      { now apply pres_inv0. }
    }
    {
      unfold Commit, LiftSPrec, LiftSRelt.
      intros. psimpl. psimpl.
      exists (eq x1).
      split.
      { repeat econstructor. }
      split.
      {
        intros. subst.
        repeat econstructor.
      }
      ddestruct H.
      2:{
        exfalso.
        now rewrite <- x2 in H3 at 1.
      }
      2:{
        exfalso.
        eapply H6.(lock_defn _ _ _).
        now rewrite <- x2 at 1.
      }
      split.
      {
        eexists.
        split. easy.
        split. now rewrite <- x at 1.
        split. easy.
        split. easy.
        constructor.
        { rewrite <- H9 at 1. apply H6. }
        { apply H6. }
        { now rewrite <- x at 1. }
        { rewrite <- H9 at 1. apply H6. }
        {
          intros.
          setoid_rewrite <- H9.
          apply H6.
          rewrite <- x2 at 1.
          rewrite insert_perm.
          apply contains_triv.
        }
      }
      {
        intros. apply eq_inj in H.
        subst. eexists. split. easy.
        unfold Guar. intros.
        constructor.
        {
          intros. destruct H10.
          constructor.
          { rewrite <- H9 at 1. apply H6. }
          { apply H6. }
          { now rewrite <- x at 1. }
          { now rewrite <- H9 at 1. }
          {
          intros.
          setoid_rewrite <- H9.
          apply resp_owns0.
          rewrite <- x2 at 1.
          rewrite insert_perm.
          apply contains_triv.
        }
        }
        { easy. }
        { easy. }
        { now rewrite <- x2 at 1. }
        {
          rewrite <- x at 1.
          cbn. intros.
          unfold not. intros.
          now ddestruct H11.
        }
        { now setoid_rewrite H9 at 1. }
      }
    }
    intros [].
    {
      unfold Commit, LiftSPrec, LiftSRelt.
      intros. psimpl. psimpl.
      exists (eq x3).
      split.
      { repeat econstructor. }
      split.
      {
        intros. subst.
        repeat econstructor.
      }
      ddestruct H.
      2:{
        exfalso.
        eapply H7.(lock_defn _ _ _).
        now rewrite <- x5 at 1.
      }
      split.
      {
        eexists.
        split. easy.
        split. now rewrite <- x at 1.
        split. easy.
        split. easy.
        constructor.
        { rewrite <- H13 at 1. apply H7. }
        { apply H7. }
        { now rewrite <- x at 1. }
        { rewrite <- H13 at 1. apply H7. }
        {
          intros.
          setoid_rewrite <- H13.
          apply H7.
          rewrite <- x5 at 1.
          apply contains_triv.
        }
      }
      {
        intros. apply eq_inj in H.
        subst. eexists. split. easy.
        unfold Guar. intros.
        constructor.
        {
          intros. destruct H14.
          constructor.
          { rewrite <- H13 at 1. apply H7. }
          { apply H7. }
          { now rewrite <- x at 1. }
          { now rewrite <- H13 at 1. }
          {
            intros. cbn in *.
            rewrite <- x in H14 at 1.
            destruct H14; cbn in *.
            { now ddestruct H14. }
            destruct H14.
            { now ddestruct H14. }
            { easy. }
          }
        }
        { easy. }
        { easy. }
        {
          rewrite <- x5 at 1.
          intros. now ddestruct H14.
        }
        {
          rewrite <- x at 1.
          cbn. intros.
          unfold not. intros.
          now ddestruct H15.
        }
        { now setoid_rewrite H13 at 1. }
      }
    }
  }
  intros [].
  rewrite <- reltCompAssoc.
  apply lemForget.
  eapply lemBind.
  {
    eapply (lemCall
      (Q:=λ _ _, LiftSPrec (λ (s : InterState F VE) ρ,
        (lockSt s).(lock_owner) = Some (Some i) /\
        PCalls ρ i = CallPoss m /\
        PRets ρ i = RetIdle /\
        Inv i s ρ))
      (S:=λ v _ _, LiftSPrec (λ (s : InterState F VE) ρ,
        (lockSt s).(lock_owner) = Some (Some i) /\
        (¬∃ R m, (i, existT _ R m) ∈ (racySt s).(racy_pend)) /\
        PCalls ρ i = CallDone m /\
        PRets ρ i = RetPoss m v /\
        Inv i s ρ))).
  {
      unfold
        Stable, stableRelt,
        sub, subRelt,
        LiftSPrec, LiftSRelt.
      intros. psimpl.
      specialize (H0 x1 eq_refl). psimpl.
      destruct H0. eexists. split. easy.
      split.
      { rewrite <- pres_own0 at 1. easy. now rewrite H1 at 1. }
      split.
      { now rewrite <- pres_call0. }
      split.
      { now rewrite <- pres_ret0. }
      { now apply pres_inv0. }
    }
    {
      unfold
        Stable, stablePost, stableRelt,
        sub, subRelt,
        LiftSPrec, LiftSRelt.
      intros. psimpl.
      specialize (H0 x1 eq_refl). psimpl.
      destruct H0. eexists. split. easy.
      split.
      { rewrite <- pres_own0 at 1. easy. now rewrite H1 at 1. }
      split.
      { now apply pres_pend0. }
      split.
      { now rewrite <- pres_call0. }
      split.
      { now rewrite <- pres_ret0. }
      { now apply pres_inv0. }
    }
    {
      unfold Commit, LiftSPrec, LiftSRelt.
      intros. psimpl. psimpl.
      exists (eq x3).
      split.
      { repeat econstructor. }
      split.
      {
        intros. subst.
        repeat econstructor.
      }
      ddestruct H.
      2:{
        exfalso.
        eapply H6.(resp_owns _ _ _).
        {
          rewrite H3 at 1.
          now left.
        }
        {
          exists i0, _, m1.
          split. easy.
          rewrite <- x1 at 1.
          now left.
        }
      }
      destruct H6.
      split.
      {
        eexists.
        split. easy.
        split. now rewrite <- H9 at 1.
        split. easy.
        split. easy.
        constructor.
        {
          rewrite <- x at 1.
          rewrite <- x1 in undl_cons0 at 1.
          easy.
        }
        { easy. }
        { now rewrite <- H9 at 1. }
        {
          rewrite <- x at 1.
          rewrite <- x1 in racy_defn0 at 1.
          easy.
        }
        {
          unfold not at 1. intros.
          psimpl. rewrite <- x in H10 at 1.
          cbn in *. destruct H10. 2: easy.
          now ddestruct H10.
        }
      }
      {
        intros. apply eq_inj in H.
        subst. eexists. split. easy.
        unfold Guar. intros.
        constructor.
        {
          intros. destruct H6.
          constructor.
          {
            rewrite <- x at 1.
            rewrite <- x1 in undl_cons0 at 1.
            easy.
          }
          { easy. }
          { now rewrite <- H9 at 1. }
          {
            rewrite <- x at 1.
            rewrite <- x1 in racy_defn0 at 1.
            easy.
          }
          {
            intros. exfalso.
            rewrite <- H9, H3 in H6 at 1.
            destruct H6.
            { now ddestruct H6. }
            destruct H6.
            { now ddestruct H6. }
            { easy. }
          }
        }
        { easy. }
        { easy. }
        { easy. }
        { now rewrite H9 at 1. }
        {
          setoid_rewrite <- x at 1.
          intros. unfold not. intros.
          psimpl. destruct H10;
          now ddestruct H10.
        }
      }
    }
    intros v.
    {
      unfold Commit, LiftSPrec, LiftSRelt.
      intros. psimpl. psimpl.
      assert (racy_val (racySt s) ≠ None).
      { apply H7. }
      ddestruct H.
      2: now rewrite <- x7 in H14 at 1.
      2: now rewrite <- x7 in H14 at 1.
      pose (p' :=
        comRetPoss i
          (comInvPoss i
            x3
            m
            (MkAtom s0 (Some (i, existT _ _ m))))
          m
          (MkAtom t0 None)
          v
      ).
      assert (
        VisPossSteps
          x3
          (([] ++ [(i, CallEv m)]) ++ [(i, RetEv m v)])
          p'
      ).
      {
        apply retStep.
        apply callStep.
        constructor.
        {
          destruct H7, x3, PState.
          cbn in *. subst.
          rewrite <- x7 in undl_cons0.
          cbn in *. ddestruct undl_cons0.
          repeat (easy || constructor).
        }
        {
          cbn. rewrite eqb_id.
          repeat (easy || constructor).
        }
      }
      exists (eq p').
      split.
      { repeat econstructor. }
      split.
      {
        intros. subst. eexists. split.
        easy. eapply erase_vis. exact H15.
      }
      split.
      {
        eexists. split. easy.
        split. now rewrite <- H13 at 1.
        split.
        {
          setoid_rewrite <- x at 1.
          unfold not. intros. now psimpl.
        }
        split. cbn. now rewrite eqb_id.
        split. cbn. now rewrite eqb_id.
        constructor.
        { cbn. now rewrite <- x at 1. }
        { easy. }
        { rewrite <- H13 at 1. apply H7. }
        { now rewrite <- x at 1. }
        {
          unfold not at 1.
          intros. psimpl.
          rewrite <- x in H18 at 1.
          cbn in *. easy.
        }
      }
      {
        intros. eexists. split. easy.
        unfold Guar. apply eq_inj in H16.
        intros. subst.
        constructor.
        {
          intros. destruct H16.
          constructor; cbn.
          { now rewrite <- x at 1. }
          { easy. }
          { now rewrite <- H13 at 1. }
          { now rewrite <- x at 1. }
          {
            unfold not at 1.
            intros. psimpl.
            rewrite <- x in H19 at 1.
            cbn in *. easy.
          }
        }
        { cbn. now rewrite eqb_nid. }
        { cbn. now rewrite eqb_nid. }
        { easy. }
        { now rewrite H13 at 1. }
        {
          intros.
          setoid_rewrite <- x at 1.
          unfold not. intros. now psimpl.
        }
      }
    }
  }
  intros v.
  apply lemForget.
  eapply lemBind.
  {
    eapply (lemCall
      (Q:=λ _ _, LiftSPrec (λ (s : InterState F VE) ρ,
        (lockSt s).(lock_owner) = Some (Some i) /\
        (¬∃ R m, (i, existT _ R m) ∈ (racySt s).(racy_pend)) /\
        PCalls ρ i = CallDone m /\
        PRets ρ i = RetPoss m v /\
        Inv i s ρ))
      (S:=λ _ _ _, LiftSPrec (λ (s : InterState F VE) ρ,
        (lockSt s).(lock_owner) ≠ Some (Some i) /\
        PCalls ρ i = CallDone m /\
        PRets ρ i = RetPoss m v /\
        Inv i s ρ))).
    {
      unfold
        Stable, stableRelt,
        sub, subRelt,
        LiftSPrec, LiftSRelt.
      intros. psimpl.
      specialize (H0 x1 eq_refl). psimpl.
      destruct H0. eexists. split. easy.
      split.
      { rewrite <- pres_own0 at 1. easy. now rewrite H1 at 1. }
      split.
      { now apply pres_pend0. }
      split.
      { now rewrite <- pres_call0. }
      split.
      { now rewrite <- pres_ret0. }
      { now apply pres_inv0. }
    }
    {
      unfold
        Stable, stablePost, stableRelt,
        sub, subRelt,
        LiftSPrec, LiftSRelt.
      intros. psimpl.
      specialize (H0 x1 eq_refl). psimpl.
      destruct H0. eexists. split. easy.
      split.
      { now apply pres_nown0. }
      split.
      { now rewrite <- pres_call0. }
      split.
      { now rewrite <- pres_ret0. }
      { now apply pres_inv0. }
    }
    {
      unfold Commit, LiftSPrec, LiftSRelt.
      intros. psimpl. psimpl.
      exists (eq x5).
      split.
      { repeat econstructor. }
      split.
      {
        intros. subst.
        repeat econstructor.
      }
      ddestruct H.
      2: now rewrite <- x7 in H4 at 1.
      2:{
        rewrite <- x7 in H4 at 1.
        cbn in *. now ddestruct H4.
      }
      2: now rewrite <- x7 in H4 at 1.
      destruct H8.
      split.
      {
        eexists.
        split. easy.
        split. now rewrite <- x at 1.
        split. now setoid_rewrite <- H14 at 1.
        split. easy.
        split. easy.
        constructor.
        { now rewrite <- H14 at 1. }
        { easy. }
        { now rewrite <- x at 1. }
        { now rewrite <- H14 at 1. }
        {
          intros.
          setoid_rewrite <- H14.
          apply resp_owns0.
          now left.
        }
      }
      {
        intros. apply eq_inj in H.
        subst. eexists. split. easy.
        unfold Guar. intros.
        constructor.
        {
          intros. destruct H8.
          constructor.
          { now rewrite <- H14 at 1. }
          { easy. }
          { now rewrite <- x at 1. }
          { now rewrite <- H14 at 1. }
          {
            intros. exfalso.
            rewrite <- x in H8 at 1.
            destruct H8.
            { now ddestruct H8. }
            destruct H8.
            { now ddestruct H8. }
            { easy. }
          }
        }
        { easy. }
        { easy. }
        {
          rewrite <- x7 at 1.
          intros. now ddestruct H8.
        }
        {
          intros. rewrite <- x at 1.
          unfold not. cbn. intros.
          now ddestruct H15.
        }
        { now setoid_rewrite H14 at 1. }
      }
    }
    intros [].
    {
      unfold Commit, LiftSPrec, LiftSRelt.
      intros. psimpl. psimpl.
      exists (eq x3).
      split.
      { repeat econstructor. }
      split.
      {
        intros. subst.
        repeat econstructor.
      }
      ddestruct H.
      2: now rewrite <- x7 in H4 at 1.
      destruct H8.
      split.
      {
        eexists.
        split. easy.
        split. now rewrite <- x at 1.
        split. easy.
        split. easy.
        constructor.
        { now rewrite <- H19 at 1. }
        { easy. }
        { now rewrite <- x at 1. }
        { now rewrite <- H19 at 1. }
        {
          intros.
          setoid_rewrite <- H19.
          apply resp_owns0.
          now left.
        }
      }
      {
        intros. apply eq_inj in H.
        subst. eexists. split. easy.
        unfold Guar. intros.
        constructor.
        {
          intros. destruct H8.
          constructor.
          { now rewrite <- H19 at 1. }
          { easy. }
          { now rewrite <- x at 1. }
          { now rewrite <- H19 at 1. }
          {
            intros.
            setoid_rewrite <- H19 at 1.
            assert (lock_owner (lockSt s) ∈ [Some (Some i), Some None]).
            {
              rewrite <- x7 at 1.
              now left.
            }
            apply resp_owns0 in H20.
            unfold not at 1. intros.
            apply H20. psimpl.
            dec_eq_nats x3 i.
            {
              exfalso. apply H5.
              now exists _, x12.
            }
            { now exists x3, _, x12. }
          }
        }
        { easy. }
        { easy. }
        {
          rewrite <- x7 at 1.
          intros. now ddestruct H8.
        }
        {
          intros. rewrite <- x at 1.
          unfold not. cbn. intros.
          now ddestruct H20.
        }
        { now setoid_rewrite H19 at 1. }
      }
    }
  }
  intros [].
  eapply lemRet.
  {
    unfold sub, subRelt.
    intros. now psimpl.
  }
Qed.

Theorem lockAroundCorrect :
  VerifyImpl VE VF
    (λ i, LiftSRelt (Rely i))
    (λ i, LiftSRelt (Guar i))
    (λ i _ m, LiftSPrec (Precs i m))
    LAImpl
    (λ i _ m, Posts i m)
    (λ i _ m _ _ _, LiftSPrec (Precs i m)).
Proof.
  constructor.
  {
    unfold LiftSRelt, LiftSPrec.
    intros. subst. eexists.
    split. easy. now constructor.
  }
  {
    unfold LiftSRelt, LiftSPrec.
    unfold sub, subRelt. intros. psimpl.
    specialize (H x eq_refl). psimpl.
    specialize (H1 x2 eq_refl). psimpl.
    eexists. split. easy.
    destruct H0, H1. constructor.
    { intros. tauto. }
    { now rewrite pres_call0. }
    { now rewrite pres_ret0. }
    {
      intros. assert (H' := H).
      apply pres_own0 in H.
      rewrite H in H'.
      apply pres_own1 in H'.
      now transitivity (lockSt x0).
    }
    { tauto. }
    { tauto. }
  }
  {
    unfold LiftSRelt, LiftSPrec.
    unfold sub, subRelt. intros. psimpl.
    specialize (H0 x eq_refl). psimpl.
    eexists. split. easy.
    now eapply H1.
  }
  {
    unfold InvokeAny, TInvoke, sub, subRelt, LiftSRelt.
    intros. psimpl. exists (invPoss i x x1).
    split.
    {
      set_ext y. unfold invPoss.
      split; intros; psimpl.
      {
        destruct x2, y. cbn in *.
        f_equal.
        { easy. }
        {
          extensionality k.
          dec_eq_nats i k.
          { now rewrite eqb_id. }
          { now rewrite eqb_nid, H7. }
        }
        {
          extensionality k.
          dec_eq_nats i k.
          { now rewrite eqb_id. }
          { now rewrite eqb_nid, H8. }
        }
      }
      {
        eexists. split. easy. cbn.
        rewrite eqb_id.
        repeat split; try easy.
        apply differ_pointwise_trivial.
        apply differ_pointwise_trivial.
      }
    }
    {
      constructor.
      {
        intros. destruct H1.
        unfold invPoss.
        constructor.
        { now rewrite <- H3 at 1. }
        { easy. }
        { now rewrite <- H3 at 1. }
        { now rewrite <- H3 at 1. }
        { now setoid_rewrite <- H3. }
      }
      { cbn. now rewrite eqb_nid. }
      { cbn. now rewrite eqb_nid. }
      { now setoid_rewrite H3. }
      { now setoid_rewrite H3. }
      { now setoid_rewrite H3. }
    }
  }
  {
    unfold ReturnAny, TReturn, sub, subRelt, LiftSRelt.
    intros. psimpl. exists (retPoss i x).
    split.
    {
      set_ext y. unfold retPoss.
      unfold mapRetPoss.
      split; intros; psimpl.
      {
        destruct x3, y. cbn in *.
        f_equal.
        { easy. }
        {
          extensionality k.
          dec_eq_nats i k.
          { now rewrite eqb_id. }
          { now rewrite eqb_nid, H8. }
        }
        {
          extensionality k.
          dec_eq_nats i k.
          { now rewrite eqb_id. }
          { now rewrite eqb_nid, H9. }
        }
      }
      {
        destruct H2. cbn in *.
        ddestruct H1. symmetry in x4.
        apply H0 in x4.
        specialize (x4 x3 eq_refl). psimpl.
        eexists. split. easy. cbn.
        rewrite eqb_id.
        repeat split; try easy.
        apply differ_pointwise_trivial.
        apply differ_pointwise_trivial.
      }
    }
    {
      constructor.
      {
        intros. destruct H1.
        unfold invPoss.
        constructor.
        { now rewrite <- H3 at 1. }
        { easy. }
        { now rewrite <- H3 at 1. }
        { now rewrite <- H3 at 1. }
        { now setoid_rewrite <- H3. }
      }
      { cbn. now rewrite eqb_nid. }
      { cbn. now rewrite eqb_nid. }
      { now setoid_rewrite H3. }
      { now setoid_rewrite H3. }
      { now setoid_rewrite H3. }
    }
  }
  {
    unfold LiftSRelt, LiftSPrec, Precs.
    intros. eexists.
    split. easy.
    split. easy.
    constructor.
    { easy. }
    { easy. }
    { easy. }
    { easy. }
    {
      cbn. unfold not. intros.
      psimpl. easy.
    }
  }
  {
    unfold
      Stable, stablePrec,
      sub, subPrec, Precs,
      LiftSPrec, LiftSRelt.
    intros. psimpl.
    specialize (H0 x1 eq_refl). psimpl.
    eexists. split. easy. destruct H0.
    split.
    { now apply pres_nown0. }
    { now apply pres_inv0. }
  }
  {
    unfold Posts, Precs, LiftSPrec, sub, subPrec.
    intros. psimpl. now eexists.
  }
  {
    intros.
    apply liftCorrect.
  }
  {
    unfold ReturnStep, Posts, LiftSPrec, LiftSRelt.
    intros. psimpl. clear H6.
    exists (eq x1).
    split.
    { repeat econstructor. }
    split.
    {
      intros. subst.
      repeat econstructor.
    }
    split.
    {
      intros. now subst.
    }
    split.
    {
      exists (retPoss i x1).
      split.
      {
        set_ext y. unfold retPoss.
        unfold mapRetPoss.
        split; intros; psimpl.
        {
          destruct x0, y. cbn in *.
          f_equal.
          { easy. }
          {
            extensionality k.
            dec_eq_nats i k.
            { now rewrite eqb_id. }
            { now rewrite eqb_nid, H9. }
          }
          {
            extensionality k.
            dec_eq_nats i k.
            { now rewrite eqb_id. }
            { now rewrite eqb_nid, H10. }
          }
        }
        {
          eexists. split. easy. cbn.
          rewrite eqb_id.
          repeat split; try easy.
          apply differ_pointwise_trivial.
          apply differ_pointwise_trivial.
        }
      }
      {
        split. easy.
        destruct H5.
        now constructor.
      }
    }
    {
      intros. apply eq_inj in H.
      subst. exists (retPoss i x0).
      split.
      {
        set_ext y. unfold retPoss.
        unfold mapRetPoss.
        split; intros; psimpl.
        {
          destruct x1, y. cbn in *.
          f_equal.
          { easy. }
          {
            extensionality k.
            dec_eq_nats i k.
            { now rewrite eqb_id. }
            { now rewrite eqb_nid, H9. }
          }
          {
            extensionality k.
            dec_eq_nats i k.
            { now rewrite eqb_id. }
            { now rewrite eqb_nid, H10. }
          }
        }
        {
          eexists. split. easy. cbn.
          rewrite eqb_id.
          repeat split; try easy.
          apply differ_pointwise_trivial.
          apply differ_pointwise_trivial.
        }
      }
      {
        unfold Guar. intros.
        constructor.
        {
          intros. destruct H1.
          now constructor.
        }
        { cbn. now rewrite eqb_nid. }
        { cbn. now rewrite eqb_nid. }
        { easy. }
        { easy. }
        { easy. }
      }
    }
  }
Qed.

End Lock_Around.