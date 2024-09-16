From LHL.Core Require Import
  Program
  ProgramRules
  Specs 
  Logic
  Tensor
  Traces
  Linearizability
  LogicPaco
  LogicFacts
  ProgramFacts
  UBLayer.

From LHL.Examples Require Import
  LockSpec
  CASSpec
  LocalVarSpec.

From LHL.Util Require Import
  Tactics
  TransUtil
  Util.

From Coq Require Import
  Logic.FunctionalExtensionality
  Logic.PropExtensionality
  Program.Equality.

From Paco Require Import paco.

Definition SpinLockAcq : Prog (CASSig bool) unit :=
  while (tmp <- call (CAS None (Some true)); ret (negb tmp)) skip.

Definition SpinLockRel: Prog (CASSig bool) unit :=
  call (CAS (Some true) None);;
  ret tt.

Definition SpinLockImpl: Impl (CASSig bool) LockSig :=
  fun _ m =>
    match m with
    | Acq => SpinLockAcq
    | Rel => SpinLockRel
    end.

Definition calcSilentPost {T E F} {VE : Spec T E} {VF : Spec T F} (G: Relt VE VF) (P: Prec VE VF) (i: Name T) :=
  fun s ρs t σs =>
    P s ρs /\ ρs = σs /\ snd s = snd t /\
    Util.differ_pointwise (fst s) (fst t) i /\
    UnderThreadStep (fst s i) None (fst t i) /\
    G s ρs t ρs.

Lemma calcSilentPostGuar {T E F} {VE : Spec T E} {VF : Spec T F} (G: Relt VE VF) (P: Prec VE VF) (i: Name T) :
  (forall s ths ρs tht,
  P (ths, s) ρs ->
  Util.differ_pointwise ths tht i ->
  UnderThreadStep (ths i) None (tht i) ->
  (calcSilentPost G P i) (ths, s) ρs (tht, s) ρs) ->
    SilentStep i G P (calcSilentPost G P i).
Proof.
  unfold SilentStep.
  unfold calcSilentPost.
  intros.
  specialize (H s ths ρs tht H0 H1 H2).
  easy.
Qed.

Lemma silentStepWeakenPre {T E F} {VE : Spec T E} {VF : Spec T F} (G Q: Relt VE VF) (P1 P2: Prec VE VF) (i: Name T) :
  P1 ==> P2 ->
  SilentStep i G P2 Q ->
  SilentStep i G P1 Q.
Proof.
  unfold SilentStep.
  intros.
  specialize (H _ _ H1).
  specialize (H0 s ths ρs tht H H2 H3).
  easy.
Qed.

Lemma silentStepWeakenPost {T E F} {VE : Spec T E} {VF : Spec T F} (G Q1 Q2: Relt VE VF) (P: Prec VE VF) (i: Name T) :
  Q1 ==> Q2 ->
  SilentStep i G P Q1 ->
  SilentStep i G P Q2.
Proof.
  unfold SilentStep.
  intros.
  specialize (H (ths, s) ρs (tht, s) ρs).
  specialize (H0 s ths ρs tht H1 H2 H3).
  destruct H0.
  specialize (H H0).
  easy.
Qed.

Lemma lemWhileSkip {T E F} {VE : Spec T E} {VF : Spec T F} {R G} {I : Post VE VF bool} {B : Prog E bool} {P} i :
  Stable R (calcSilentPost G (I true) i) ->
  SilentStep i G (I true) (calcSilentPost G (I true) i) ->
  (I true) ->> (calcSilentPost G (I true) i) ==> P ->
  VerifyProg i R G P B I ->
  VerifyProg i R G P (while B skip) (UnitRet (I false)).
Proof.
  unfold VerifyProg. 
  rewrite ! paco_eqv.
  intros H_stable H_silent H_inv HPB.
  cut (
    forall B' P',
    paco_safe i R G P' B' I ->
    paco_safe i R G P' (whileAux B skip B' skip) (UnitRet (I false))
  ).
  { intros. apply H. easy. }
  pcofix rec. intros. punfold H0. dependent destruction H0.
  { destruct v.
    { rewrite frobProgId at 1. cbn. pfold. econstructor. 
      { exact H_stable. }
      { eapply silentStepWeakenPre. 2: apply H_silent. 
        unfold ReltToPrec. unfold sub, subPrec.
        intros.
        destruct H0 as [s' [ρs' ?]].
        exists s', ρs'.
        specialize (H _ _ _ _ H0). 
        apply H.
      }
      { right. apply rec. rewrite <- paco_eqv.
        eapply weakenPrec.
        { unfold VerifyProg. rewrite paco_eqv. apply HPB. }
        { eapply subReltTrans.
          { eapply reltComposeMono1. apply H. }
          { apply H_inv. }
        }
      }
    }
    { rewrite frobProgId at 1. cbn. pfold. econstructor. unfold UnitRet. easy. }
  }
  { rewrite frobProgId at 1. cbn. pfold. econstructor.
    { apply H. }
    { apply H0. }
    { apply H1. }
    intros.
    specialize (H2 v). destruct_all.
    split; [easy |].
    right. apply rec.
    destruct H3. 2: inversion H3.
    easy. 
  }
  { rewrite frobProgId at 1. cbn. pfold. econstructor.
    { apply H. }
    { apply H0. }
    { right. apply rec. 
      destruct H1. 2: inversion H1.
      easy.
    }
  }
Qed.

Lemma stable_compose_R {T E F} {VE : Spec T E} {VF : Spec T F} (P R : Relt VE VF) :
  R ->> R ==> R ->
  Stable R (P ->> R).
Proof.
  unfold Stable, stableRelt.
  intros.
  rewrite reltCompAssoc.
  apply reltComposeMono2, H.
Qed.

Lemma lemWhileSkip2 {T E F} {VE : Spec T E} {VF : Spec T F} {R G} {I : Post VE VF bool} {B : Prog E bool} {P} i :
  (forall s ρ, R s ρ s ρ) ->
  R ->> R ==> R ->
  SilentStep i G (I true) ((calcSilentPost G (I true) i)) ->
  (I true) ->> (calcSilentPost G (I true) i) ->> R ==> P ->
  VerifyProg i R G P B I ->
  VerifyProg i R G P (while B skip) (UnitRet (I false)).
Proof.
  unfold VerifyProg. 
  rewrite ! paco_eqv.
  intros R_refl R_trans H_silent H_inv HPB.
  cut (
    forall B' P',
    paco_safe i R G P' B' I ->
    paco_safe i R G P' (whileAux B skip B' skip) (UnitRet (I false))
  ).
  { intros. apply H. easy. }
  pcofix rec. intros. punfold H0. dependent destruction H0.
  { destruct v.
    { rewrite frobProgId at 1. cbn. pfold. econstructor. 
      { apply (stable_compose_R (calcSilentPost G (I true) i) R R_trans). }
      { apply silentStepWeakenPre with (P2 := ReltToPrec (I true)).
        {
          unfold ReltToPrec. unfold sub, subPrec.
          intros.
          destruct H0 as [s' [ρs' ?]].
          exists s', ρs'.
          specialize (H _ _ _ _ H0). 
          apply H.
        }
        { apply silentStepWeakenPost with (Q1 := calcSilentPost G (I true) i).
          2: apply H_silent.
          unfold ReltCompose, sub, subRelt.
          intros.
          exists t, σ.
          split; [easy |].
          apply R_refl.
        }
      }
      { right. apply rec. rewrite <- paco_eqv.
        eapply weakenPrec.
        { unfold VerifyProg. rewrite paco_eqv. apply HPB. }
        { eapply subReltTrans.
          { eapply reltComposeMono1. apply H. }
          { apply H_inv. }
        }
      }
    }
    { rewrite frobProgId at 1. cbn. pfold. econstructor. unfold UnitRet. easy. }
  }
  { rewrite frobProgId at 1. cbn. pfold. econstructor.
    { apply H. }
    { apply H0. }
    { apply H1. }
    intros.
    specialize (H2 v). destruct_all.
    split; [easy |].
    right. apply rec.
    destruct H3. 2: inversion H3.
    easy. 
  }
  { rewrite frobProgId at 1. cbn. pfold. econstructor.
    { apply H. }
    { apply H0. }
    { right. apply rec. 
      destruct H1. 2: inversion H1.
      easy.
    }
  }
Qed.

Module SpinLockTest.

Definition E := CASSig bool.
Definition F := LockSig.
Definition acf T := @LockActiveMap T.
Definition HAcf T : @acf_sound T F lockSpec (acf T) := @LockActiveMapSound T.
Definition VE T : Spec T E:= @casSpec T bool.
Definition VF T := @lockSpec T.
Definition VFU T := SpecWithUB (@lockSpec T) (acf T) (HAcf T).
Definition ReltU T := Relt (VE T) (VFU T).
Definition Relt T := Relt (VE T) (VF T).
Definition PrecU T := Prec (VE T) (VFU T).
Definition Prec T := Prec (VE T) (VF T).
Definition PostU T := Post (VE T) (VFU T).
Definition Post T := Post (VE T) (VF T).
Definition UState T := State (VFU T).

Ltac elim_corece :=
  repeat match goal with
  | H : context[(CASState ?T bool)] |- _ =>
      change (CASState T bool) with (@State T (CASSig bool) (VE T)) in H
  | |- context[(CASState ?T bool)] =>
      change (CASState T bool) with (@State T (CASSig bool) (VE T))
  | H : context[(ThreadsSt ?T E ?F)] |- _ =>
    unfold E in H
  | |- context[(ThreadsSt ?T E ?F)] =>
    unfold E
  | H : context[(ThreadsSt ?T ?E F)] |- _ =>
    unfold F in H
  | |- context[(ThreadsSt ?T ?E F)] =>
    unfold F
  | H : context[@PState ?T F (VFU ?T)] |- _ =>
      unfold F in H
  | |- context[@PState ?T F (VFU ?T)] =>
      unfold F
  | H : context[(forall _ : Name ?T, ThreadState (CASSig bool) F)] |- _ =>
      change ((forall _ : Name T, ThreadState (CASSig bool) F)) with (ThreadsSt T E LockSig) in H
  | |- context[(forall _ : Name ?T, ThreadState (CASSig bool) F)] =>
      change ((forall _ : Name T, ThreadState (CASSig bool) F)) with (ThreadsSt T E LockSig)
  end.

Definition i_owns {T} (i : Name T) (s: InterState F (VE T)) (ρ: Poss (VFU T)) :=
  PState ρ = inl (LockOwned i) /\ snd s = CASDef (Some true) None.

Definition i_not_owns {T} (i : Name T) (s: InterState F (VE T)) (ρ: Poss (VFU T)) :=
  (PState ρ = inl LockUnowned /\ snd s = CASDef None None) \/ 
  (exists j, j <> i /\ i_owns j s ρ).

Definition valid_state {T} (i : Name T) (s: InterState F (VE T)) (ρ: Poss (VFU T)) :=
  i_owns i s ρ \/ i_not_owns i s ρ.

Definition is_ub_state {T} (ρ: Poss (VFU T)) :=
  exists a, PState ρ = inr (UBState_, a).

Definition ub_and_idle {T} i (ρ: Poss (VFU T)) :=
  exists a, PState ρ = inr (UBState_, a) /\ a i = None.

Definition Precs {T} i A (m : LockSig A) : PrecU T :=
  fun s ρs => exists ρ, ρs = eq ρ /\
    match m with
    | Acq =>
        (valid_state i s ρ \/ is_ub_state ρ) /\
        StateWithUB_acf _ (acf T) (PState ρ) i = None
    | Rel =>
        (valid_state i s ρ \/ is_ub_state ρ) /\
        StateWithUB_acf _ (acf T) (PState ρ) i = None
    end.

Definition Posts {T} i A (m : LockSig A) : PostU T A :=
  fun v s ρs t σs => exists ρ σ, ρs = eq ρ /\ σs = eq σ /\
    match m with
    | Acq =>
        PCalls σ i = CallDone Acq /\ PRets σ i = RetPoss Acq tt /\
        ((i_not_owns i s ρ /\ i_owns i t σ /\ fst t i = Cont m (Return v)) \/
         (Precs i unit Acq s ρs /\ ub_and_idle i σ))
    | Rel =>
        PCalls σ i = CallDone Rel /\ PRets σ i = RetPoss Rel tt /\
        ((i_owns i s ρ /\ i_not_owns i t σ /\ fst t i = Cont m (Return v)) \/
         (Precs i unit Rel s ρs /\ ub_and_idle i σ))
    end.

Definition CSs {T} i A (m : LockSig A) : PostU T A :=
  fun v s ρs t σs => exists ρ σ, ρs = eq ρ /\ σs = eq σ /\
    match m with
    | Acq =>
        t = (fun j => if i =? j then Idle else fst s j, snd s) /\ 
        mapRetPoss i m v ρ σ
    | Rel =>
        t = (fun j => if i =? j then Idle else fst s j, snd s) /\ 
        mapRetPoss i m v ρ σ
    end.

Definition Rely {T} i : ReltU T :=
  fun s ρs t σs => forall ρ, ρs = eq ρ -> exists σ, σs = eq σ /\
    fst s i = fst t i /\
    (i_owns i s ρ -> i_owns i t σ \/ is_ub_state σ) /\ 
    (i_not_owns i s ρ -> i_not_owns i t σ \/ is_ub_state σ) /\
    (is_ub_state ρ -> is_ub_state σ) /\
    PCalls ρ i = PCalls σ i /\
    PRets ρ i = PRets σ i /\ 
    StateWithUB_acf _ (acf T) (PState ρ) i = StateWithUB_acf _ (acf T) (PState σ) i /\
    ((exists a e m, snd s = CASDef a (Some (MkCASPend i (CAS e m)))) -> s = t /\ ρ = σ).

Definition Guar {T} i : ReltU T :=
  fun s ρs t σs => forall ρ, ρs = eq ρ -> exists σ, σs = eq σ /\
    (forall j, j <> i -> fst s j = fst t j) /\
    (forall j, j <> i -> i_owns j s ρ -> (i_owns j t σ \/ is_ub_state σ)) /\
    (forall j, j <> i -> i_not_owns j s ρ -> (i_not_owns j t σ \/ is_ub_state σ)) /\
    (is_ub_state ρ -> is_ub_state σ) /\
    (forall j, j <> i -> PCalls ρ j = PCalls σ j /\ PRets ρ j = PRets σ j) /\
    (forall j, j <> i -> StateWithUB_acf _ (acf T) (PState ρ) j = StateWithUB_acf _ (acf T) (PState σ) j) /\
    (forall j, j <> i -> (exists a e m, snd s = CASDef a (Some (MkCASPend j (CAS e m))) )-> s = t /\ ρ = σ).

Lemma valid_state_idle {T} i s ρ: valid_state i s ρ -> StateWithUB_acf _ (acf T) (PState ρ) i = None.
Proof.
  intros.
  unfold valid_state in H.
  destruct H.
  + unfold i_owns in H. destruct H. rewrite H. easy.
  + unfold i_not_owns in H. destruct H.
    { destruct H. rewrite H. easy. }
    { destruct H as [j [? ?]]. destruct H0. rewrite H0. easy. }
Qed.

Lemma SpinLock_R_refl {T} : forall (i : Name T) s ρ, Rely i s ρ s ρ.
Proof.
  unfold Rely.
  intros.
  exists ρ0.
  repeat split; try easy.
  + intros. left. easy.
  + intros. left. easy.
Qed.    

Lemma SpinLock_R_trans {T} : 
  forall (i : Name T), Rely i ->> Rely i ==> Rely i.
Proof.
  unfold sub, subRelt, ReltCompose.
  intros.
  destruct H as [s' [ρ' [? ?]]].
  unfold Rely in *.
  intros.
  specialize (H _ H1).
  destruct_all.
  specialize (H0 _ H).
  destruct_all.
  exists x0.
  repeat split; try easy.
  + rewrite H2, H10. easy.
  + intros Howns.
    specialize (H3 Howns).
    destruct H3 as [Howns' | Hub].
    { specialize (H11 Howns'). destruct H11.
      { left. easy. }
      { right. easy. }
    }
    { specialize (H13 Hub). right. easy. }
  + intros Hunowns.
    specialize (H4 Hunowns).
    destruct H4 as [Hunowns' | Hub].
    { specialize (H12 Hunowns'). destruct H12.
      { left. easy. }
      { right. easy. }
    }
    { specialize (H13 Hub). right. easy. }
  + intros. apply H13. apply H5. easy.
  + rewrite H6, H14. easy.
  + rewrite H7, H15. easy.
  + rewrite H8, H16. easy.
  + specialize (H9 H18).
    destruct H9. subst s'.
    specialize (H17 H18).
    easy.
  + specialize (H9 H18).
    destruct H9. subst s'.
    specialize (H17 H18).
    rewrite H19. easy.
Qed.

Lemma SpinLock_G_in_R {T} : 
  forall (i j : Name T), i <> j -> Guar i ==> Rely j.
Proof.
  unfold Rely, Guar, sub, subRelt.
  intros.
  specialize (H0 _ H1).
  destruct_all.
  exists x.
  assert(j <> i) as Hneq by easy.
  specialize (H2 _ Hneq).
  specialize (H3 _ Hneq).
  specialize (H4 _ Hneq).
  specialize (H6 _ Hneq).
  specialize (H7 _ Hneq).
  specialize (H8 _ Hneq).
  repeat split; try easy.
  specialize (H8 H9). easy.
  specialize (H8 H9). easy.
Qed.

Lemma Poss_eq_inv: forall {T F} {VF: Spec T F} (i: Name T) (ρ0: Poss VF)  pcall pret,
  (fun σ =>
      exists ρ, ρ0 = ρ /\
      PState σ = PState ρ /\
      PCalls σ i = pcall /\
      PRets σ i = pret /\
      differ_pointwise (PCalls ρ) (PCalls σ) i /\
      differ_pointwise (PRets ρ) (PRets σ) i) =
  eq ({| PState := PState ρ0; 
      PCalls := fun k : Name T => if i =? k then pcall else PCalls ρ0 k; 
      PRets :=  fun k : Name T => if i =? k then pret else PRets ρ0 k |} : Poss VF).
Proof.
  intros.
  extensionality σ'.
  apply propositional_extensionality.
  split.
  { 
    intros.
    destruct H as [? [? [? [? [? [? ?]]]]]].
    subst x. 
    destruct σ'; simpl in *.
    unfold differ_pointwise in H3, H4.
    f_equal; try easy.
    { extensionality k.
      destruct (classicT (i = k)).
      { subst k. rewrite eqb_id. auto. }
      { rewrite (eqb_nid _ _ n). specialize (H3 k (ltac:(auto))). auto. }
    }
    { extensionality k.
      destruct (classicT (i = k)).
      { subst k. rewrite eqb_id. auto. }
      { rewrite (eqb_nid _ _ n). specialize (H4 k (ltac:(auto))). auto. }
    }
  }
  {
    intros.
    subst σ'.
    simpl.
    exists ρ0.
    rewrite eqb_id.
    repeat split; auto.
    { apply differ_pointwise_trivial. }
    { apply differ_pointwise_trivial. }
  }
Qed.

Lemma Poss_eq_inv2: forall {T F} {VF: Spec T F} (i: Name T) (ρ: Poss VF) (st: State VF) pcall pret,
  (fun σ =>
      PState σ = st /\
      PCalls σ i = pcall /\
      PRets σ i = pret /\
      differ_pointwise (PCalls ρ) (PCalls σ) i /\
      differ_pointwise (PRets ρ) (PRets σ) i) =
  eq ({| PState := st; 
      PCalls := fun k : Name T => if i =? k then pcall else PCalls ρ k; 
      PRets :=  fun k : Name T => if i =? k then pret else PRets ρ k |} : Poss VF).
Proof.
  intros.
  extensionality σ'.
  apply propositional_extensionality.
  split.
  { 
    intros.
    destruct H as [? [? [? [? ?]]]]. 
    destruct σ'; simpl in *.
    unfold differ_pointwise in H2, H3.
    f_equal; try easy.
    { extensionality k.
      destruct (classicT (i = k)).
      { subst k. rewrite eqb_id. auto. }
      { rewrite (eqb_nid _ _ n). specialize (H2 k (ltac:(auto))). auto. }
    }
    { extensionality k.
      destruct (classicT (i = k)).
      { subst k. rewrite eqb_id. auto. }
      { rewrite (eqb_nid _ _ n). specialize (H3 k (ltac:(auto))). auto. }
    }
  }
  {
    intros.
    subst σ'.
    simpl.
    rewrite eqb_id.
    repeat split; auto.
    { apply differ_pointwise_trivial. }
    { apply differ_pointwise_trivial. }
  }
Qed.

Lemma Poss_eq_inv3: forall {T F} {VF: Spec T F} (i: Name T) (ρ0: Poss VF) ρs pcall pret,
  ρs = eq ρ0 ->
  (fun σ =>
      exists ρ, ρs ρ /\
      PState σ = PState ρ /\
      PCalls σ i = pcall /\
      PRets σ i = pret /\
      differ_pointwise (PCalls ρ) (PCalls σ) i /\
      differ_pointwise (PRets ρ) (PRets σ) i) =
  eq ({| PState := PState ρ0; 
      PCalls := fun k : Name T => if i =? k then pcall else PCalls ρ0 k; 
      PRets :=  fun k : Name T => if i =? k then pret else PRets ρ0 k |} : Poss VF).
Proof.
  intros.
  rewrite <- Poss_eq_inv.
  rewrite H.
  reflexivity.
Qed.

Lemma Poss_eq_unique: forall {T} ρs (ρ: Poss (VFU T)) ρ', 
  ρs = eq ρ -> ρs ρ' -> ρ = ρ'.
Proof.
  intros.
  rewrite H in H0.
  apply H0.
Qed.

Lemma Poss_eq_unique2: forall {T} ρs (ρ: Poss (VFU T)) ρ', 
  ρs = eq ρ -> ρs = eq ρ' -> ρ' = ρ.
Proof.
  intros.
  rewrite H in H0.
  assert(eq ρ ρ = eq ρ' ρ). { rewrite H0. reflexivity. }
  rewrite <- H1.
  reflexivity.
Qed.

Lemma Poss_eq_unique3: forall {T} (ρ: Poss (VFU T)) ρ', 
  eq ρ = eq ρ' -> ρ = ρ'.
Proof.
  intros.
  assert(eq ρ ρ' = eq ρ' ρ'). { rewrite H. reflexivity. }
  rewrite H0.
  reflexivity.
Qed.

Lemma SpinLock_Inv_in_R {T} : 
  forall (i j : Name T), i <> j -> InvokeAny SpinLockImpl i ==> Rely j.
Proof.
  intros.
  unfold InvokeAny, sub, subRelt.
  intros.
  destruct H0 as [A [m HInv]].
  unfold TInvoke in HInv.
  destruct_all.
  unfold TIdle in H0.
  destruct_all.
  inversion H1.
  simpl in H5.
  elim_corece.
  rewrite H0 in H5.
  inversion H5; subst.
  dependent destruction H8.
  unfold Rely.
  intros.
  exists (@MkPoss T F (VFU T) (PState ρ0)
          (fun k => if i =? k then CallPoss m else PCalls ρ0 k)
          (fun k => if i =? k then RetIdle else PRets ρ0 k)).
  split.
  { subst ρ. apply Poss_eq_inv. }
  split.
  { apply H6. easy. }
  split.
  { intros. unfold i_owns in *. simpl in *. left. elim_corece. rewrite <- H2. easy. }
  split.
  { intros. unfold i_not_owns, i_owns in *. simpl in *. left. elim_corece. rewrite <- H2. easy. }
  split.
  { intros. unfold is_ub_state in *. simpl in *. apply H7. }
  split.
  { simpl. rewrite (eqb_nid i j H). easy. }
  split.
  { simpl. rewrite (eqb_nid i j H). easy. }
  split.
  { simpl. easy. }
  
Qed.

Lemma SpinLock_Ret_in_R {T} : 
  forall (i j : Name T), i <> j -> ReturnAny SpinLockImpl i ==> Rely j.
Proof.
  intros.
  unfold ReturnAny, sub, subRelt.
  intros.
  destruct H0 as [A [m [v HRet]]].
  unfold TReturn in HRet.
  destruct_all.
  unfold Returned in H0.
  inversion H1.
  simpl in *.
  inversion H4; subst.
  dependent destruction H7.
  dependent destruction H10.
  specialize (H0 H11).
  unfold Rely.
  intros.
  exists (@MkPoss T F (VFU T) (PState ρ0)
          (fun j => if i =? j then CallIdle else PCalls ρ0 j)
          (fun j => if i =? j then RetIdle else PRets ρ0 j)).
  split.
  { subst ρ. unfold mapRetPoss. rewrite <- Poss_eq_inv.
    extensionality x. apply propositional_extensionality. split; intros; destruct_all; subst.
    { exists x0. easy. }
    { exists x0. specialize (H0 x0 (ltac:(reflexivity))). easy. }
  }
  split.
  { apply H5. easy. }
  split.
  { intros. unfold i_owns in *. simpl in *. left. elim_corece. rewrite <- H2. easy. }
  split.
  { intros. unfold i_not_owns, i_owns in *. simpl in *. left. elim_corece. rewrite <- H2. easy. }
  split.
  { intros. unfold is_ub_state in *. simpl in *. apply H6. } 
  { simpl. rewrite (eqb_nid i j H). easy. }
Qed.

Lemma SpinLock_init_in_P {T} : 
  forall i (A: Type) m, Precs i A m (allIdle, (VE T).(Init)) (eq initPoss).
Proof.
  intros.
  unfold Precs.
  exists initPoss.
  split; [ reflexivity |].
  unfold valid_state, i_not_owns, initPoss.
  destruct m. simpl.
  + split. 
    { left. right. left. easy. }
    easy.
  + split. 
    { left. right. left. easy. }
    easy.
Qed.

Lemma SpinLock_P_stable {T} : 
  forall (i: Name T) A m, Stable (Rely i) (Precs i A m).
Proof.
  unfold Stable, stablePrec, stableRelt, sub, subPrec, subRelt.
  intros.
  rename ρ into ρs.
  destruct H as [s' [ρs' [? ?]]].
  unfold Precs, Rely in *.
  destruct H as [ρ' [? ?]].
  specialize (H0 _ H).
  destruct H0 as [ρ [? ?]].
  destruct_all.
  exists ρ.
  split; [easy |].
  destruct m.
  + destruct H1 as [[Hvalid | Hub] HIdle].
    - destruct Hvalid as [Howns | Hunowns].
      * specialize (H3 Howns). destruct H3 as [Howns' | Hub'].
        { split.
          { left. left. easy. }
          { rewrite <- H8. apply HIdle. }
        }
        { split.
          { right. unfold is_ub_state in Hub'. easy. }
          { rewrite <- H8. apply HIdle. }
        }
      * specialize (H4 Hunowns). destruct H4 as [Hunowns' | Hub'].
        { split.
          { left. right. easy. }
          { rewrite <- H8. apply HIdle. }
        }
        { split.
          { right. unfold is_ub_state in Hub'. easy. }
          { rewrite <- H8. apply HIdle. }
        }
    - specialize (H5 Hub).
      split.
      { right. easy. }
      { rewrite <- H8. apply HIdle. }
  + destruct H1 as [[Hvalid | Hub] HIdle].
    - destruct Hvalid as [Howns | Hunowns].
      * specialize (H3 Howns). destruct H3 as [Howns' | Hub'].
        { split.
          { left. left. easy. }
          { rewrite <- H8. apply HIdle. }
        }
        { split.
          { right. unfold is_ub_state in Hub'. easy. }
          { rewrite <- H8. apply HIdle. }
        }
      * specialize (H4 Hunowns). destruct H4 as [Hunowns' | Hub'].
        { split.
          { left. right. easy. }
          { rewrite <- H8. apply HIdle. }
        }
        { split.
          { right. unfold is_ub_state in Hub'. easy. }
          { rewrite <- H8. apply HIdle. }
        }
    - specialize (H5 Hub).
      split.
      { right. easy. }
      { rewrite <- H8. apply HIdle. }
Qed.

Lemma SpinLock_switch_code {T} : 
  forall (i: Name T) A m1 B m2 v,
    (prComp (Precs i A m1) (Posts i A m1 v)) <<- (CSs i A m1 v) ==> Precs i B m2.
Proof.
  unfold sub, subPrec.
  intros.
  rename ρ into ρs.
  destruct H as [s2 [ρs2 [? ?]]].
  destruct H as [s1 [ρs1 [? ?]]].
  unfold Precs, Posts, CSs in *.
  destruct H as [ρ1 [? ?]].
  destruct H1 as [ρ1' [ρ2 [? [? ?]]]].
  pose proof Poss_eq_unique2 _ _ _ H H1 as Htmp. subst ρ1'.
  destruct H0 as [ρ2' [ρ [? [? ?]]]].
  pose proof Poss_eq_unique2 _ _ _ H0 H3 as Htmp. subst ρ2'.
  exists ρ. split; [easy |].
  cut((valid_state i s ρ \/ is_ub_state ρ) /\ StateWithUB_acf LockStep (acf T) (PState ρ) i = None).
  { destruct m2; easy. }
  assert(
      exists v: A,
      PCalls ρ2 i = CallDone m1 /\
      PRets ρ2 i = RetPoss m1 v /\
      ((valid_state i s2 ρ2 /\ fst s2 i = Cont m1 (Return v)) \/ 
       (ub_and_idle i ρ2))) as Hpost.
  { destruct m1; exists tt; destruct v.
    { repeat split; try easy.
      destruct H4 as [? [? Hpost]].
      destruct Hpost as [HH | HH].
      { left. split; [| easy]. left. easy. }
      { right. easy. }
    }
    { repeat split; try easy.
      destruct H4 as [? [? Hpost]].
      destruct Hpost as [HH | HH].
      { left. split; [| easy]. right. easy. }
      { right. easy. }
    }
  }
  destruct Hpost as [v' Hpost].
  assert(s = (fun j : Name T => if i =? j then Idle else fst s2 j, snd s2) /\ mapRetPoss i m1 v ρ2 ρ) as HCs.
  { destruct m1; easy. }
  destruct HCs as [Hs Hret].
  assert(PState ρ = PState ρ2) as Hρ2. { unfold mapRetPoss in Hret. easy. }
  destruct Hpost as [? [? [[Hvalid Hfst] | HH]]].
  { split.
    { left.
      unfold valid_state in Hvalid.
      destruct Hvalid as [Howns | Hunowns].
      { left. unfold i_owns in *. subst s. simpl. unfold mapRetPoss in Hret.
        split. 
        { destruct_all. rewrite Hρ2. easy. }
        { easy. }
      }
      { right. unfold i_not_owns in *. unfold i_owns in *. subst s. simpl. 
        destruct Hunowns as [Hunowns | [j [? ?]]].
        { left. destruct Hunowns. rewrite Hρ2. split; easy. }
        { right. exists j. rewrite Hρ2. split; easy. }
      }
    }
    { rewrite Hρ2. eapply valid_state_idle. apply Hvalid. }
  }
  { unfold is_ub_state. unfold ub_and_idle in HH.
    destruct HH as [a [Hacf Hnone]].
    split.
    { right. exists a. rewrite Hρ2. easy. }
    { rewrite Hρ2. rewrite Hacf. simpl. easy. }
  }
Qed.

Definition MkmapRetPoss{T F VF A} i (m : F A) (ρ : @Poss T F VF) : @Poss T F VF :=
  MkPoss T F VF (PState ρ)
         (fun j => if i =? j then CallIdle else PCalls ρ j)
         (fun j => if i =? j then RetIdle else PRets ρ j).

Lemma differ_pointwise_calc {A State : Type} (f g: A -> State) i (s: State):
  differ_pointwise f g i -> 
  g i = s ->
  (fun j => if i =? j then s else f j) = g.
Proof.
  intros.
  extensionality j.
  destruct (classicT (i = j)).
  + subst j. rewrite eqb_id. easy.
  + rewrite (eqb_nid _ _ n). 
    unfold differ_pointwise in H.
    assert(j <> i) as Hneq by easy.
    specialize (H j Hneq).
    easy.
Qed.
 
Lemma MkmapRetPoss_eq {T A} i (m : F A) v (ρ : @Poss T F (VFU T)) ρs:
  ρs = eq ρ ->
  PCalls ρ i = CallDone m ->
  PRets ρ i = RetPoss m v ->
  (fun τ : Poss (VFU T) =>
    exists σ : Poss (VFU T), ρs σ /\ mapRetPoss i m v σ τ) =
  eq (MkmapRetPoss i m ρ).
Proof.
  intros.
  extensionality x.
  apply propositional_extensionality.
  split; intros.
  { destruct H2 as [σ [? ?]]. 
    unfold mapRetPoss in H3.
    destruct_all.
    unfold MkmapRetPoss.
    pose proof Poss_eq_unique _ _ _ H H2 as Htmp. subst σ.
    destruct x. simpl in *. subst.
    f_equal; try easy.
    { apply differ_pointwise_calc; easy. }
    { apply differ_pointwise_calc; easy. }
  }
  { exists ρ. 
    split. { rewrite H. reflexivity. }
    subst x.
    unfold MkmapRetPoss, mapRetPoss.
    simpl.
    rewrite eqb_id.
    repeat split; try easy.
    { apply differ_pointwise_trivial. }
    { apply differ_pointwise_trivial. }
  }
Qed.

Lemma SpinLock_all_return {T} : 
  forall (i: Name T) A m v, ReturnStep i (Guar i) (Posts i A m v) m v (CSs i A m v).
Proof.
  unfold ReturnStep.
  intros.
  destruct H as [s0 [ρs0 ?]].
  destruct H as [ρ0 [ρ [? [? ?]]]].
  exists ρs.
  split.
  { exists ρ. rewrite H1. reflexivity. }
  split.
  { intros. exists σ. split; [easy | constructor]. }
  split.
  { intros.
    pose proof Poss_eq_unique _ _ _ H1 H3 as Htmp. subst ρ.
    destruct m; simpl in *; destruct v; easy.
  }
  split.
  { unfold CSs.
    exists ρ.
    exists (MkmapRetPoss i m ρ).
    split; [easy |].
    split. 
    { apply MkmapRetPoss_eq. 
      { easy. }
      { destruct m; easy. }
      { destruct m; destruct v; easy. }
    }
    assert(mapRetPoss i m v ρ (MkmapRetPoss i m ρ)).
    { unfold mapRetPoss, MkmapRetPoss. simpl. rewrite eqb_id.
      destruct m; repeat split; try destruct v; try apply differ_pointwise_trivial; try easy.
    }
    destruct m; easy.
  }
  { unfold Guar.
    intros.
    pose proof Poss_eq_unique2 _ _ _ H1 H3 as Htmp. subst ρ1.
    exists  (MkmapRetPoss i m ρ).
    split.
    { apply MkmapRetPoss_eq. 
      { easy. }
      { destruct m; easy. }
      { destruct m; destruct v; easy. }
    }
    split.
    { intros. simpl. assert(i <> j) as n by easy. rewrite (eqb_nid _ _ n). easy. }
    split.
    { intros. left. unfold i_owns in *. simpl in *. easy. }
    split.
    { intros. left. unfold i_not_owns, i_owns in *. simpl in *. easy. }
    split.
    { intros. unfold is_ub_state in *. simpl in *. easy. }
    split.
    { intros. simpl. assert(i <> j) as n by easy. rewrite (eqb_nid _ _ n). easy. }
    { intros. simpl. easy. }
  }
Qed.

Lemma SpinLock_verify_aux' {T} (i: Name T) A (m : LockSig A):
  (prComp (Precs i A m) (TInvoke SpinLockImpl i A m)) = 
  fun s ρs t σs => exists ρ σ, ρs = eq ρ /\ σs = eq σ /\
    fst s i = Idle /\
    fst t i = Cont m (SpinLockImpl A m) /\
    differ_pointwise (fst s) (fst t) i /\
    snd s = snd t /\
    StateWithUB_acf _ (acf T) (PState ρ) i = None /\
    PState ρ = PState σ /\
    PCalls ρ i = CallIdle /\ PRets ρ i = RetIdle /\
    PCalls σ i = CallPoss m /\ PRets σ i = RetIdle /\
    differ_pointwise (PCalls ρ) (PCalls σ) i /\
    differ_pointwise (PRets ρ) (PRets σ) i /\
    ((i_owns i s ρ /\ i_owns i t σ) \/ 
     (i_not_owns i s ρ /\ i_not_owns i t σ) \/
     (is_ub_state ρ /\ is_ub_state σ)).
Proof.
  extensionality s. extensionality ρs.
  extensionality t. extensionality σs.
  apply propositional_extensionality.
  split; intros.
  { destruct H as [H1 H2].
    destruct H1 as [ρ [Hρ Htmp]].
    assert((valid_state i s ρ \/ is_ub_state ρ) /\ StateWithUB_acf LockStep (acf T) (PState ρ) i = None) as HPrecs. {
      destruct m; easy.
    }
    clear Htmp.
    destruct HPrecs as [HPrecs HNone].
    unfold TInvoke in H2.
    rewrite Hρ in H2.
    rewrite Poss_eq_inv in H2.
    exists ρ. eexists.
    split; [easy |].
    split. { destruct_all. apply e0. }
    unfold TIdle in H2.
    destruct H2 as [[Hfst HρIdle] ?].
    specialize (HρIdle ρ (ltac:(easy))).
    destruct H as [Hstep [Hsnd Hσ]].
    inversion Hstep; subst. 
    simpl in *.
    rewrite Hfst in H. inversion H. subst.
    dependent destruction H2.
    rewrite eqb_id.
    repeat split; try easy; try apply differ_pointwise_trivial.
    { unfold differ_pointwise. intros j Hneq. specialize (H0 j Hneq). easy. }
    { destruct HPrecs as [[Howns | Hunowns] | Hub].
      { left. unfold i_owns in *. 
        elim_corece. rewrite <- Hsnd.
        repeat split; try easy.
      }
      { right. left. unfold i_not_owns, i_owns in *.
        elim_corece. rewrite <- Hsnd.
        repeat split; try easy.
      }
      { right. right. unfold is_ub_state in *. easy. }
    }
  }
  { destruct H as [ρ [σ [Hρ [Hσ H]]]].
    unfold prComp.
    split.
    { unfold Precs.
      exists ρ. split; [easy |].
      cut((valid_state i s ρ \/ is_ub_state ρ) /\ StateWithUB_acf LockStep (acf T) (PState ρ) i = None).
      { destruct m; easy. }
      { destruct_all. split; [| easy].
        destruct H11 as [Howns | [Hunowns | Hub]].
        { left. left. easy. }
        { left. right. easy. }
        { right. easy. }
      }
    }
    { unfold TInvoke.
      rewrite Hρ.
      rewrite Poss_eq_inv.
      split.
      { unfold TIdle.
        split; [easy |].
        intros ρ0 ?. subst ρ0. easy.
      }
      split.
      { constructor.
        { simpl. destruct_all. elim_corece. rewrite H, H0. constructor; easy. }
        { simpl. destruct_all. unfold differ_pointwise in H1. intros j Hneq. specialize (H1 j Hneq). easy. }
      }
      split; [easy |].
      { rewrite Hσ.
        extensionality x. apply propositional_extensionality. split; intros; destruct_all; subst.
        { destruct x. simpl in *. subst. f_equal.
          { apply differ_pointwise_calc; easy. }
          { apply differ_pointwise_calc; easy. }
        }
        { destruct σ. simpl in *. subst. f_equal.
          { unfold differ_pointwise in H10. extensionality j. destruct (classicT (i = j)).
            { subst j. rewrite eqb_id. easy. }
            { rewrite (eqb_nid _ _ n). specialize (H10 j (ltac:(easy))). easy. }
          }
          { unfold differ_pointwise in H11. extensionality j. destruct (classicT (i = j)).
            { subst j. rewrite eqb_id. easy. }
            { rewrite (eqb_nid _ _ n). specialize (H11 j (ltac:(easy))). easy. }
          }
        }
      }
    }
  }
Qed.

Lemma SpinLock_verify_aux {T} (i: Name T) A (m : LockSig A):
  (prComp (Precs i A m) (TInvoke SpinLockImpl i A m) ->> Rely i) = 
  fun s ρs t σs => exists ρ σ, ρs = eq ρ /\ σs = eq σ /\
    fst s i = Idle /\
    fst t i = Cont m (SpinLockImpl A m) /\
    StateWithUB_acf _ (acf T) (PState ρ) i = None /\
    StateWithUB_acf _ (acf T) (PState σ) i = None /\
    PCalls ρ i = CallIdle /\ PRets ρ i = RetIdle /\
    PCalls σ i = CallPoss m /\ PRets σ i = RetIdle /\
    ((i_owns i s ρ /\ (i_owns i t σ \/ is_ub_state σ)) \/ 
     (i_not_owns i s ρ /\ (i_not_owns i t σ \/ is_ub_state σ)) \/
     (is_ub_state ρ /\ is_ub_state σ)).
Proof.
  rewrite SpinLock_verify_aux'.
  extensionality s. extensionality ρs.
  extensionality t. extensionality σs.
  apply propositional_extensionality.
  split; intros; simpl.
  { destruct H as [s' [ρs' [H HRely]]].
    destruct H as [ρ [ρ' [Hρ [Hρ' H]]]].
    unfold Rely in HRely.
    specialize (HRely _ Hρ').
    destruct HRely as [σ [Hσ HRely]].
    exists ρ, σ.
    repeat split; try easy.
    { destruct_all. elim_corece. rewrite <- H0. easy. }
    { destruct_all. rewrite <- H6. rewrite <- H11. easy. }
    { destruct_all. rewrite <- H4. easy. }
    { destruct_all. rewrite <- H5. easy. }
    { destruct_all. destruct H18 as [Howns | [Hunowns | Hub]].
      { specialize (H1 (proj2 Howns)).
        destruct H1 as [Howns' | Hub'].
        { left. split; [| left]; easy. }
        { left. split; [| right]; easy. }
      }
      { specialize (H2 (proj2 Hunowns)).
        destruct H2 as [Hunowns' | Hub'].
        { right. left. split; [| left]; easy. }
        { right. left. split; [| right]; easy. }
      }
      { specialize (H3 (proj2 Hub)). right. right. easy. }
    }
  }
  { unfold ReltCompose.
    destruct H as [ρ [σ [Hρ [Hσ H]]]].
    remember ( MkPoss T F (VFU T) (PState ρ)
          (fun j : Name T => if i =? j then CallPoss m else PCalls ρ j)
          (fun j : Name T => if i =? j then RetIdle else PRets ρ j)) as ρ'.
    exists (fun j => if i =? j then fst t i else fst s j, snd s).
    exists (eq ρ').
    split.
    { exists ρ, ρ'.
      subst ρ'. simpl. rewrite eqb_id.
      repeat split; try easy; try apply differ_pointwise_trivial.
      destruct_all.
      destruct H7 as [Howns | [Hunowns | Hub]].
      { left. unfold i_owns in *. easy. }
      { right. left. unfold i_not_owns, i_owns in *. easy. }
      { right. right. unfold is_ub_state in *. easy. }
    }
    { unfold Rely. intros ρ0 Hρ0.
      pose proof Poss_eq_unique3 _ _ Hρ0 as Htmp. subst ρ0. clear Hρ0.
      exists σ.
      simpl. rewrite eqb_id.
      assert(PState ρ = PState ρ') as Hρ'. { subst ρ'. reflexivity. } 
      repeat split; try easy.
      { intros Honws. unfold i_owns in *. simpl in *. destruct_all. destruct H9. easy.
        destruct H9.
        { elim_corece. rewrite H0 in Hρ'. unfold i_not_owns in H9. destruct_all.
          destruct H9; destruct_all.
          { rewrite H9 in Hρ'. inversion Hρ'. }
          { unfold i_owns in H11. destruct H11. rewrite H11 in Hρ'. inversion Hρ'. subst i. contradiction. }
        }
        { right. easy. }
      }
      { intros Hnotowns.
        destruct H as [? [? [? [? [? [? [? [? Hpos]]]]]]]].
        destruct Hpos as [Howns | [Hunowns | Hub]].
        { destruct Howns as [Howns ?].
          unfold i_not_owns, i_owns in *.
          elim_corece. rewrite <- Hρ' in Hnotowns.
          assert(PState ρ <> inl (LockOwned i)) as Hneq. 
          { destruct Hnotowns.
            { destruct H8. rewrite H8. easy. }
            { destruct H8 as [j [n [H8 ?]]]. rewrite H8. intro HH. inversion HH. subst j. contradiction. } 
          }
          destruct Howns.
          rewrite H8 in Hneq. contradiction.
        }
        { easy. }
        { right. easy. }
      }
      { intros Hub. destruct H as [? [? [? [? [? [? [? [? Hpos]]]]]]]].
        destruct Hpos as [Howns | [Hunowns | Hub']].
        { destruct Howns as [Howns ?].
          unfold i_owns in Howns.
          destruct Howns as [Howns ?].
          rewrite Howns in Hρ'. 
          unfold is_ub_state in Hub. destruct Hub as [a Hub].
          elim_corece. rewrite Hub in Hρ'. inversion Hρ'.
        }
        { destruct Hunowns as [Hunowns ?].
          unfold i_not_owns in Hunowns.
          destruct Hunowns as [Hunowns | Hunowns].
          { destruct Hunowns as [Hunowns ?].
            rewrite Hunowns in Hρ'. 
            unfold is_ub_state in Hub. destruct Hub as [a Hub].
            elim_corece. rewrite Hub in Hρ'. inversion Hρ'.
          }
          { destruct Hunowns as [j [n [Hunowns ?]]].
            rewrite Hunowns in Hρ'. 
            unfold is_ub_state in Hub. destruct Hub as [a Hub].
            elim_corece. rewrite Hub in Hρ'. inversion Hρ'.
           }
        }
        { easy. }
      }
      { subst ρ'. simpl. rewrite eqb_id. easy. }
      { subst ρ'. simpl. rewrite eqb_id. easy. }
      { elim_corece. rewrite <- Hρ'. destruct_all. rewrite H1, H2. easy. }
    }
  }
Qed.

Lemma SpinLock_Acq_verified {T} : 
  forall (i: Name T), 
      VerifyProg i (Rely i) (Guar i) 
      (prComp (Precs i unit Acq) (TInvoke SpinLockImpl i _ Acq) ->> Rely i)
      (SpinLockImpl _ Acq)
      (Posts i unit Acq).
Proof.
  intros.
  simpl.
  unfold SpinLockAcq.
  rewrite SpinLock_verify_aux.
  apply weakenPrec with (P := 
    fun _ _ s ρs => exists (ρ: Poss (VFU T)), ρs = eq ρ /\
      fst s i = Cont Acq (SpinLockImpl unit Acq) /\
      StateWithUB_acf _ (acf T) (PState ρ) i = None /\
      PCalls ρ i = CallPoss Acq /\ PRets ρ i = RetIdle /\
      (i_owns i s ρ \/ i_not_owns i s ρ \/ is_ub_state ρ)).
  2: {
    unfold sub, subRelt.
    intros.
    rename ρ into ρs.
    rename σ into σs.
    destruct H as [ρ [σ [? [? ?]]]].
    exists σ.
    repeat split; try easy.
    destruct_all.
    destruct H9 as [Howns | [Hunowns | Hub]].
    { destruct Howns as [Howns HT].
      destruct HT.
      { left. easy. }
      { right. right. easy. }
    }
    { destruct Hunowns as [Hunowns HT].
      destruct HT.
      { right. left. easy. }
      { right. right. easy. }
    }
    { right. right. easy. }
  }
  eapply weakenPost.
  {
    eapply (lemWhileSkip2
      (I := (fun v s ρs t σs => exists (ρ σ: Poss (VFU T)), ρs = eq ρ /\ σs = eq σ /\
        fst s i = Cont Acq (SpinLockImpl unit Acq) /\
        StateWithUB_acf _ (acf T) (PState ρ) i = None /\
        StateWithUB_acf _ (acf T) (PState σ) i = None /\
        PCalls ρ i = CallPoss Acq /\ PRets ρ i = RetIdle /\
        ((v = true /\ 
            fst t i = Cont Acq (NoOp (SpinLockImpl unit Acq)) /\
            PCalls σ i = CallPoss Acq /\ PRets σ i = RetIdle /\
            ((i_owns i s ρ /\ (i_owns i t σ \/ is_ub_state σ)) \/
            (i_not_owns i s ρ /\ (i_not_owns i t σ \/ is_ub_state σ)) \/
            (is_ub_state ρ /\ is_ub_state σ))) \/
         (v = false /\
            fst t i = Cont Acq (Return tt) /\
            PCalls σ i = CallDone Acq /\ PRets σ i = RetPoss Acq tt /\
            ((i_not_owns i s ρ /\ (i_owns i t σ \/ is_ub_state σ)) \/
             (is_ub_state ρ /\ is_ub_state σ)))
        )
      ))).
    { apply SpinLock_R_refl. }
    { apply SpinLock_R_trans. } 
    { apply calcSilentPostGuar.
      intros.
      unfold calcSilentPost.
      repeat split; try easy.
      unfold Guar. intros. exists ρ. simpl.
      repeat split; try easy.
      { intros. simpl. unfold differ_pointwise in H0. specialize (H0 j (ltac:(easy))). easy. }
      { intros. do 4 destruct H. destruct_all.
        destruct H11.
        2: { destruct H11. congruence. }
        destruct_all.
        destruct H15 as [Howns | [Hunowns | Hub]].
        { destruct Howns as [Howns HT].
          destruct HT.
          { left. easy. }
          { left. easy. }
        }
        { destruct Hunowns as [Hunowns HT].
          destruct HT.
          { left. easy. }
          { left. easy. }
        }
        { left. easy. }
      }
      { intros. do 4 destruct H. destruct_all.
        destruct H11.
        2: { destruct H11. congruence. }
        destruct_all.
        destruct H15 as [Howns | [Hunowns | Hub]].
        { destruct Howns as [Howns HT].
          destruct HT.
          { left. easy. }
          { left. easy. }
        }
        { destruct Hunowns as [Hunowns HT].
          destruct HT.
          { left. easy. }
          { left. easy. }
        }
        { left. easy. }
      }
    }
    { eapply subReltTrans with (R2 :=
      (fun (_ : InterState F (VE T)) (_ : PossSet (VFU T)) (s : (Name T -> ThreadState (CASSig bool) F) * State (VE T))(ρs : Poss (VFU T) -> Prop) =>
        exists ρ : Poss (VFU T), ρs = eq ρ /\ fst s i = Cont Acq (SpinLockImpl unit Acq) /\ 
          StateWithUB_acf LockStep (acf T) (PState ρ) i = None /\ 
          PCalls ρ i = CallPoss Acq /\ PRets ρ i = RetIdle /\ 
          (i_owns i s ρ \/ i_not_owns i s ρ \/ is_ub_state ρ)) ->> Rely i).
      {
        rewrite <- reltCompAssoc.
        apply reltComposeMono1.
        unfold sub, subRelt. intros.
        rename ρ into ρs.
        rename σ into σs.
        destruct H as [s' [ρs' [? ?]]].
        destruct H as [ρ [ρ' [Hρ [Hρ' ?]]]].
        destruct_all.
        unfold calcSilentPost in H0.
        destruct H0. destruct H0 as [s1 [ρs1 [ρ1 [ρ'' [Hρ1 [Hρ'' ?]]]]]].
        pose proof Poss_eq_unique2 ρs' ρ' ρ'' (ltac:(easy)) Hρ''. subst ρ''. clear Hρ''.
        destruct H6. subst σs.
        exists ρ'.
        destruct_all. destruct H14.
        2: { destruct H14. congruence. }
        destruct_all.
        repeat split; try easy.
        { rewrite H15 in H8. inversion H8. subst. dependent destruction H19.
          unfold E. unfold F. rewrite H20. reflexivity. }
        { destruct H18 as [Howns | [Hunowns | Hub]].
          { destruct Howns as [? HT].
            destruct HT.
            { left. unfold i_owns. unfold i_owns in H19. elim_corece. rewrite H6 in H19. easy. }
            { right. right. easy. }
          }
          { destruct Hunowns as [? HT].
            destruct HT.
            { right. left. unfold i_not_owns, i_owns. unfold i_not_owns, i_owns in H19. elim_corece. rewrite H6 in H19. easy. }
            { right. right. easy. }
          }
          { right. right. easy. }
        }
      }
      { unfold sub, subRelt.
        intros.
        rename σ into σs.
        rename ρ into ρs.
        destruct H as [s' [ρs' [? HRely]]].
        destruct H as [ρ' [Hρ' ?]].
        unfold Rely in HRely.
        specialize (HRely _ Hρ').
        destruct HRely as [σ [Hσ HRely]].
        exists σ.
        destruct_all.
        repeat split; try easy.
        { elim_corece. rewrite <- H0. easy. }
        { rewrite <- H6. easy. }
        { rewrite <- H4. easy. }
        { rewrite <- H5. easy. }
        { destruct H10 as [Howns | [Hunowns | Hub]].
          { specialize (H1 Howns). destruct H1.
            { left. easy. }
            { right. right. easy. }
          }
          { specialize (H2 Hunowns). destruct H2.
            { right. left. easy. }
            { right. right. easy. }
          }
          { specialize (H3 Hub). right. right. easy. }
        }
      }
    }
    {
      eapply lemBind.
      { eapply (lemCall
          (Q := fun s ρs t σs => exists (ρ σ: Poss (VFU T)), ρs = eq ρ /\ σs = eq σ /\
                  fst s i = Cont Acq (SpinLockImpl unit Acq) /\
                  fst t i = UCall Acq (CAS None (Some true))
                              (fun x : bool =>
                              whileAux (tmp <- call (CAS None (Some true)); ret (negb tmp)) skip
                                       (tmp <- Return x; ret (negb tmp)) skip) /\
                  StateWithUB_acf _ (acf T) (PState ρ) i = None /\
                  StateWithUB_acf _ (acf T) (PState σ) i = None /\
                  PCalls ρ i = CallPoss Acq /\ PRets ρ i = RetIdle /\
                  PCalls σ i = CallPoss Acq /\ PRets σ i = RetIdle /\
                  ((i_owns i s ρ /\ (i_owns i t σ \/ is_ub_state σ)) \/
                   (i_not_owns i s ρ /\ (i_not_owns i t σ \/ is_ub_state σ)) \/
                   (is_ub_state ρ /\ is_ub_state σ)))
          (S := fun v s ρs t σs => exists (ρ σ: Poss (VFU T)), ρs = eq ρ /\ σs = eq σ /\
                  fst s i = UCall Acq (CAS None (Some true))
                              (fun x : bool =>
                              whileAux (tmp <- call (CAS None (Some true)); ret (negb tmp)) skip
                                       (tmp <- Return x; ret (negb tmp)) skip) /\
                  StateWithUB_acf _ (acf T) (PState ρ) i = None /\
                  StateWithUB_acf _ (acf T) (PState σ) i = None /\
                  PCalls ρ i = CallPoss Acq /\ PRets ρ i = RetIdle /\
                  PCalls σ i = CallDone Acq /\ PRets σ i = RetPoss Acq tt /\
                  ((v = true /\ i_owns i s ρ /\ (i_owns i t σ \/ is_ub_state σ)) \/
                   (v = false /\ 
                    ((i_not_owns i s ρ /\ (i_owns i t σ \/ is_ub_state σ)) \/
                     (is_ub_state ρ /\ is_ub_state σ)))))).
        { admit. }
        { admit. }
        { unfold Commit. intros.
          destruct H as [s0 [ρs0 [ρ [Hρ [Hfsts [HIdle [HCall [HRet HPrec]]]]]]]].
          exists ρs.
          split.
          { exists ρ. rewrite Hρ. reflexivity. }
          split.
          { intros. exists σ. split; [easy | constructor]. }
          split.
          { exists ρ, ρ.
            repeat split; try easy.
            { elim_corece. rewrite Hfsts in H1.
              inversion H1; subst. dependent destruction H3.
              unfold while in x.
              rewrite frobProgId in x at 1. cbn in x.
              dependent destruction x.
              easy.
            }
            { destruct HPrec as [Howns | [Hunowns | Hub]].
              { left. split; [| left]. easy. }
              { right. left. split; [| left]; easy. }
              { right. right. easy. }
              { right. left. easy. }
              { right. right. easy. }
            }
          }
        }
      }
    }
    { admit. }
  }
  { intros. destruct v. unfold UnitRet.
    unfold sub, subRelt.
    intros.
    rename σ into σs.
    rename ρ into ρs.
    destruct H as [ρ [σ [Hρ [Hσ H]]]].
    destruct H as [? [? [? [? [? Hres]]]]].
    destruct Hres as [Htrue | Hfalse].
    1: { destruct Htrue. congruence. }
    unfold Posts.
    exists ρ, σ.
    repeat split; try easy.
    destruct Hfalse as [? [? [? [? Hres]]]].
    destruct Hres as [HS | HF]. 
    { destruct HS as [HPre HPost].
      destruct HPost.
      { left. easy. }
      { right. unfold Precs, ub_and_idle.
        split.
        { exists ρ. split; [easy |].
          split; [| easy].
          left. unfold valid_state. right. easy.
        }
        { unfold is_ub_state in H8. destruct H8 as [a H8].
          exists a.
          rewrite H8 in H1. simpl in H1. easy.
        }
      }
    }
    { destruct HF as [HPre HPost].
      right. unfold Precs, ub_and_idle.
      split.
      { exists ρ. split; [easy |].
        split; [| easy].
        right. unfold valid_state. easy.
      }
      { unfold is_ub_state in HPost. destruct HPost as [a HPost].
        exists a.
        rewrite HPost in H1. simpl in H1. easy.
      }
    }
  }
Admitted.

Lemma SpinLock_Rel_aux1 {T} (i: Name T) (s1: InterState F (VE T)) ρs1 s2 ρs2: 
  (prComp (Precs i unit Rel) (TInvoke SpinLockImpl i unit Rel)) s1 ρs1 s2 ρs2 ->
    exists ρ, ρs2 = eq ρ /\ 
    fst s2 i = Cont Rel (SpinLockImpl _ Rel) /\ 
    PCalls ρ i = CallPoss Rel /\ PRets ρ i = RetIdle /\
    ((snd s2 = CASDef (Some true) None /\ PState ρ = inl (LockOwned i))  \/ 
     (PState ρ <> inl (LockOwned i) /\ (StateWithUB_acf _ (acf T) (PState ρ) i = None))).
Proof.
  intros.
  destruct H.
  unfold Precs in H.
  destruct H as [ρ1 [? ?]].
  unfold TInvoke in H0.
  destruct_all.
  exists (@MkPoss T F (VFU T) (PState ρ1)
          (fun j => if i =? j then CallPoss Rel else PCalls ρ1 j)
          (fun j => if i =? j then RetIdle else PRets ρ1 j)).
  simpl.
  split.
  { subst ρs2. rewrite <- Poss_eq_inv2. rewrite H. reflexivity. }
  split.
  { unfold TIdle in H0. destruct_all. inversion H2; subst. 
    simpl in H6. elim_corece. rewrite H0 in H6. 
    inversion H6; subst. dependent destruction H4. easy. 
  }
  rewrite eqb_id.
  do 2 split; try easy.
  elim_corece.
  rewrite H3 in H1.
  destruct H1; [left | right]; easy.
Qed.

Lemma SpinLock_Rel_aux2 {T} (i: Name T) (s1: InterState F (VE T)) ρs1 s2 ρs2: 
  (prComp (Precs i unit Rel) (TInvoke SpinLockImpl i unit Rel) ->> (Rely i)) s1 ρs1 s2 ρs2 ->
    exists ρ, ρs2 = eq ρ /\ 
    fst s2 i = Cont Rel (SpinLockImpl _ Rel) /\ 
    PCalls ρ i = CallPoss Rel /\ PRets ρ i = RetIdle /\
    ((snd s2 = CASDef (Some true) None /\ PState ρ = inl (LockOwned i))  \/ 
     (PState ρ <> inl (LockOwned i) /\ (StateWithUB_acf _ (acf T) (PState ρ) i = None))).
Proof.
  intros.
  destruct H as [s' [ρs' [? ?]]].
  pose proof SpinLock_Rel_aux1 i s1 ρs1 s' ρs' H.
  destruct H1 as [ρ' [? ?]].
  unfold Rely in H0.
  specialize (H0 _ H1).
  destruct H0 as [ρ2 [? ?]].
  exists ρ2.
  split; try easy.
  split.
  { destruct_all. rewrite <- H3. rewrite H2. reflexivity. }
  split.
  { destruct_all. rewrite <- H10. apply H4. }
  split.
  { destruct_all. rewrite <- H11. apply H5. }
  destruct_all.
  destruct H6.
  { destruct_all. specialize (H7 _ H13). destruct H7.
    { left. destruct H7. rewrite <- H14, H7, H6. easy. }
    { right. destruct H7 as [a ?]. rewrite <- H12. rewrite H7, H13. easy. }
  }
  { right. 
    destruct H6. 
    rewrite <- H12. rewrite H13.
    split; [| reflexivity].
    destruct (PState ρ').
    { destruct s.
      destruct owner.
      { destruct (classicT (i = n)).
        { subst n. specialize (H7 m (ltac:(auto))). destruct H7.
          { destruct m.
            { destruct H7. rewrite H7. easy. }
            { unfold LockOwned in H6. contradiction. }
          }
          { destruct H7. rewrite H7. easy. }
        }
        { apply H8. intros. intro. inversion H14. subst n. contradiction. }
      }
      { apply H8. intros. intro. inversion H14. }
    }
    { destruct p. destruct u.
      specialize (H9 a (ltac:(reflexivity))). destruct H9. rewrite H9. easy. 
    }
  }
Qed.

Lemma SpinLock_Rel_aux3 {T} (i: Name T) (s1: InterState F (VE T)) ρs1 s2 ρs2: 
  ((prComp (Precs i unit Rel) (TInvoke SpinLockImpl i unit Rel) ->> (Rely i)) ->> 
    (fun (s: InterState F (VE T)) (ρs: PossSet (VFU T)) t σs =>
        exists ρ σ, ρs = eq ρ /\ σs = eq σ /\
        UnderThreadStep (fst s i) (Some (CallEv (CAS (Some true) None))) (fst t i) /\
        PCalls σ i = CallDone Rel /\
        PRets σ i = RetIdle /\
        ((PState ρ = inl (LockOwned i) /\ PState σ = inl (LockRelRan i) /\ Step (VE T) (snd s) (i, (CallEv (CAS (Some true) None))) (snd t)) \/ 
         (exists a, PState σ = inr (UBState_, a) /\ (a i = Some (existT (fun A => LockSig A) unit Rel))))))
    s1 ρs1 s2 ρs2 ->
      exists ρ, ρs2 = eq ρ /\
      fst s2 i = UCall Rel (CAS (Some true) None) (fun x1 : bool => Return x1;; Return tt) /\
      PCalls ρ i = CallDone Rel /\
      PRets ρ i = RetIdle /\
      ((PState ρ = inl (LockRelRan i) /\ snd s2 = CASDef (Some true) (Some (MkCASPend i (CAS (Some true) None)))) \/
       (exists a, PState ρ = inr (UBState_, a) /\ (a i = Some (existT (fun A => LockSig A) unit Rel)))).
Proof.
  intros.
  destruct H as [s' [ρs' [? ?]]].
  apply SpinLock_Rel_aux2 in H.
  destruct H as [ρ [? [? [? [? ?]]]]].
  destruct H0 as [ρ' [ρ2 [? [? ?]]]].
  exists ρ2.
  split; [easy |].
  split.
  { destruct H6. elim_corece. rewrite H1 in H6. inversion H6; subst.
    dependent destruction H9. rewrite H13.
    unfold call, ret in x.
    rewrite ProgramFacts.frobProgId in x at 1. unfold ProgramFacts.frobProgram in x. simpl in x.
    inversion x.
    dependent destruction H5.
    reflexivity.
  }
  split; [easy |].
  split; [easy |].
  destruct H6 as [? [? [? ?]]].
  destruct H4.
  { destruct H9.
    { destruct H4. destruct H9. elim_corece. rewrite H4 in H11. destruct H11. inversion H12; subst. left. easy. }
    { right. apply H9. } 
  }
  { pose proof Poss_eq_unique2 _ _ _ H H0. subst ρ.
    destruct H9.
    { destruct H9. destruct H4. contradiction. }
    { right. destruct H9. exists x. easy. }
  }
Qed.

Lemma SpinLock_Rel_aux4 {T} (i: Name T) (s1: InterState F (VE T)) ρs1 s2 ρs2 v: 
  (((prComp (Precs i unit Rel) (TInvoke SpinLockImpl i unit Rel) ->> (Rely i)) ->> 
    (fun (s: InterState F (VE T)) (ρs: PossSet (VFU T)) t σs =>
        exists ρ σ, ρs = eq ρ /\ σs = eq σ /\
        UnderThreadStep (fst s i) (Some (CallEv (CAS (Some true) None))) (fst t i) /\
        PCalls σ i = CallDone Rel /\
        PRets σ i = RetIdle /\
        ((PState ρ = inl (LockOwned i) /\ PState σ = inl (LockRelRan i) /\ Step (VE T) (snd s) (i, (CallEv (CAS (Some true) None))) (snd t)) \/ 
         (exists a, PState σ = inr (UBState_, a) /\ (a i = Some (existT (fun A => LockSig A) unit Rel)))))) ->>
    (fun s ρs t σs =>
        exists ρ σ, ρs = eq ρ /\ σs = eq σ /\
        UnderThreadStep (fst s i) (Some (RetEv (CAS (Some true) None) v)) (fst t i) /\
        PCalls σ i = CallDone Rel /\
        PRets σ i = RetPoss Rel tt /\
        ((PState ρ = inl (LockRelRan i) /\ (forall m, PState σ <> inl (LockDef (Some i) m))) \/ 
         ((exists a, PState σ = inr (UBState_, a) /\ a i = None)))))
    s1 ρs1 s2 ρs2 ->
      exists ρ, ρs2 = eq ρ /\
      fst s2 i = Cont Rel (Return tt) /\
      PCalls ρ i = CallDone Rel /\
      PRets ρ i = RetPoss Rel tt /\
      ((forall m, PState ρ <> inl (LockDef (Some i) m)) \/ 
      (exists a, PState ρ = inr (UBState_, a) /\ a i = None)).
Proof.
  intros.
  destruct H as [s' [ρs' [? ?]]].
  apply SpinLock_Rel_aux3 in H.
  destruct H as [ρ [? [? [? [? ?]]]]].
  destruct H0 as [ρ' [ρ2 [? [? ?]]]].
  exists ρ2.
  split; [easy |].
  split.
  { destruct H6. elim_corece. rewrite H1 in H6. inversion H6; subst.
    dependent destruction H9. dependent destruction H12. rewrite H14.
    rewrite (ProgramFacts.frobProgId (@Return (CASSig bool) bool v;; Return tt)).
    unfold ProgramFacts.frobProgram.
    simpl. reflexivity.    
  }
  split; [easy |].
  split; [easy |].
  destruct H6 as [? [? [? ?]]].
  destruct H4.
  { destruct H9.
    { destruct H9. left. apply H10. }
    { destruct H9. right. exists x. easy. }
  }
  { pose proof Poss_eq_unique2 _ _ _ H H0. subst ρ.
    destruct H9.
    { destruct H9. left. easy. }
    { right. destruct H9. exists x. easy. }
  }
Qed.

Lemma SpinLock_Rel_verified {T} : 
  forall (i: Name T), 
      VerifyProg i (Rely i) (Guar i) 
      (prComp (Precs i unit Rel) (TInvoke SpinLockImpl i _ Rel) ->> Rely i)
      (SpinLockImpl _ Rel)
      (Posts i unit Rel).
Proof.
  intros. simpl.
  apply (lemBind (fun (_: bool) => 
            (fun v : unit => Posts i unit Rel v) tt)).
  + eapply weakenPost.
    eapply (lemCall 
      (Q := fun (s: InterState F (VE T)) (ρs: PossSet (VFU T)) t σs =>
        exists ρ σ, ρs = eq ρ /\ σs = eq σ /\
        UnderThreadStep (fst s i) (Some (CallEv (CAS (Some true) None))) (fst t i) /\
        PCalls σ i = CallDone Rel /\
        PRets σ i = RetIdle /\
        ((PState ρ = inl (LockOwned i) /\ PState σ = inl (LockRelRan i) /\ Step (VE T) (snd s) (i, (CallEv (CAS (Some true) None))) (snd t)) \/ 
         (exists a, PState σ = inr (UBState_, a) /\ (a i = Some (existT (fun A => LockSig A) unit Rel)))))
      (S := fun v s ρs t σs =>
        exists ρ σ, ρs = eq ρ /\ σs = eq σ /\
        UnderThreadStep (fst s i) (Some (RetEv (CAS (Some true) None) v)) (fst t i) /\
        PCalls σ i = CallDone Rel /\
        PRets σ i = RetPoss Rel tt /\
        (((PState ρ = inl (LockRelRan i) /\ forall m, PState σ <> inl (LockDef (Some i) m))) \/ 
         (exists a, PState σ = inr (UBState_, a) /\ a i = None)))).
    { unfold Stable, stableRelt, sub, subRelt.
      intros.
      rename ρ into ρs.
      rename σ into σs.
      destruct H as [s' [ρs' [? ?]]].
      destruct H as [ρ [ρ' [? [? ?]]]].
      unfold Rely in H0.
      specialize (H0 _ H1).
      destruct H0 as [σ [? ?]].
      exists ρ, σ.
      split; try easy.
      split; try easy.
      split.
      { destruct H2. destruct H3. elim_corece. rewrite <- H3. apply H2. }
      split.
      { destruct_all. unfold F. rewrite <- H7. easy. }
      split.
      { destruct_all. unfold F. rewrite <- H8. easy. }  
      destruct_all.
      destruct H12.
      { destruct H12 as [? [? ?]].
        specialize (H4 _ H13).
        destruct H4.
        { left. destruct H4. elim_corece. rewrite <- H15. easy. }
        { right. destruct H4 as [a ?].
          unfold F in H13.
          rewrite H13 in H9.
          rewrite H4 in H9.
          inversion H9; subst. rewrite eqb_id in H16.
          exists a. easy.
        }
      }
      {
        right.
        destruct H12 as [a ?].
        destruct H12.
        specialize (H6 _ H12).
        destruct H6 as [a' ?].
        unfold F in H12.
        rewrite H12 in H9.
        exists a'.
        split; try easy.
        rewrite H6 in H9.
        inversion H9; subst.
        easy.
      }
    }
    { unfold Stable, stablePost, stableRelt, sub, subRelt.
      intros.
      rename ρ into ρs.
      rename σ into σs.
      destruct H as [s' [ρs' [? ?]]].
      destruct H as [ρ [ρ' [? [? ?]]]].
      unfold Rely in H0.
      specialize (H0 _ H1).
      destruct H0 as [σ [? ?]].
      exists ρ, σ.
      split; try easy.
      split; try easy.
      split.
      { destruct H2. destruct H3. elim_corece. rewrite <- H3. apply H2. }
      split.
      { destruct_all. unfold F. rewrite <- H7. easy. }
      split.
      { destruct_all. unfold F. rewrite <- H8. easy. }  
      destruct_all.
      destruct H12.
      { destruct H12 as [? ?].
        specialize (H5 H13).
        left. easy. 
      }
      { right.
        destruct H12 as [a [? ?]].
        specialize (H6 _ H12).
        destruct H6 as [a' ?].
        exists a'.
        unfold F in H12.
        rewrite H12 in H9.
        rewrite H6 in H9.
        inversion H9; subst.
        easy.
      }
    }
    { unfold Commit. intros.
      destruct H as [s0 [ρs0 ?]].
      apply SpinLock_Rel_aux2 in H.
      destruct H as [ρ [? [? [? [? ?]]]]].
      destruct H6.
      {
        remember (
          (MkPoss T LockSig (VFU T)
          (inl (LockRelRan i))
          (fun k : Name T =>
            match @eqb (Name T) i k
            return (PCall LockSig) with
            | true => @CallDone LockSig unit Rel
            | false => @PCalls T LockSig (VFU T) ρ k
            end)
          (fun k : Name T =>
            match @eqb (Name T) i k
            return (PRet LockSig) with
            | true => @RetIdle LockSig
            | false => @PRets T LockSig (VFU T) ρ k
            end))) as σ.
        exists (eq σ).
        split. { exists σ. easy. }
        split.
        { intros. subst σ0. exists ρ.
          split. { rewrite H. reflexivity. }
          subst σ.
          destruct ρ.
          destruct_all. simpl in *. subst.
          eapply PossStepsStep.
          4: apply PossStepsRefl.
          { apply PCommitCall with (i := i) (A := unit) (m := Rel); simpl; try easy.
            { constructor. constructor. }
            { rewrite eqb_id. easy. }
            { rewrite eqb_id. easy. }
          }
          { intros. simpl. rewrite (eqb_nid _ _ H). easy. }
          { intros. simpl. rewrite (eqb_nid _ _ H). easy. }
        }
        split.
        { exists ρ, σ.
          subst σ. simpl. rewrite eqb_id. 
          repeat split; try easy.
          left. easy.
        }
        {
          unfold Guar.
          intros.
          pose proof Poss_eq_unique2 _ _ _ H H7. subst ρ0.
          exists σ.
          split; try easy.
          split.
          { unfold differ_pointwise in H0. intros. specialize (H0 j (ltac:(auto))). easy. }
          split.
          { intros.
            rewrite H9 in H6.
            destruct H6.
            inversion H10; subst; contradiction. 
          }
          split.
          { intros. subst σ. simpl. intro. inversion H10; subst; contradiction. }
          split.
          { intros. rewrite H8 in H6. destruct H6. inversion H9. }
          { intros. subst σ. simpl. assert(i <> j) by easy.
            rewrite (eqb_nid _ _ H9). destruct H6. rewrite H10. easy.
          }
        }
      }
      { 
        remember
          ((MkPoss T LockSig (VFU T)
          (inr (UBState_, fun j => if i =? j then Some (existT (fun A => LockSig A) unit Rel) else (StateWithUB_acf _ (acf T) (PState ρ) j)))
          (fun j => if i =? j then CallDone Rel else PCalls ρ j)
          (fun j => if i =? j then RetIdle else PRets ρ j))) as σ.
        exists (eq σ).
        split. { exists σ. easy. }
        split.
        { intros. subst σ0. exists ρ.
          split. { rewrite H. reflexivity. }
          subst σ.
          destruct ρ.
          destruct_all. simpl in *. subst.
          eapply PossStepsStep.
          4: apply PossStepsRefl.
          { apply PCommitCall with (i := i) (A := unit) (m := Rel); simpl; try easy.
            { destruct PState.
              { constructor.
                { intros. intro. inversion H; subst. contradiction. }
                { constructor; try rewrite eqb_id; try easy; try apply differ_pointwise_trivial. }
              }
              { destruct p as [u a]. destruct u.
                simpl in H7.
                constructor.
                constructor; try rewrite eqb_id; try easy; try apply differ_pointwise_trivial.
              }
            }
            { rewrite eqb_id. easy. }
            { rewrite eqb_id. easy. }
          }
          { intros. simpl. rewrite (eqb_nid _ _ H). easy. }
          { intros. simpl. rewrite (eqb_nid _ _ H). easy. }
        }
        split.
        { exists ρ, σ.
          subst σ. simpl. rewrite eqb_id. 
          repeat split; try easy.
          right.
          eexists.
          split.
          { reflexivity. }
          { simpl. rewrite eqb_id. easy. }
        }
        {
          unfold Guar.
          intros.
          pose proof Poss_eq_unique2 _ _ _ H H7. subst ρ0.
          exists σ.
          split; try easy.
          split.
          { unfold differ_pointwise in H0. intros. specialize (H0 j (ltac:(auto))). easy. }
          split.
          { intros. right. subst σ. eexists. reflexivity. }
          split.
          { intros. subst σ. simpl. easy. }
          split.
          { intros. subst σ. eexists. reflexivity. }
          { intros. subst σ. simpl. assert(i <> j) by easy.
            rewrite (eqb_nid _ _ H9). destruct H6. easy. }
        }
      }
    }
    {
      unfold Commit. intros.
      destruct H as [s0 [ρs0 ?]].
      apply SpinLock_Rel_aux3 in H.
      destruct H as [ρ [? [? [? [? ?]]]]].
      destruct H6.
      {
        remember (
          (MkPoss T LockSig (VFU T)
          (inl (LockUnowned))
          (fun k : Name T =>
            match @eqb (Name T) i k
            return (PCall LockSig) with
            | true => @CallDone LockSig unit Rel
            | false => @PCalls T LockSig (VFU T) ρ k
            end)
          (fun k : Name T =>
            match @eqb (Name T) i k
            return (PRet LockSig) with
            | true => @RetPoss LockSig unit Rel tt
            | false => @PRets T LockSig (VFU T) ρ k
            end))) as σ.
        exists (eq σ).
        split. { exists σ. easy. }
        split.
        { intros. subst σ0. exists ρ.
          split. { rewrite H. reflexivity. }
          subst σ.
          destruct ρ.
          destruct_all. simpl in *. subst.
          eapply PossStepsStep.
          4: apply PossStepsRefl.
          { apply PCommitRet with (i := i) (A := unit) (m := Rel) (v := tt); simpl; try easy.
            { constructor. constructor. }
            { rewrite eqb_id. easy. }
            { rewrite eqb_id. easy. }
          }
          { intros. simpl. rewrite (eqb_nid _ _ H). easy. }
          { intros. simpl. rewrite (eqb_nid _ _ H). easy. }
        }
        split.
        { exists ρ, σ.
          subst σ. simpl. rewrite eqb_id. 
          repeat split; try easy.
          left. easy.
        }
        {
          unfold Guar.
          intros.
          pose proof Poss_eq_unique2 _ _ _ H H7. subst ρ0.
          exists σ.
          split; try easy.
          split.
          { unfold differ_pointwise in H0. intros. specialize (H0 j (ltac:(auto))). easy. }
          split.
          { intros.
            rewrite H9 in H6.
            destruct H6.
            inversion H6; subst; contradiction. 
          }
          split.
          { intros. subst σ. simpl. intro. inversion H10; subst; contradiction. }
          split.
          { intros. rewrite H8 in H6. destruct H6. inversion H6. }
          { intros. subst σ. simpl. assert(i <> j) by easy.
            destruct H6. rewrite H6. simpl.
            rewrite (eqb_nid _ _ H9). 
            easy.
          }
        }
      }
      {
        remember
          ((MkPoss T LockSig (VFU T)
          (inr (UBState_, fun j => if i =? j then None else (StateWithUB_acf _ (acf T) (PState ρ) j)))
          (fun j => if i =? j then CallDone Rel else PCalls ρ j)
          (fun j => if i =? j then RetPoss Rel tt else PRets ρ j))) as σ.
        exists (eq σ).
        split. { exists σ. easy. }
        split.
        { intros. subst σ0. exists ρ.
          split. { rewrite H. reflexivity. }
          subst σ.
          destruct ρ.
          destruct_all. simpl in *. subst.
          eapply PossStepsStep.
          4: apply PossStepsRefl.
          { apply PCommitRet with (i := i) (A := unit) (m := Rel) (v := tt); simpl; try easy.
            { constructor. constructor; try rewrite eqb_id; try easy; try apply differ_pointwise_trivial. }
            { rewrite eqb_id. easy. }
            { rewrite eqb_id. easy. }
          }
          { intros. simpl. rewrite (eqb_nid _ _ H). easy. }
          { intros. simpl. rewrite (eqb_nid _ _ H). easy. }
        }
        split.
        { exists ρ, σ.
          subst σ. simpl. rewrite eqb_id. 
          repeat split; try easy.
          right.
          eexists.
          split.
          { reflexivity. }
          { simpl. rewrite eqb_id. easy. }
        }
        {
          unfold Guar.
          intros.
          pose proof Poss_eq_unique2 _ _ _ H H7. subst ρ0.
          exists σ.
          split; try easy.
          split.
          { unfold differ_pointwise in H0. intros. specialize (H0 j (ltac:(auto))). easy. }
          split.
          { intros. right. subst σ. eexists. reflexivity. }
          split.
          { intros. subst σ. simpl. easy. }
          split.
          { intros. subst σ. eexists. reflexivity. }
          { intros. subst σ. simpl. assert(i <> j) by easy.
            rewrite (eqb_nid _ _ H9). destruct H6. easy. }
        }
      }
    }
    {
      unfold sub, subRelt.
      intros.
      rewrite <- LogicFacts.reltCompAssoc in H.
      rename ρ into ρs.
      rename σ into σs.
      assert(Precs i unit Rel s ρs).
      { destruct H as [x1 [x2 [? ?]]].
        destruct H as [x3 [x4 [? ?]]].
        destruct H as [x5 [x6 [? ?]]].
        unfold prComp in H.
        destruct H.
        apply H.
      }
      apply SpinLock_Rel_aux4 in H.
      unfold Posts.
      unfold Precs in H0.
      destruct H0 as [ρ [? ?]].
      destruct H as [σ [? ?]].
      exists ρ, σ.
      split; try easy.
      split; try easy.
      split; try easy.
      destruct H2 as [? [? [? ?]]].
      destruct H5.
      { left. easy. }
      { right. destruct H5 as [a [? ?]]. exists a. easy. }
    }
  + intros.
    constructor.
    easy.
Qed.

Lemma SpinLock_all_verified {T} : 
  forall (i: Name T) A m, 
      VerifyProg i (Rely i) (Guar i) 
      (prComp (Precs i A m) (TInvoke SpinLockImpl i _ m) ->> Rely i)
      (SpinLockImpl _ m)
      (Posts i A m).
Proof.
  intros.
  destruct m.
  + apply SpinLock_Acq_verified.
  + apply SpinLock_Rel_verified.
Qed.

Lemma SpinLock_all_return {T} : 
  forall (i: Name T) A m v, ReturnStep i (Guar i) (Posts i A m v) m v (CSs i A m v).
Proof.
  intros.
  destruct m.
  + admit.
  + unfold ReturnStep.
    intros.
    unfold Posts in H.
    destruct H as [s1 [ρs1 [ρ1 [ρ ?]]]].
    destruct_all.
    exists ρs.
    split.
    { exists ρ. rewrite H1. easy. }
    split.
    { intros. exists σ. split; [exact H5 | constructor]. }
    split.
    { intros. pose proof Poss_eq_unique _ _ _ H1 H5. subst σ. destruct v. easy. }
    split.
    { unfold CSs. 
      exists ρ.
      exists (MkPoss T F (VFU T)
        (PState ρ)
        (fun j => if i =? j then CallIdle else PCalls ρ j)
        (fun j => if i =? j then RetIdle else PRets ρ j)).
      split; [easy |].
      split.
      { extensionality x. apply propositional_extensionality. split; intros.
        { destruct H5 as [σ [? ?]]. pose proof Poss_eq_unique _ _ _ H1 H5. subst σ. destruct v.
          unfold mapRetPoss in H6.
          destruct x. destruct ρ.
          simpl in *.
          destruct_all.
          f_equal.
          { easy. }
          { extensionality j. destruct (classicT (i = j)).
            { subst j. rewrite eqb_id. rewrite H6. easy. }
            { rewrite (eqb_nid _ _ n). unfold differ_pointwise in H10.
              assert(j <> i) by auto.
              specialize (H10 j H13). easy.
            }
          }
          { extensionality j. destruct (classicT (i = j)).
            { subst j. rewrite eqb_id. rewrite H8. easy. }
            { rewrite (eqb_nid _ _ n). unfold differ_pointwise in H11.
              assert(j <> i) by auto.
              specialize (H11 j H13). easy.
            }
          }
        }
        { exists ρ.
          split. { rewrite H1. reflexivity. } 
          unfold mapRetPoss.
          subst x. simpl. rewrite eqb_id.
          destruct v.
          repeat split; try apply differ_pointwise_trivial; easy.
        }
      }
      simpl. rewrite eqb_id.
      repeat split; try apply differ_pointwise_trivial; easy.
    }
    { unfold Guar. intros.
      pose proof Poss_eq_unique2 _ _ _ H1 H5. subst ρ0.
      exists (MkPoss T F (VFU T)
        (PState ρ)
        (fun j => if i =? j then CallIdle else PCalls ρ j)
        (fun j => if i =? j then RetIdle else PRets ρ j)).
      split.
      { extensionality x. apply propositional_extensionality. split; intros.
        { destruct H6 as [σ [? ?]]. pose proof Poss_eq_unique _ _ _ H1 H6. subst σ. destruct v.
          unfold mapRetPoss in H7.
          destruct x. destruct ρ.
          simpl in *.
          destruct_all.
          f_equal.
          { easy. }
          { extensionality j. destruct (classicT (i = j)).
            { subst j. rewrite eqb_id. rewrite H7. easy. }
            { rewrite (eqb_nid _ _ n). unfold differ_pointwise in H11.
              assert(j <> i) by auto.
              specialize (H11 j H14). easy.
            }
          }
          { extensionality j. destruct (classicT (i = j)).
            { subst j. rewrite eqb_id. rewrite H9. easy. }
            { rewrite (eqb_nid _ _ n). unfold differ_pointwise in H12.
              assert(j <> i) by auto.
              specialize (H12 j H14). easy.
            }
          }
        }
        { exists ρ.
          split. { rewrite H1. reflexivity. } 
          unfold mapRetPoss.
          subst x. simpl. rewrite eqb_id.
          destruct v.
          repeat split; try apply differ_pointwise_trivial; easy.
        }
      }
      simpl.
      split.
      { intros. assert(i <> j) by auto. rewrite (eqb_nid _ _ H7). easy. }
      split.
      { intros. left. easy. }
      split.
      { intros. apply H7. }
      split.
      { intros. exists a1. easy. }
      split.
      { assert(i <> j) by auto. rewrite (eqb_nid _ _ H7). easy. }
      split.
      { assert(i <> j) by auto. rewrite (eqb_nid _ _ H7). easy. }
      { reflexivity. }
    }
Admitted.

End SpinLockTest.

Module SpinLockNormal.

Definition E := CASSig bool.
Definition F := LockSig.
Definition VE T : Spec T E:= @casSpec T bool.
Definition VF T := @lockSpec T.
Definition Relt T := Relt (VE T) (VF T).
Definition Prec T := Prec (VE T) (VF T).
Definition Post T := Post (VE T) (VF T).

(* Definition Valid {T} : Prec T :=
  fun s ρs => exists ρ, ρs = eq ρ /\
    ((PState ρ = LockUnowned /\ exists m, snd s = CASDef None m) \/
    (exists j, PState ρ = LockAcqRan j /\ exists m, snd s = CASDef None m) \/
    (exists j, PState ρ = LockOwned j /\ exists m, snd s = CASDef (Some true) m) \/
    (exists j, PState ρ = LockRelRan j /\ exists m, snd s = CASDef (Some true) m)).

Definition Invalid {T} : Prec T :=
  fun s ρs => ~Valid s ρs. *)

Definition Precs {T} i A (m : LockSig A) : Prec T :=
  fun s ρs => exists ρ, ρs = eq ρ /\
    match m with
    | Acq =>
        (PState ρ <> LockOwned i /\ PState ρ <> LockRelRan i /\ PState ρ <> LockAcqRan i)
    | Rel =>
        PState ρ = LockOwned i /\ snd s = CASDef (Some true) None
    end.

Definition Posts {T} i A (m : LockSig A) : Post T A :=
  fun v s ρs t σs => exists ρ σ, ρs = eq ρ /\ σs = eq σ /\
    match m with
    | Acq =>
        (PState σ = LockOwned i /\ PState ρ <> LockOwned i)
    | Rel =>
        PState ρ = LockOwned i /\
        (forall m, PState σ <> LockDef (Some i) m) /\
        σ.(PRets) i = RetPoss m v /\
        σ.(PCalls) i = CallDone m /\
        fst t i = Cont m (Return v)
    end.

Definition Rely {T} i : Relt T :=
  fun s ρs t σs => forall ρ, ρs = eq ρ -> exists σ, σs = eq σ /\
    (PCalls ρ i = PCalls σ i) /\
    (PRets ρ i = PRets σ i) /\
    (forall m, PState ρ = LockDef (Some i) m -> PState σ = LockDef (Some i) m) /\ 
    (forall m, PState ρ = LockDef (Some i) m -> snd s = snd t) /\
    ((forall m, PState ρ <> LockDef (Some i) m) -> (forall m, PState σ <> LockDef (Some i) m)) /\
    (fst s i = fst t i).

Definition Guar {T} i : Relt T :=
  fun s ρs t σs => forall ρ, ρs = eq ρ -> exists σ, σs = eq σ /\
    (forall j, j <> i -> fst s j = fst t j) /\
    (forall j, j <> i -> PCalls ρ j = PCalls σ j) /\
    (forall j, j <> i -> PRets ρ j = PRets σ j) /\
    (forall j, j <> i -> 
      forall m, PState ρ = LockDef (Some j) m -> PState σ = LockDef (Some j) m) /\
    (forall j, j <> i -> 
      forall m, PState ρ = LockDef (Some j) m -> snd s = snd t) /\
    (forall j, j <> i -> 
      ((forall m, PState ρ <> LockDef (Some j) m) -> (forall m, PState σ <> LockDef (Some j) m))).

Lemma SpinLock_R_refl {T} : forall (i : Name T) s ρ, Rely i s ρ s ρ.
Proof.
  unfold Rely; intros.
  exists ρ0.
  split; auto.
  repeat split; intros; auto.
Qed.

Lemma SpinLock_R_trans {T} : 
  forall (i : Name T), Rely i ->> Rely i ==> Rely i.
Proof.
  unfold sub, subRelt.
  intros.
  unfold ReltCompose in H.
  destruct_all.
  rename x into s'.
  rename x0 into ρ'.
  unfold Rely in *.
  intros.
  specialize (H ρ0 H1).
  destruct_all.
  rename x into ρ'_.
  specialize (H0 ρ'_ H).
  destruct_all.
  rename x into σ_.
  exists σ_.
  repeat split; intros; try easy.
Admitted.

Lemma SpinLock_G_in_R {T} : 
  forall (i j : Name T), i <> j -> Guar i ==> Rely j.
Proof.
  unfold Guar, Rely, sub, subRelt. intros.
  specialize (H0 _ H1).
  destruct_all.
  exists x.
  specialize (H2 j (ltac: (easy))).
  specialize (H3 j (ltac: (easy))).
  specialize (H4 j (ltac: (easy))).
  specialize (H5 j (ltac: (easy))).
  specialize (H6 j (ltac: (easy))).
  specialize (H7 j (ltac: (easy))).
  repeat split; intros; try easy.
  + specialize (H5 m).
    apply H5, H8.
  + specialize (H5 m).
    apply (H6 _ H8).
  + apply H7, H8.
Qed.

Lemma Poss_eq_inv: forall {T A VF} (i: Name T) (m : LockSig A) ρs ρ σs (σ: Poss VF),
  ρs = eq ρ ->
  σs = (fun σ  =>
        exists ρ,
        ρs ρ /\
        PState σ = PState ρ /\
        PCalls σ i = CallPoss m /\
        PRets σ i = RetIdle /\
        differ_pointwise (PCalls ρ) (PCalls σ) i /\
        differ_pointwise (PRets ρ) (PRets σ) i) ->
  σ = {| PState := PState ρ; PCalls :=
        fun k : Name T =>
          if i =? k then CallPoss m 
          else PCalls ρ k; PRets :=
        fun k : Name T =>
          if i =? k then RetIdle 
          else PRets ρ k |} ->
  σs = eq σ.
Proof.
  intros.
  rewrite H0, H1.
  extensionality σ'.
  apply propositional_extensionality.
  split.
  { 
    clear H0 H1.
    intros.
    destruct H0 as [ρ' [? [? [? [? [? ?]]]]]].
    assert(ρ = ρ'). { rewrite H in H0. apply H0. }
    subst ρ'.
    destruct σ'; simpl in *.
    apply f_equal3.
    { auto. }
    { 
      extensionality k. destruct (classicT (i = k)).
      { subst k. rewrite eqb_id. auto. }
      { 
        rewrite (eqb_nid _ _ n).
        unfold differ_pointwise in H4.
        specialize (H4 k (ltac:(auto))).
        auto.
      }
    }
    { 
      extensionality k. destruct (classicT (i = k)).
      { subst k. rewrite eqb_id. auto. }
      { 
        rewrite (eqb_nid _ _ n).
        unfold differ_pointwise in H5.
        specialize (H5 k (ltac:(auto))).
        auto.
      }
    }
  }
  {
    intros. subst σ'.
    exists ρ.
    repeat split.
    { rewrite H. reflexivity. }
    { simpl. rewrite eqb_id. reflexivity. } 
    { simpl. rewrite eqb_id. reflexivity. }
    { simpl. apply differ_pointwise_trivial. }
    { simpl. apply differ_pointwise_trivial. }
  }
Qed.

Lemma Poss_eq_inv2: forall {T A VF} (i: Name T) (m : LockSig A) ρs ρ (σs: PossSet VF),
  ρs = eq ρ ->
  σs = (fun σ =>
        exists ρ,
        ρs ρ /\
        PState σ = PState ρ /\
        PCalls σ i = CallPoss m /\
        PRets σ i = RetIdle /\
        differ_pointwise (PCalls ρ) (PCalls σ) i /\
        differ_pointwise (PRets ρ) (PRets σ) i) ->
  σs = eq {| PState := PState ρ; PCalls :=
        fun k : Name T =>
          if i =? k then CallPoss m 
          else PCalls ρ k; PRets :=
        fun k : Name T =>
          if i =? k then RetIdle 
          else PRets ρ k |}.
Proof.
  intros.
  pose proof Poss_eq_inv i m ρs ρ σs 
    {| PState := PState ρ; 
       PCalls := fun j : Name T => if i =? j then CallPoss m else PCalls ρ j; 
       PRets := fun j : Name T => if i =? j then RetIdle else PRets ρ j |} H H0.
    apply H1.
    reflexivity.
Qed.

Lemma Poss_eq_inv3: forall {F T} {VF: Spec T F} (i: Name T) (ρ: Poss VF) σs (st: State VF) pcall pret,
  σs = (fun σ =>
        PState σ = st /\
        PCalls σ i = pcall /\
        PRets σ i = pret /\
        differ_pointwise (PCalls ρ) (PCalls σ) i /\
        differ_pointwise (PRets ρ) (PRets σ) i) ->
  σs = eq ( {| PState := st; 
        PCalls := fun k : Name T => if i =? k then pcall else PCalls ρ k; 
        PRets :=  fun k : Name T => if i =? k then pret else PRets ρ k |} : Poss VF).
Proof.
  intros.
  extensionality σ'.
  apply propositional_extensionality.
  split.
  { 
    intros.
    rewrite H in H0.
    destruct H0 as [? [? [? [? ?]]]].
    destruct σ'; simpl in *.
    unfold differ_pointwise in H3, H4.
    f_equal; try easy.
    { extensionality k.
      destruct (classicT (i = k)).
      { subst k. rewrite eqb_id. auto. }
      { rewrite (eqb_nid _ _ n). specialize (H3 k (ltac:(auto))). auto. }
    }
    { extensionality k.
      destruct (classicT (i = k)).
      { subst k. rewrite eqb_id. auto. }
      { rewrite (eqb_nid _ _ n). specialize (H4 k (ltac:(auto))). auto. }
    }
  }
  {
    intros.
    subst σ'.
    rewrite H.
    simpl.
    rewrite eqb_id.
    repeat split; auto.
    { apply differ_pointwise_trivial. }
    { apply differ_pointwise_trivial. }
  }
Qed.

Lemma Poss_eq_unique: forall {T} ρs (ρ: Poss (VF T)) ρ', 
  ρs = eq ρ -> ρs ρ' -> ρ = ρ'.
Proof.
  intros.
  rewrite H in H0.
  apply H0.
Qed.

Lemma Poss_eq_unique2: forall {T} ρs (ρ: Poss (VF T)) ρ', 
  ρs = eq ρ -> ρs = eq ρ' -> ρ' = ρ.
Proof.
  intros.
  rewrite H in H0.
  assert(eq ρ ρ = eq ρ' ρ). { rewrite H0. reflexivity. }
  rewrite <- H1.
  reflexivity.
Qed.

Lemma SpinLock_Inv_in_R {T} : 
  forall (i j : Name T), i <> j -> InvokeAny SpinLockImpl i ==> Rely j.
Proof.
  unfold InvokeAny, Guar, Rely, sub, subRelt; intros.
  rename σ into σs.
  rename ρ into ρs.
  rename ρ0 into ρ.
  destruct H0 as [Ret [m HInv]].
  unfold TInvoke in HInv.
  destruct HInv as [HIdle [HO [HU Hsig]]].
  set ( σ :=
     {| 
        PState := ρ.(PState); 
        PCalls := fun k =>
          if (eqb i k) then CallPoss m
          else ρ.(PCalls) k;
        PRets := fun k =>
          if (eqb i k) then RetIdle
          else ρ.(PRets) k 
      |}).
  exists σ.
  pose proof Poss_eq_inv i m ρs ρ σs σ H1 Hsig (ltac:(reflexivity)) as H0.
  repeat split; simpl; try rewrite (eqb_nid _ _ H); auto.
  inversion HO; exact (H3 j (ltac:(auto))).
Qed.

Lemma SpinLock_Ret_in_R {T} : 
  forall (i j : Name T), i <> j -> ReturnAny SpinLockImpl i ==> Rely j.
Proof.
  unfold ReturnAny, Guar, Rely, sub, subRelt; intros.
  rename σ into σs.
  rename ρ into ρs.
  rename ρ0 into ρ.
  destruct H0 as [Ret [m HRet]].
  unfold TReturn in HRet.
  destruct HRet as [v [? [? [? ?]]]].
  set ( σ :=
     {| 
        PState := ρ.(PState); 
        PCalls := fun k =>
          if (eqb i k) then CallDone m
          else ρ.(PCalls) k;
        PRets := fun k =>
          if (eqb i k) then RetPoss m v
          else ρ.(PRets) k 
      |}).
  exists σ.
  unfold mapRetPoss in H4.
  repeat split; simpl; try rewrite (eqb_nid _ _ H); auto.
  + rewrite H4.
    extensionality x.
    apply propositional_extensionality.
    admit.
  + inversion H2.
    exact (H6 j (ltac:(auto))).
Admitted.

(* Lemma SpinLock_init_in_P {T} : 
  forall i (A: Type) m, Precs i A m (allIdle, (VE T).(Init)) (eq initPoss).
Proof.
  intros.
  unfold Precs.
  exists initPoss. split; auto.
  destruct m; simpl; intros; try easy.
  split. *)

Lemma SpinLock_P_stable {T} : 
  forall (i: Name T) A m, Stable (Rely i) (Precs i A m).
Proof.
  unfold Stable, stablePrec, PrecCompose, sub, subPrec.
  intros.
  destruct H as [s0 [ρ0 [? ?]]].
  unfold Precs in *.
  unfold Rely in H0.
  destruct m.
  + destruct H as [ρ0' [? ?]].
    specialize (H0 _ H).
    destruct H0 as [ρ' [? ?]].
    exists ρ'. split; auto.
    destruct_all.
    assert((forall m : option(LockSig unit), PState ρ0' <> LockDef (Some i) m)). {
      intros.
      unfold LockOwned, LockRelRan, LockAcqRan in *.
      destruct m; try easy.
      dependent destruction l; easy.
    }
    specialize (H6 H10).
    pose proof (H10 None).
    pose proof (H10 (Some Rel)).
    pose proof (H10 (Some Acq)).
    unfold LockOwned, LockRelRan, LockAcqRan.
    repeat split; easy.
  + destruct H as [ρ0' [? ?]].
    specialize (H0 _ H).
    destruct H0 as [ρ' [? ?]].
    exists ρ'. split; auto.
    destruct_all.
    specialize (H4 None).
    specialize (H4 H1).
    split; [exact H4 | ].
    assert(snd s0 = snd s). {
      specialize (H5 None).
      apply H5, H1.
    }
    rewrite <- H9.
    apply H8.
Qed.

(* Lemma SpinLock_Q_stable {T} : 
  forall (i: Name T) A m, Stable (Rely i) (Posts i A m).
Proof.
  unfold Stable, stablePost, stableRelt, sub, subRelt, ReltCompose.
  intros.
  destruct H as [t0 [σ0 [? ?]]].
  unfold Posts in *.
  unfold Rely in H0.
  intros.
  specialize (H _ H1).
  destruct H as [σ0' [? ?]].
  specialize (H0 _ H).
  destruct H0 as [σ' [? ?]].
  exists σ'. split; [exact H0 | ].
  destruct m.
  + destruct_all.
    specialize (H5 None).
    pose proof (proj1 H5 H2).
    easy.
  + destruct_all.
    specialize (H5 None).
    pose proof (proj1 H5).
    repeat split; try easy.
    { apply (proj1 H7 H9). }
    { rewrite <- H4. apply H10. }
    { rewrite <- H3. apply H11. }
    { rewrite <- H12, H8. reflexivity. }
Qed. *)

(* Lemma SpinLock_switch_code {T} : 
  forall (i: Name T) A m1 B m2 v,
    (prComp (Precs i A m1) (Posts i A m1 v)) <<- (Posts i A m1 v) <<- TReturn SpinLockImpl i m1 v ==> Precs i B m2.
Proof.
  intros.
  unfold sub, subPrec, subRelt, ReltCompose, PrecCompose.
  intros.
  destruct H as [s1 [ρ1 [? ?]]].
  destruct H as [s2 [ρ2 [? ?]]].
Admitted. *)

Lemma Rel_verify_aux' {T} :
  forall (i: Name T) (s0: InterState F (VE T)) (ρs0: PossSet (VF T)) s1 ρs1,
    (prComp (Precs i unit Rel) (TInvoke SpinLockImpl i unit Rel)) s0 ρs0 s1 ρs1 ->
      exists ρ1, ρs1 = eq ρ1 /\
        PState ρ1 = LockOwned i /\
        PCalls ρ1 i = CallPoss Rel /\
        PRets ρ1 i = RetIdle /\
        snd s1 = CASDef (Some true) None /\
        fst s1 i = Cont Rel (SpinLockImpl _ Rel).
Proof.
  intros.
  unfold prComp, ReltCompose in H.
  destruct H.
  unfold Precs in H.
  destruct H as [ρ [? [? ?]]].
  unfold TInvoke in H0.
  destruct H0 as [? [? [? ?]]].
  exists {| 
    PState := ρ.(PState); 
    PCalls := fun j =>
      if (eqb i j) then CallPoss Rel
      else ρ.(PCalls) j;
    PRets := fun j =>
      if (eqb i j) then RetIdle
      else ρ.(PRets) j
  |}.
  simpl.
  rewrite (eqb_id i).
  rewrite <- H2.
  unfold TIdle in H0.
  destruct H0.
  split.
  { pose proof Poss_eq_inv i Rel ρs0 ρ ρs1 
    {| PState := PState ρ; 
       PCalls := fun j : Name T => if i =? j then CallPoss Rel else PCalls ρ j; 
       PRets := fun j : Name T => if i =? j then RetIdle else PRets ρ j |} H H5.
    apply H7.
    reflexivity. }
  repeat split; try easy.
  inversion H3; subst; simpl in *.
  inversion H7; subst.
  dependent destruction H5.
  exact H12.
Qed.

Lemma Rel_verify_aux {T} :
  forall (i: Name T) (s0: InterState F (VE T)) (ρs0: PossSet (VF T)) s1 ρs1,
    (prComp (Precs i unit Rel) (TInvoke SpinLockImpl i unit Rel) ->> Rely i) s0 ρs0 s1 ρs1 ->
      exists ρ1, ρs1 = eq ρ1 /\
        PState ρ1 = LockOwned i /\
        PCalls ρ1 i = CallPoss Rel /\
        PRets ρ1 i = RetIdle /\
        snd s1 = CASDef (Some true) None /\  
        fst s1 i = Cont Rel (SpinLockImpl _ Rel).
Proof.
  intros.
  unfold ReltCompose in H.
  destruct H as [s2 [ρs2 [? ?]]].
  pose proof Rel_verify_aux' i s0 ρs0 s2 ρs2 H.
  destruct H1 as [ρ2 [? [? [? [? [? ?]]]]]].
  unfold Rely in H0.
  specialize (H0 _ H1).
  destruct H0 as [ρ1 [? ?]].
  destruct_all.
  exists ρ1.
  split; [exact H0 | ].
  split; [apply (H9 None H2) |].
  split.
  { rewrite <- H7. apply H3. }
  split.
  { rewrite <- H8. apply H4. }
  split. 
  { pose proof (H10 None H2). rewrite <- H13. apply H5. }
  rewrite <- H12. apply H6.
Qed.

Lemma Rel_verify_aux'' {T} :
  forall (i: Name T) (s0: InterState F (VE T)) (ρs0: PossSet (VF T)) s1 ρs1,
    (prComp (Precs i unit Rel) (TInvoke SpinLockImpl i unit Rel) ->> Rely i) s0 ρs0 s1 ρs1 ->
      exists ρ0, ρs0 = eq ρ0 /\ PState ρ0 = LockOwned i /\ snd s0 = CASDef (Some true) None.
Proof.
  intros.
  unfold prComp, ReltCompose in H.
  destruct_all.
  unfold Precs in H.
  unfold PrecToRelt in H.
  apply H.
Qed.

Lemma differ_pointwise_trans {A State} : forall (i: A) s1 s2 (s3: (A -> State)),
  differ_pointwise s1 s2 i -> differ_pointwise s2 s3 i -> differ_pointwise s1 s3 i.
Proof.
  intros.
  unfold differ_pointwise in *.
  intros.
  specialize (H j H1).
  specialize (H0 j H1).
  auto.
  rewrite H0, H.
  reflexivity.
Qed.

Lemma SpinLock_Rel_verified {T} : 
  forall (i: Name T),
    VerifyProg i (Rely i) (Guar i)
      (prComp (Precs i unit Rel) (TInvoke SpinLockImpl i _ Rel) ->> Rely i)
      (SpinLockImpl _ Rel)
      (fun v => Posts i unit Rel v).
Proof.
  intros. simpl.
  unfold SpinLockRel.
  apply (lemBind (fun (_: bool) => 
            (fun v : unit => Posts i unit Rel v) tt)).
  + eapply weakenPost.
    eapply (lemCall 
      (Q := fun (s: InterState F (VE T)) (ρs: PossSet (VF T)) t σs =>
        exists ρ σ, ρs = eq ρ /\ σs = eq σ /\
        UnderThreadStep (fst s i) (Some (CallEv (CAS (Some true) None))) (fst t i) /\
        Step (VE T) (snd s) (i, (CallEv (CAS (Some true) None))) (snd t) /\ 
        PState σ = LockRelRan i /\
        PCalls σ i = CallDone Rel /\
        PRets σ i = RetIdle /\
        True /\ True)   (* The following conditions are removed. Use True /\ True to avoid label changes  *)
        (* (forall j, j <> i -> PCalls σ j = PCalls ρ j) /\
        (forall j, j <> i -> PRets σ j = PRets ρ j)) *)
      (S := fun v s ρs t σs =>
        exists ρ σ, ρs = eq ρ /\ σs = eq σ /\ v = true /\
        UnderThreadStep (fst s i) (Some (RetEv (CAS (Some true) None) true)) (fst t i) /\
        (forall m, PState σ <> LockDef (Some i) m) /\
        PCalls σ i = CallDone Rel /\
        PRets σ i = RetPoss Rel tt /\
        True /\ True)).   (* The following conditions are removed. Use True /\ True to avoid label changes  *)
        (* (forall j, j <> i -> PCalls σ j = PCalls ρ j) /\
        (forall j, j <> i -> PRets σ j = PRets ρ j))). *)
    {
      unfold Stable, stableRelt, sub, subRelt.
      intros; simpl in *.
      unfold ReltCompose in H.
      rename ρ into ρs.
      rename σ into σs.
      destruct H as [s0 [ρs0 [? ?]]].
      destruct H as [ρ [ρ0 [? [? ?]]]].
      unfold Rely in H0.
      specialize (H0 _ H1).
      destruct H0 as [σ [? ?]].
      exists ρ, σ.
      split; [exact H |].
      split; [exact H0 |].
      destruct_all.
      change (@fst (ThreadsSt T E F) (CASState T bool) t i) with 
        (@fst (ThreadsSt T E LockSig) (@State T E (VE T)) t i).
      rewrite <- H8.
      split; [exact H2 |].
      specialize (H6 _ H10).
      change (@snd (ThreadsSt T E F) (CASState T bool) t) with 
        (@snd (ThreadsSt T E LockSig) (@State T E (VE T)) t).
      rewrite <- H6.
      split; [ exact H9 |].
      split; [ apply (H5 (Some Rel) H10) |].
      split.
      { unfold F in H11. rewrite H11 in H3. unfold F. rewrite H3. reflexivity. }
      split.
      { unfold F in H12. rewrite H12 in H4. unfold F. rewrite H4. reflexivity. }
      easy.
    }
    { 
      unfold Stable, stablePost, stableRelt, sub, subRelt.
      intros; simpl in *.
      unfold ReltCompose in H.
      rename ρ into ρs.
      rename σ into σs.
      destruct H as [s0 [ρs0 [? ?]]].
      destruct H as [ρ [ρ0 [? [? ?]]]].
      unfold Rely in H0.
      specialize (H0 _ H1).
      destruct H0 as [σ [? ?]].
      exists ρ, σ.
      split; [exact H |].
      split; [exact H0 |].
      destruct_all.
      split; [exact H2 |].
      change (@fst (ThreadsSt T E F) (CASState T bool) t i) with 
        (@fst (ThreadsSt T E LockSig) (@State T E (VE T)) t i).
      rewrite <- H8.
      split; [exact H9 |].
      split; [apply H7, H10 |].
      split.
      { unfold F in H11. rewrite H11 in H3. unfold F. rewrite H3. reflexivity. }
      split.
      { unfold F in H12. rewrite H12 in H4. unfold F. rewrite H4. reflexivity. }
      easy.
    }
    { 
      unfold Commit.
      intros.
      unfold ReltToPrec in H.
      destruct H as [s0 [ρs0 ?]].
      pose proof Rel_verify_aux i s0 ρs0 s ρs H.
      destruct H3 as [ρ [? ?]].
      destruct_all.
      remember
      (fun σ: Poss (VF T) => 
        PState σ = LockRelRan i /\
        PCalls σ i = CallDone Rel /\
        PRets σ i = RetIdle /\
        differ_pointwise (PCalls ρ) (PCalls σ) i /\
        differ_pointwise (PRets ρ) (PRets σ) i) as σs.
      pose proof Poss_eq_inv3 _ _ _ _ _ _ Heqσs.
      remember (
        (MkPoss T LockSig (VF T)
        (@LockRelRan (Name T) i)
        (fun k : Name T =>
      match @eqb (Name T) i k
      return (PCall LockSig) with
      | true => @CallDone LockSig unit Rel
      | false => @PCalls T LockSig (VF T) ρ k
      end)
        (fun k : Name T =>
      match @eqb (Name T) i k
      return (PRet LockSig) with
      | true => @RetIdle LockSig
      | false => @PRets T LockSig (VF T) ρ k
      end))) as σ.
      exists σs.
      split. { exists σ. rewrite H9. reflexivity. }
      split. 
      { intros. exists ρ. 
        pose proof Poss_eq_unique _ _ _ H9 H10; subst σ0. 
        split. { rewrite H3. reflexivity. }
        apply (PossStepsStep i ρ σ σ).
        { apply (PCommitCall i _ _ unit Rel); subst σ; simpl; try easy.
          { rewrite H4. constructor. }
          { rewrite eqb_id. reflexivity. }
          { rewrite eqb_id. reflexivity. }
        }
        { intros. subst σ. simpl. rewrite (eqb_nid _ _ H11). reflexivity. }
        { intros. subst σ. simpl. rewrite (eqb_nid _ _ H11). reflexivity. }
        { constructor. }
      }
      split.
      { exists ρ, σ.
        repeat split; subst σ; simpl; try rewrite eqb_id; try easy.
        (* { intros. rewrite (eqb_nid i j (ltac:(auto))). reflexivity. }
        { intros. rewrite (eqb_nid i j (ltac:(auto))). reflexivity. } *)
      }
      unfold Guar.
      intros.
      pose proof Poss_eq_unique2 _ _ _ H3 H10; subst ρ0.
      exists σ.
      split; [exact H9 |].
      unfold differ_pointwise in H0.
      split. { intros. specialize (H0 _ H11); easy. }
      split.
      { intros. subst σ. simpl. rewrite (eqb_nid i j (ltac:(auto))). reflexivity. }
      split.
      { intros. subst σ. simpl. rewrite (eqb_nid i j (ltac:(auto))). reflexivity. }
      split.
      { intros. subst σ; simpl. rewrite H4 in H12. inversion H12; subst j; contradiction. }
      split.
      { intros. subst σ; simpl.
        rewrite H4 in H12. inversion H12; subst j; contradiction. }
      intros.
      subst σ; intros; simpl.
      { unfold LockRelRan. intro. inversion H13; subst; contradiction. }
    }
    {
      unfold Commit; intros.
      unfold ReltToPrec in H.
      destruct H as [s0 [ρs0 ?]].
      unfold ReltCompose in H at 1.
      destruct H as [s1 [ρs1 ?]].
      destruct H.
      pose proof Rel_verify_aux i s0 ρs0 s1 ρs1 H.
      clear H.
      destruct H4 as [ρ1 [? ?]].
      destruct_all.
      assert(ρ1 = x). { apply (Poss_eq_unique2 _ _ _ H3 H). }
      subst x.
      rename x0 into ρ.
      remember
      (fun σ: Poss (VF T) => 
        PState σ = LockUnowned /\
        PCalls σ i = CallDone Rel /\
        PRets σ i = RetPoss Rel tt /\
        differ_pointwise (PCalls ρ) (PCalls σ) i /\
        differ_pointwise (PRets ρ) (PRets σ) i) as σs.
      pose proof Poss_eq_inv3 _ _ _ _ _ _ Heqσs.
      remember
      (MkPoss T LockSig (VF T) (@LockUnowned (Name T))
      (fun k : Name T =>
      match @eqb (Name T) i k return (PCall LockSig) with
      | true => @CallDone LockSig unit Rel
      | false => @PCalls T LockSig (VF T) ρ k
      end)
        (fun k : Name T =>
      match @eqb (Name T) i k return (PRet LockSig) with
      | true => @RetPoss LockSig unit Rel tt
      | false => @PRets T LockSig (VF T) ρ k
      end)) as σ.
      exists σs.
      split. { exists σ. rewrite H17; reflexivity. } 
      split.
      { intros. pose proof Poss_eq_unique _ _ _ H17 H18; subst σ0. 
        exists ρ. split; [rewrite H9; reflexivity |].
        apply (PossStepsStep i ρ σ σ).
        { apply (PCommitRet i _ _ unit Rel tt); subst σ; simpl; try easy.
          { unfold F in H12. rewrite H12. constructor. }
          { rewrite eqb_id. reflexivity. }
          { rewrite eqb_id. reflexivity. }
        }
        { intros. subst σ. simpl. rewrite (eqb_nid _ _ H19). reflexivity. }
        { intros. subst σ. simpl. rewrite (eqb_nid _ _ H19). reflexivity. }
        { constructor. }
      }
      split.
      { exists ρ, σ.
        assert(v = true).
        { unfold F in H11.
          rewrite H7 in H11.
          inversion H11; subst.
          change (@snd (ThreadsSt T E F) (@State T E (VE T)) s) with 
            (@snd (ThreadsSt T E LockSig) (CASState T bool) s) in H2.
          rewrite <- H23 in H2.
          inversion H2; subst.
          { dependent destruction H21; easy. }
          { contradiction. }
        }
        subst v.
        repeat split; subst σ; simpl; try rewrite eqb_id; try easy.
        (* { intros. rewrite (eqb_nid i j (ltac:(auto))). reflexivity. }
        { intros. rewrite (eqb_nid i j (ltac:(auto))). reflexivity. } *)
      }
      unfold Guar.
      intros.
      pose proof Poss_eq_unique2 _ _ _ H18 H9; subst ρ0.
      exists σ.
      split; [exact H17 |]. 
      split.
      { unfold differ_pointwise in H0. intros. specialize (H0 _ H19); easy. }
      split.
      { subst σ. simpl. intros. rewrite (eqb_nid i j (ltac:(auto))). reflexivity. }
      split.
      { subst σ. simpl. intros. rewrite (eqb_nid i j (ltac:(auto))). reflexivity. }
      split.
      { subst σ. simpl. unfold F in H12. rewrite H12.
        intros; inversion H20; subst j; contradiction. }
      split.
      { subst σ. simpl. unfold F in H12. rewrite H12. intros. inversion H20; subst j; contradiction. }
      intros.
      subst σ; intros; simpl.
      { unfold LockUnowned. intro. inversion H21; subst; contradiction. }
    }
    {
      unfold sub, subRelt.
      intros.
      unfold ReltToPrec in H.
      rename ρ into ρs.
      rename σ into σs.
      destruct H as [s0 [ρs0 ?]].
      unfold ReltCompose in H at 2.
      destruct H.
      pose proof Rel_verify_aux i s ρs s0 ρs0 H.
      destruct H1 as [ρ0 [? ?]].
      destruct H0 as [s1 [ρs1 ?]].
      destruct H0.
      destruct H0 as [ρ0_ [ρ1 [? [? ?]]]].
      pose proof Poss_eq_unique2 _ _ _ H0 H1; subst ρ0_.
      destruct H3 as [ρ1_ [σ [? [? ?]]]].
      pose proof Poss_eq_unique2 _ _ _ H3 H4; subst ρ1_.
      unfold Posts. intros.
      pose proof Rel_verify_aux'' i s ρs s0 ρs0 H.
      destruct H8 as [ρ [? ?]].
      exists ρ, σ.
      split; [exact H8 |].
      split; [exact H6 |].
      split; [exact (proj1 H9) |].
      destruct_all.
      split; [exact H16 |].
      split; [exact H18|].
      split; [exact H17 |].
      unfold F in H5. rewrite H14 in H5.
      inversion H5; subst.
      dependent destruction H30.
      unfold F in H15. rewrite H32 in H15.
      inversion H15; subst.
      dependent destruction H8.
      unfold call, ret in x.
      dependent destruction x.
      rewrite ProgramFacts.frobProgId in x at 1. unfold ProgramFacts.frobProgram in x. simpl in x.
      inversion x.
      dependent destruction H1.
      rewrite H29.
      rewrite (ProgramFacts.frobProgId (@Return (CASSig bool) bool true;; Return tt)).
      unfold ProgramFacts.frobProgram.
      simpl. reflexivity.
    }
  + intros.
    apply lemRet.
    intros.
    destruct v0.
    easy.
Qed.

Lemma SpinLock_Acq_verified {T} : 
  forall (i: Name T),
    VerifyProg i (Rely i) (Guar i)
      (prComp (Precs i unit Acq) (TInvoke SpinLockImpl i _ Acq) ->> Rely i)
      (SpinLockImpl _ Acq)
      (fun v => Posts i unit Acq v).
Proof.
  intros.
  simpl.
  unfold SpinLockAcq.
Admitted.

Lemma SpinLock_all_verified {T} : 
  forall (i: Name T) A m,
    VerifyProg i (Rely i) (Guar i)
      (prComp (Precs i A m) (TInvoke SpinLockImpl i _ m) ->> Rely i)
      (SpinLockImpl _ m)
      (fun v => Posts i A m v).
Proof.
  intros.
  destruct m eqn : I.
  + apply SpinLock_Acq_verified.
  + apply SpinLock_Rel_verified.
Qed.

End SpinLockNormal.




Module SpinLockUB.

Definition E := CASSig bool.
Definition F := LockSig.
Definition acf T := @LockActiveMap T.
Definition HAcf T : @acf_sound T F lockSpec (acf T) := @LockActiveMapSound T.
Definition VE T : Spec T E:= @casSpec T bool.
Definition VF T := @lockSpec T.
Definition VFU T := SpecWithUB (@lockSpec T) (acf T) (HAcf T).
Definition ReltU T := Relt (VE T) (VFU T).
Definition Relt T := Relt (VE T) (VF T).
Definition PrecU T := Prec (VE T) (VFU T).
Definition Prec T := Prec (VE T) (VF T).
Definition PostU T := Post (VE T) (VFU T).
Definition Post T := Post (VE T) (VF T).
Definition UState T := State (VFU T).

Definition Precs {T} i A (m : LockSig A) : @PrecU T :=
  fun s ρs => exists ρ, ρs = eq ρ /\
    match m with
    | Acq =>
        PState ρ = inl (LockOwned i) \/ 
        PState ρ = inl (LockRelRan i) \/ 
        PState ρ = inl (LockAcqRan i) \/
        exists a, PState ρ = inr (UBState_, a)
    | Rel =>
        PState ρ <> inl (LockOwned i) /\
        (StateWithUB_acf _ (acf T) (PState ρ) i = None)
    end.

Definition Posts {T} i A (m : LockSig A) : @PostU T A :=
  fun _ s ρs t σs => exists ρ σ, ρs = eq ρ /\ σs = eq σ /\
    match m with
    | Acq =>
        exists a, PState σ = inr (UBState_, a) /\
        PCalls σ i = CallDone Acq /\
        PRets σ i = RetPoss Acq tt
    | Rel =>
        exists a, PState σ = inr (UBState_, a) /\
        PCalls σ i = CallDone Rel /\
        PRets σ i = RetPoss Rel tt
    end.

(* Definition Rely {T} i := ReltWithUB (VF := (VF T)) (acf T) (HAcf T) (SpinLockNormal.Rely i).
Definition Guar {T} i := ReltWithUB (VF := (VF T)) (acf T) (HAcf T) (SpinLockNormal.Guar i).
Ltac unfold_rely H := unfold Rely, ReltWithUB, SpinLockNormal.Rely in H.
Ltac unfold_guar H := unfold Guar, ReltWithUB, SpinLockNormal.Guar in H. *)

Definition Rely {T} i : ReltU T :=
  fun s ρs t σs => forall ρ, ρs = eq ρ -> exists σ, σs = eq σ /\
    (PCalls ρ i = PCalls σ i) /\
    (PRets ρ i = PRets σ i) /\
    (forall m, PState ρ = inl (LockDef (Some i) m) -> 
      (PState σ = inl (LockDef (Some i) m) \/ 
      (exists a, PState σ = inr (UBState_, a)))) /\
    True /\
    (* (forall m, PState ρ = inl (LockDef (Some i) m) -> snd s = snd t) /\ *)
    ((forall m, PState ρ <> inl (LockDef (Some i) m)) -> (forall m, PState σ <> inl (LockDef (Some i) m))) /\
    ((exists a, PState ρ = inr (UBState_, a)) -> (exists a', PState σ = inr (UBState_, a'))) /\
    (fst s i = fst t i) /\
    (StateWithUB_acf _ (acf T) (PState ρ) i = StateWithUB_acf _ (acf T) (PState σ) i).

Definition Guar {T} i : ReltU T :=
  fun s ρs t σs => forall ρ, ρs = eq ρ -> exists σ, σs = eq σ /\
    (forall j, j <> i -> fst s j = fst t j) /\
    (forall j, j <> i -> PCalls ρ j = PCalls σ j) /\
    (forall j, j <> i -> PRets ρ j = PRets σ j) /\
    (forall j, j <> i ->
      forall m, PState ρ = inl (LockDef (Some j) m) ->
        (PState σ = inl (LockDef (Some j) m) \/ 
        (exists a, PState σ = inr (UBState_, a)))) /\
    True /\
    (* (forall j, j <> i -> 
      forall m, PState ρ = inl (LockDef (Some j) m) -> snd s = snd t) /\ *)
    (forall j, j <> i -> 
      ((forall m, PState ρ <> inl (LockDef (Some j) m)) -> (forall m, PState σ <> inl (LockDef (Some j) m)))) /\
    ((exists a, PState ρ = inr (UBState_, a)) -> (exists a', PState σ = inr (UBState_, a'))) /\
    (forall j, j <> i -> (StateWithUB_acf _ (acf T) (PState ρ) j = StateWithUB_acf _ (acf T) (PState σ) j)).

Lemma Poss_eq_unique: forall {T} ρs (ρ: Poss (VFU T)) ρ', 
  ρs = eq ρ -> ρs ρ' -> ρ = ρ'.
Proof.
  intros.
  rewrite H in H0.
  apply H0.
Qed.

Lemma Poss_eq_unique2: forall {T} ρs (ρ: Poss (VFU T)) ρ', 
  ρs = eq ρ -> ρs = eq ρ' -> ρ' = ρ.
Proof.
  intros.
  rewrite H in H0.
  assert(eq ρ ρ = eq ρ' ρ). { rewrite H0. reflexivity. }
  rewrite <- H1.
  reflexivity.
Qed.

Lemma SpinLock_G_in_R {T} : 
  forall (i j : Name T), i <> j -> Guar i ==> Rely j.
Proof.
  unfold Guar, Rely, sub, subRelt.
  intros.
  specialize (H0 _ H1).
  destruct_all.
  rename ρ into ρs.
  rename σ into σs.
  rename x into σ.
  rename ρ0 into ρ.
  exists σ.
  assert(j <> i) by auto.
  specialize (H2 _ H10).
  specialize (H3 _ H10).
  specialize (H4 _ H10).
  specialize (H5 _ H10).
  specialize (H7 _ H10).
  specialize (H9 _ H10).
  repeat split; intros; simpl; try easy.
  + specialize (H5 _ H11).
    destruct H5.
    - left. easy.
    - right. destruct_all. exists x. apply H5.
  + specialize (H7 H11).
    apply H7.
  + apply (H8 H11).
Qed.

Lemma Rel_verify_aux1 {T} :
  forall (i: Name T) (s0: InterState F (VE T)) (ρs0: PossSet (VFU T)) s1 ρs1,
    (prComp (Precs i unit Rel) (TInvoke SpinLockImpl i unit Rel)) s0 ρs0 s1 ρs1 ->
      exists ρ1, ρs1 = eq ρ1 /\
        PState ρ1 <> inl (LockOwned i) /\
        (StateWithUB_acf _ (acf T) (PState ρ1) i = None) /\
        PCalls ρ1 i = CallPoss Rel /\
        PRets ρ1 i = RetIdle /\
        fst s1 i = Cont Rel (SpinLockImpl _ Rel).
Proof.
  intros.
  unfold prComp, ReltCompose in H.
  destruct H.
  unfold Precs in H.
  destruct H as [ρ0 [? ?]].
  unfold TInvoke in H0.
  destruct H0 as [? [? [? ?]]].
  exists {| 
    PState := ρ0.(PState); 
    PCalls := fun j =>
      if (eqb i j) then CallPoss Rel
      else ρ0.(PCalls) j;
    PRets := fun j =>
      if (eqb i j) then RetIdle
      else ρ0.(PRets) j
  |}.
  simpl.
  rewrite (eqb_id i).
  unfold TIdle in H0.
  destruct H0.
  split.
  { pose proof SpinLockNormal.Poss_eq_inv i Rel ρs0 ρ0 ρs1
    {| PState := PState ρ0; 
       PCalls := fun j : Name T => if i =? j then CallPoss Rel else PCalls ρ0 j; 
       PRets := fun j : Name T => if i =? j then RetIdle else PRets ρ0 j |} H H4.
    apply H6.
    reflexivity. }
  repeat split; try easy.
  inversion H2; subst; simpl in *.
  inversion H6; subst.
  dependent destruction H4.
  exact H11.
Qed.

Lemma LockUnowned_Rely {T} :
  forall (i: Name T) (s0: InterState F (VE T)) (ρs0: PossSet (VFU T)) s1 ρs1 ρ0,
    ρs0 = eq ρ0 ->
    Rely i s0 ρs0 s1 ρs1 ->
    PState ρ0 <> inl (LockOwned i) ->
    (exists ρ1, (ρs1 = eq ρ1) /\ PState ρ1 <> inl (LockOwned i)).
Proof.
  intros.
  unfold Rely in H0.
  specialize (H0 _ H).
  destruct_all.
  rename x into ρ1.
  exists ρ1.
  split; [exact H0 |].
  destruct (PState ρ0).
  + destruct s as [j m].
    destruct j.
    - rename n into j.
      destruct (classicT (i = j)).
      * subst j.
        specialize (H4 m (ltac:(auto))).
        destruct m.
        { destruct H4.
          rewrite H4. easy. 
          destruct_all.
          rewrite H4. easy.
        }
        contradiction.
      * apply H6. intros. intro.
        inversion H10. rewrite H12 in n. contradiction.
    - apply H6. easy.
  + assert(forall m : option (LockSig unit), inr p <> inl (LockDef (Some i) m)) by (intros; easy).
    apply (H6 H10).
Qed.

Lemma Rel_verify_aux2 {T} :
  forall (i: Name T) (s0: InterState F (VE T)) (ρs0: PossSet (VFU T)) s1 ρs1,
    (prComp (Precs i unit Rel) (TInvoke SpinLockImpl i unit Rel) ->> Rely i) s0 ρs0 s1 ρs1 ->
      exists ρ1, ρs1 = eq ρ1 /\
        PState ρ1 <> inl (LockOwned i) /\
        (StateWithUB_acf _ (acf T) (PState ρ1) i = None) /\
        PCalls ρ1 i = CallPoss Rel /\
        PRets ρ1 i = RetIdle /\
        fst s1 i = Cont Rel (SpinLockImpl _ Rel).
Proof.
  intros.
  unfold ReltCompose in H.
  destruct H as [s2 [ρs2 [? ?]]].
  pose proof Rel_verify_aux1 i s0 ρs0 s2 ρs2 H.
  destruct H1 as [ρ2 [? [? [? [? ?]]]]].
  pose proof LockUnowned_Rely _ _ _ _ _ _ H1 H0 H2.
  unfold Rely in H0.
  specialize (H0 _ H1).
  destruct H0 as [ρ1 [? ?]].
  destruct_all.
  pose proof Poss_eq_unique2 _ _ _ H6 H0; subst x.
  exists ρ1.
  split; [exact H0 | ].
  split; [exact H16 |].
  split.
  { rewrite <- H15. apply H3. }
  split.
  { rewrite <- H7. apply H4. }
  split.
  { rewrite <- H9. apply H5. }
  rewrite <- H14. apply H8.
Qed.

Lemma Rel_verify_aux3 {T} :
  forall (i: Name T) (s0: InterState F (VE T)) (ρs0: PossSet (VFU T)) s1 ρs1,
    ((prComp (Precs i unit Rel) (TInvoke SpinLockImpl i unit Rel) ->> Rely i) ->>
    (fun s ρs t σs =>
        exists ρ σ, ρs = eq ρ /\ σs = eq σ /\
        UnderThreadStep (fst s i) (Some (CallEv (CAS (Some true) None))) (fst t i) /\
        (exists a, PState σ = inr (UBState_, a) /\ (a i = Some (existT (fun A => LockSig A) unit Rel))) /\
        PCalls σ i = CallDone Rel /\
        PRets σ i = RetIdle)) s0 ρs0 s1 ρs1 -> 
    exists ρ1, ρs1 = eq ρ1 /\
      (exists a, PState ρ1 = inr (UBState_, a) /\ (a i = Some (existT (fun A => LockSig A) unit Rel))) /\
      PCalls ρ1 i = CallDone Rel /\
      PRets ρ1 i = RetIdle /\
      fst s1 i = UCall Rel (CAS (Some true) None) (fun x1 : bool => Return x1;; Return tt).
Proof.
  intros.
  unfold ReltCompose in H at 1.
  destruct H as [s2 [ρs2 [? ?]]].
  pose proof Rel_verify_aux2 i s0 ρs0 s2 ρs2 H.
  destruct H1 as [ρ2 [? [? [? [? ?]]]]].
  destruct H0 as [ρ2' [ρ1 [? [? ?]]]].
  pose proof Poss_eq_unique2 _ _ _ H0 H1; subst ρ2'.
  exists ρ1.
  split; [exact H6 |].
  destruct_all.
  split. { exists x. easy. }
  split; [exact H10 |].
  split; [exact H11 |].
  rewrite H8 in H7.
  inversion H7; subst.
  dependent destruction H14.
  unfold call, ret in x.
  rewrite ProgramFacts.frobProgId in x at 1. unfold ProgramFacts.frobProgram in x. simpl in x.
  inversion x.
  dependent destruction H6.
  rewrite H18.
  reflexivity.
Qed.

Lemma Rel_verify_aux4 {T} :
  forall (i: Name T) (s0: InterState F (VE T)) (ρs0: PossSet (VFU T)) s1 ρs1 v,
    (((prComp (Precs i unit Rel) (TInvoke SpinLockImpl i unit Rel) ->> Rely i) ->>
    (fun (s: InterState F (VE T)) (ρs: PossSet (VFU T)) t σs =>
        exists ρ σ, ρs = eq ρ /\ σs = eq σ /\
        UnderThreadStep (fst s i) (Some (CallEv (CAS (Some true) None))) (fst t i) /\
        (exists a, PState σ = inr (UBState_, a) /\ (a i = Some (existT (fun A => LockSig A) unit Rel))) /\
        PCalls σ i = CallDone Rel /\
        PRets σ i = RetIdle)) ->>
    (fun s ρs t (σs: PossSet (VFU T)) =>
        exists ρ σ, ρs = eq ρ /\ σs = eq σ /\
        UnderThreadStep (fst s i) (Some (RetEv (CAS (Some true) None) v)) (fst t i) /\
        (exists a, PState σ = inr (UBState_, a) /\ a i = None) /\
        PCalls σ i = CallDone Rel /\
        PRets σ i = RetPoss Rel tt)) s0 ρs0 s1 ρs1 -> 
    exists ρ1, ρs1 = eq ρ1 /\
        fst s1 i = Cont Rel (Return tt) /\
        (exists a, PState ρ1 = inr (UBState_, a) /\ a i = None) /\
        PCalls ρ1 i = CallDone Rel /\
        PRets ρ1 i = RetPoss Rel tt.
Proof.
  intros.
  unfold ReltCompose in H at 1.
  destruct H as [t [σs [? ?]]].
  pose proof Rel_verify_aux3 i s0 ρs0 t σs H.
  clear H.
  destruct H1 as [σ [? ?]].
  destruct_all.
  rename x into a.
  rename x0 into σ'.
  rename x1 into ρ1.
  pose proof Poss_eq_unique2 _ _ _ H0 H; subst σ'.
  exists ρ1.
  destruct_all.
  split; [exact H6 |].
  split.
  { rewrite H4 in H7. inversion H7; subst.
    dependent destruction H13.
    dependent destruction H16.
    rewrite H18.
    rewrite (ProgramFacts.frobProgId (Return v;; Return tt)).
    simpl. reflexivity.
  }
  split. { exists x2. easy. }
  split; [exact H9 |].
  exact H10.
Qed.

Lemma SpinLock_Rel_verified {T} : 
  forall (i: Name T),
    VerifyProg i (Rely i) (Guar i)
      (prComp (Precs i unit Rel) (TInvoke SpinLockImpl i _ Rel) ->> Rely i)
      (SpinLockImpl _ Rel)
      (fun v => Posts i unit Rel v).
Proof.
  intros; simpl.
  apply (lemBind (fun (_: bool) => 
            (fun v : unit => Posts i unit Rel v) tt)).
  + eapply weakenPost.
    eapply (lemCall 
      (Q := fun (s: InterState F (VE T)) (ρs: PossSet (VFU T)) t σs =>
        exists ρ σ, ρs = eq ρ /\ σs = eq σ /\
        UnderThreadStep (fst s i) (Some (CallEv (CAS (Some true) None))) (fst t i) /\
        (* Step (VE T) (snd s) (i, (CallEv (CAS (Some true) None))) (snd t) /\  *)
        (exists a, PState σ = inr (UBState_, a) /\ (a i = Some (existT (fun A => LockSig A) unit Rel))) /\
        PCalls σ i = CallDone Rel /\
        PRets σ i = RetIdle)
      (S := fun v s ρs t σs =>
        exists ρ σ, ρs = eq ρ /\ σs = eq σ /\
        UnderThreadStep (fst s i) (Some (RetEv (CAS (Some true) None) v)) (fst t i) /\
        (exists a, PState σ = inr (UBState_, a) /\ a i = None) /\
        PCalls σ i = CallDone Rel /\
        PRets σ i = RetPoss Rel tt)).
    { unfold Stable, stableRelt, sub, subRelt, ReltCompose.
      intros.
      rename ρ into ρs.
      rename σ into σs.
      destruct H as [s1 [ρs1 ?]].
      destruct H.
      destruct H as [ρ [ρ1 [? [? ?]]]].
      unfold Rely in H0.
      specialize (H0 _ H1).
      destruct H0 as [σ [? ?]].
      exists ρ, σ.
      split; [exact H |].
      split; [exact H0 |].
      destruct_all.
      unfold F. rewrite <- H9.
      split; [easy |].
      split.
      { assert((exists a : ActiveMap T LockSig, PState ρ1 = inr (UBState_, a))).
        { exists x. easy. }
        specialize (H8 H15).
        destruct H8 as [a' ?].
        exists a'.
        split; [ easy |].
        unfold F in H11. rewrite H11 in H10.
        rewrite H8 in H10.
        unfold StateWithUB_acf in H10.
        rewrite <- H10.
        apply H14.
      }
      rewrite <- H3, <- H4.
      easy.
    }
    {
      unfold Stable, stablePost, stableRelt, sub, subRelt, ReltCompose.
      intros.
      rename ρ into ρs.
      rename σ into σs.
      destruct H as [s1 [ρs1 ?]].
      destruct H.
      destruct H as [ρ [ρ1 [? [? ?]]]].
      unfold Rely in H0.
      specialize (H0 _ H1).
      destruct H0 as [σ [? ?]].
      exists ρ, σ.
      split; [exact H |].
      split; [exact H0 |].
      destruct_all.
      unfold F. rewrite <- H9.
      split; [easy |].
      split.
      { assert((exists a : ActiveMap T LockSig, PState ρ1 = inr (UBState_, a))).
        { exists x. easy. }
        specialize (H8 H15).
        destruct H8 as [a' ?].
        exists a'.
        split; [ easy |].
        unfold F in H11. rewrite H11 in H10.
        rewrite H8 in H10.
        unfold StateWithUB_acf in H10.
        rewrite <- H10.
        apply H14.
      }
      rewrite <- H3, <- H4.
      easy.
    }
    {
      unfold Commit.
      intros.
      unfold ReltToPrec in H.
      destruct H as [s0 [ρs0 ?]].
      pose proof Rel_verify_aux2 i s0 ρs0 s ρs H.
      destruct H3 as [ρ [? [? [? [? ?]]]]].
      remember (
        MkPoss T F (VFU T)
        (inr (UBState_, fun j => if i =? j then Some (existT (fun A => LockSig A) unit Rel) else (StateWithUB_acf _ (acf T) (PState ρ) j)))
        (fun j => if i =? j then CallDone Rel else PCalls ρ j)
        (fun j => if i =? j then RetIdle else PRets ρ j)) as σ.
      exists (eq σ).
      split. { exists σ. reflexivity. }
      split.
      { intros. exists ρ.
        split. { rewrite H3. reflexivity. }
        subst σ0.
        apply (PossStepsStep i ρ σ σ).
        { apply (PCommitCall i _ _ unit Rel); subst σ; simpl; try easy.
          { destruct (PState ρ).
            { constructor.
              { intros. intro. inversion H8; subst. contradiction. }
              { constructor. 
                { unfold StateWithUB_acf in H5. apply H5. }
                { rewrite eqb_id. reflexivity. }
                { apply differ_pointwise_trivial. }
              }
            }
            { destruct p. destruct u. constructor. constructor.
              { unfold StateWithUB_acf in H5. apply H5. }
              { rewrite eqb_id. reflexivity. }
              { apply differ_pointwise_trivial. }
            }
          }
          { rewrite eqb_id. reflexivity. }
          { rewrite eqb_id. reflexivity. }
        }
        { intros. subst σ. simpl. rewrite (eqb_nid _ _ H8). reflexivity. }
        { intros. subst σ. simpl. rewrite (eqb_nid _ _ H8). reflexivity. }
        { constructor. }
      }
      split.
      { exists ρ, σ.
        repeat split; subst σ; simpl; try rewrite eqb_id; try easy.
        eexists.
        split. { reflexivity. }
        simpl. rewrite eqb_id. reflexivity.
      }
      { unfold Guar.
        intros.
        pose proof Poss_eq_unique2 _ _ _ H8 H3; subst ρ0.
        exists σ.
        split; [reflexivity |].
        split. 
        { intros. unfold differ_pointwise in H0. specialize (H0 _ H9). easy. }
        split.
        { subst σ. simpl. intros. rewrite (eqb_nid i j (ltac:(auto))). reflexivity. }
        split.
        { subst σ. simpl. intros. rewrite (eqb_nid i j (ltac:(auto))). reflexivity. }
        split.
        { intros. subst σ. simpl.
          right. 
          eexists. reflexivity.
        }
        split; [ easy |].
        split. { intros. subst σ. easy. }
        split.
        { intros. subst σ. simpl. eexists. reflexivity. }
        { intros. subst σ. simpl. rewrite (eqb_nid i j (ltac:(auto))). reflexivity. }
      }
    }
    {
      unfold Commit.
      intros.
      unfold ReltToPrec in H.
      destruct H as [s0 [ρs0 ?]].
      pose proof Rel_verify_aux3 i s0 ρs0 s ρs H.
      clear H.
      destruct H3 as [ρ [? [? [? [? ?]]]]].
      destruct H3 as [a [? ?]].
      remember (
        MkPoss T F (VFU T)
        (inr (UBState_, fun j => if i =? j then None else (StateWithUB_acf _ (acf T) (PState ρ) j)))
        (fun j => if i =? j then CallDone Rel else PCalls ρ j)
        (fun j => if i =? j then RetPoss Rel tt else PRets ρ j)) as σ.
      exists (eq σ).
      split. { exists σ. reflexivity. }
      split.
      { intros. exists ρ.
        split. { rewrite H. reflexivity. }
        subst σ0.
        apply (PossStepsStep i ρ σ σ).
        { apply (PCommitRet i _ _ unit Rel tt); subst σ; simpl; try easy.
          { rewrite H3. constructor. constructor.
            { apply H7. }
            { rewrite eqb_id. reflexivity. }
            { apply differ_pointwise_trivial. }
        }
        { rewrite eqb_id. reflexivity. }
        { rewrite eqb_id. reflexivity. }
        }
        { intros. subst σ. simpl. rewrite (eqb_nid _ _ H8). reflexivity. }
        { intros. subst σ. simpl. rewrite (eqb_nid _ _ H8). reflexivity. }
        { constructor. }
      }
      split.
      { exists ρ, σ.
        unfold F in H1. rewrite H6 in H1. inversion H1; subst.
        dependent destruction H9.
        dependent destruction H12.
        unfold F. rewrite H6.
        repeat split; simpl; try rewrite eqb_id; try easy.
        eexists. split; [reflexivity |].
        simpl. rewrite eqb_id. reflexivity.
      }
      { unfold Guar.
        intros.
        pose proof Poss_eq_unique2 _ _ _ H8 H; subst ρ0.
        exists σ.
        split; [reflexivity |].
        split. 
        { intros. unfold differ_pointwise in H0. specialize (H0 _ H9). easy. }
        split.
        { subst σ. simpl. intros. rewrite (eqb_nid i j (ltac:(auto))). reflexivity. }
        split.
        { subst σ. simpl. intros. rewrite (eqb_nid i j (ltac:(auto))). reflexivity. }
        split.
        { intros. subst σ. simpl.
          right. 
          eexists. reflexivity.
        }
        split; [ easy |].
        split. { intros. subst σ. easy. }
        split.
        { intros. subst σ. simpl. eexists. reflexivity. }
        { intros. subst σ. simpl. rewrite (eqb_nid i j (ltac:(auto))). reflexivity. }
      }
    }
    {
      unfold sub, subRelt.
      intros.
      rename ρ into ρs.
      rename σ into σs.
      rewrite <- LogicFacts.reltCompAssoc in H.
      pose proof Rel_verify_aux4 i s ρs t σs v H.
      assert(exists ρ, ρs = eq ρ).
      { unfold ReltCompose in H. destruct_all. unfold prComp in H.
        destruct H.
        unfold Precs in H.
        destruct H as [ρ0 [? ?]].
        exists ρ0. rewrite H. reflexivity. 
      }
      clear H.
      destruct H0 as [σ [? ?]].
      unfold Posts.
      destruct H1 as [ρ ?].
      destruct_all.
      exists ρ, σ.
      repeat split; try easy.
      exists x. easy.
    }
  + intros.
    constructor.
    easy. 
Qed.

End SpinLockUB.

Module SpinLockAll.

