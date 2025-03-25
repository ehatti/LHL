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

Definition E := CASSig bool.
Definition F := LockSig.
Definition acf T := @LockActiveMap T.
Definition HAcf T : @acf_sound T F lockSpec (acf T) := @LockActiveMapSound T.
Definition VE T : Spec T E:= @casSpec T bool.
Definition VF T := @lockSpec T.
Definition Vξ T : ClientSpec T F (VF T).(State) :=
  fun m s =>
    match m with.
Definition VFU T := SpecWithUB (@lockSpec T) (acf T) (HAcf T).
Definition ReltU T := Relt (VE T) (VFU T).
Definition Relt T := Relt (VE T) (VF T).
Definition PrecU T := Prec (VE T) (VFU T).
Definition Prec T := Prec (VE T) (VF T).
Definition PostU T := Post (VE T) (VFU T).
Definition Post T := Post (VE T) (VF T).
Definition UState T := State (VFU T).

Ltac elim_corece :=
  unfold E in *; unfold F in *;
  repeat match goal with
  | H : context[(CASState ?T bool)] |- _ =>
      change (CASState T bool) with (@State T (CASSig bool) (VE T)) in H
  | |- context[(CASState ?T bool)] =>
      change (CASState T bool) with (@State T (CASSig bool) (VE T))
  | H : context[(forall _ : Name ?T, ThreadState (CASSig bool) F)] |- _ =>
      change ((forall _ : Name T, ThreadState (CASSig bool) F)) with (forall _ : Name T, ThreadState (CASSig bool) LockSig) in H
  | H : context[(forall _ : Name ?T, ThreadState (CASSig bool) LockSig)] |- _ =>      
      change (forall _ : Name ?T, ThreadState (CASSig bool) LockSig) with (ThreadsSt T (CASSig bool) LockSig) in H
  | |- context [(forall _ : Name ?T, ThreadState (CASSig bool) F)] =>
      change (forall _ : Name ?T, ThreadState (CASSig bool) F) with (forall _ : Name T, ThreadState (CASSig bool) LockSig)
  | |- context [(forall _ : Name ?T, ThreadState (CASSig bool) LockSig)] =>
      change (forall _ : Name ?T, ThreadState (CASSig bool) LockSig) with (ThreadsSt T (CASSig bool) LockSig)
  end.

Definition CAS_i_acq {T} (i : Name T) : option (@CASPend T bool) :=
  (Some (MkCASPend i (CAS None (Some true)))).

Definition CAS_i_rel {T} (i : Name T) : option (@CASPend T bool) :=
  (Some (MkCASPend i (CAS (Some true) None))).

Definition i_owns {T} (i : Name T) (s: InterState F (VE T)) (ρ: Poss (VFU T)) :=
  PState ρ = inl (LockOwned i) /\ (snd s = CASDef (Some true) None \/ (exists j, j <> i /\ snd s = CASDef (Some true) (CAS_i_acq j))).

Definition other_owns{T} (i : Name T) (s: InterState F (VE T)) (ρ: Poss (VFU T)) :=
  exists j, j <> i /\ i_owns j s ρ.

Definition unowns {T} (s: InterState F (VE T)) (ρ: Poss (VFU T)) :=
  PState ρ = inl LockUnowned /\ snd s = CASDef None None.

Definition unowns_acq {T} (i : Name T) (s: InterState F (VE T)) (ρ: Poss (VFU T)) :=
  PState ρ = inl LockUnowned /\ snd s = CASDef None (CAS_i_acq i).

Definition i_owns_rel {T} (i : Name T) (s: InterState F (VE T)) (ρ: Poss (VFU T)) :=
  PState ρ = inl (LockOwned i) /\ snd s = CASDef (Some true) (CAS_i_rel i).

Definition other_owns_rel {T} (i : Name T) (s: InterState F (VE T)) (ρ: Poss (VFU T)) :=
  exists j, j <> i /\ i_owns_rel j s ρ.

Definition is_ub_state {T} (s: InterState F (VE T)) (ρ: Poss (VFU T)) :=
  exists a, PState ρ = inr (UBState_, a) /\ exists o m, snd s = CASDef o m.

Definition i_not_owns {T} (i : Name T) (s: InterState F (VE T)) (ρ: Poss (VFU T)) :=
  (other_owns i s ρ \/ unowns s ρ \/ (exists j, j <> i /\ unowns_acq j s ρ) \/ (other_owns_rel i s ρ)).

Definition other_owns_acq {T} (i : Name T) (s: InterState F (VE T)) (ρ: Poss (VFU T)) :=
  exists j, j <> i /\ PState ρ = inl (LockOwned j) /\ snd s = CASDef (Some true) (CAS_i_acq i).

Definition valid_state {T} (i : Name T) (s: InterState F (VE T)) (ρ: Poss (VFU T)) :=
  i_owns i s ρ \/ other_owns i s ρ \/ unowns s ρ \/ (exists j, unowns_acq j s ρ) \/ i_owns_rel i s ρ \/ other_owns_rel i s ρ.

Definition Precs {T} i A (m : LockSig A) : PrecU T :=
  fun s ρs => exists ρ, ρs = eq ρ /\
    match m with
    | Acq =>
        (valid_state i s ρ \/ is_ub_state s ρ) /\
        StateWithUB_acf _ (acf T) (PState ρ) i = None
    | Rel =>
        (valid_state i s ρ \/ is_ub_state s ρ) /\
        StateWithUB_acf _ (acf T) (PState ρ) i = None
    end.

Definition Posts {T} i A (m : LockSig A) : PostU T A :=
  fun v _ _ t σs => exists σ, σs = eq σ /\
    match m with
    | Acq =>
        (PCalls σ i = CallDone Acq /\ PRets σ i = RetPoss Acq tt /\
         i_owns i t σ /\ fst t i = Cont m (Return v)) \/
        (((PCalls σ i = CallPoss Acq /\ PRets σ i = RetIdle) \/
          (PCalls σ i = CallDone Acq /\ PRets σ i = RetPoss Acq tt)) /\
         is_ub_state t σ /\ StateWithUB_acf _ (acf T) (PState σ) i = None)
    | Rel =>
        (PCalls σ i = CallDone Rel /\ PRets σ i = RetPoss Rel tt /\
         i_not_owns i t σ /\ fst t i = Cont m (Return v)) \/
        (((PCalls σ i = CallPoss Rel /\ PRets σ i = RetIdle) \/
          (PCalls σ i = CallDone Rel /\ PRets σ i = RetPoss Rel tt)) /\
         is_ub_state t σ /\ StateWithUB_acf _ (acf T) (PState σ) i = None)
    end.

Definition CSs {T} i A (m : LockSig A) : PostU T A :=
  fun v s ρs t σs => exists ρ σ, ρs = eq ρ /\ σs = eq σ /\
    match m with
    | Acq =>
        (t = (fun j => if i =? j then Idle else fst s j, snd s) /\ mapRetPoss i m v ρ σ) \/ 
        (is_ub_state t σ /\ StateWithUB_acf _ (acf T) (PState σ) i = None)
    | Rel =>
        (t = (fun j => if i =? j then Idle else fst s j, snd s) /\ mapRetPoss i m v ρ σ) \/
        (is_ub_state t σ /\ StateWithUB_acf _ (acf T) (PState σ) i = None)
    end.

Definition Rely {T} i : ReltU T :=
  fun s ρs t σs => forall ρ, ρs = eq ρ -> exists σ, σs = eq σ /\
    fst s i = fst t i /\
    (i_owns i s ρ -> i_owns i t σ \/ is_ub_state t σ) /\ 
    (i_not_owns i s ρ -> i_not_owns i t σ \/ is_ub_state t σ) /\
    (i_owns_rel i s ρ -> i_owns_rel i t σ \/ is_ub_state t σ) /\
    (unowns_acq i s ρ -> unowns_acq i t σ \/ is_ub_state t σ) /\
    (other_owns_acq i s ρ -> other_owns_acq i t σ \/ is_ub_state t σ) /\
    (is_ub_state s ρ -> is_ub_state t σ) /\
    PCalls ρ i = PCalls σ i /\
    PRets ρ i = PRets σ i /\ 
    StateWithUB_acf _ (acf T) (PState ρ) i = StateWithUB_acf _ (acf T) (PState σ) i.

Definition Guar {T} i : ReltU T :=
  fun s ρs t σs => forall ρ, ρs = eq ρ -> exists σ, σs = eq σ /\
    (forall j, j <> i -> fst s j = fst t j) /\
    (forall j, j <> i -> i_owns j s ρ -> (i_owns j t σ \/ is_ub_state t σ)) /\
    (forall j, j <> i -> i_not_owns j s ρ -> (i_not_owns j t σ \/ is_ub_state t σ)) /\
    (forall j, j <> i -> i_owns_rel j s ρ -> (i_owns_rel j t σ \/ is_ub_state t σ)) /\
    (forall j, j <> i -> unowns_acq j s ρ -> (unowns_acq j t σ \/ is_ub_state t σ)) /\
    (forall j, j <> i -> other_owns_acq j s ρ -> (other_owns_acq j t σ \/ is_ub_state t σ)) /\
    (is_ub_state s ρ -> is_ub_state t σ) /\
    (forall j, j <> i -> PCalls ρ j = PCalls σ j /\ PRets ρ j = PRets σ j) /\
    (forall j, j <> i -> StateWithUB_acf _ (acf T) (PState ρ) j = StateWithUB_acf _ (acf T) (PState σ) j).

Lemma valid_state_idle {T} i s ρ :
  valid_state i s ρ ->
  StateWithUB_acf _ (acf T) (PState ρ) i = None.
Proof.
  intros.
  unfold valid_state in H.
  destruct H as [Howns | [Howns | [Howns | [Howns | [Howns | Howns]]]]].
  { destruct Howns as [Howns ?]. rewrite Howns. easy. }
  { destruct Howns as [j [Hneq Howns]]. unfold i_owns in Howns. destruct Howns as [Howns ?]. rewrite Howns. easy. }
  { destruct Howns as [Howns ?]. rewrite Howns. easy. }
  { destruct Howns as [j [Howns ?]]. rewrite Howns. easy. }
  { destruct Howns as [Howns ?]. rewrite Howns. easy. }
  { destruct Howns as [j [Hneq [Howns ?]]]. rewrite Howns. easy. }
Qed.

Lemma i_owns_easy {T} : forall (i : Name T) s ρ t σ, 
  snd s = snd t ->
  PState ρ = PState σ ->
  i_owns i s ρ ->
  i_owns i t σ.
Proof.
  intros.
  unfold i_owns in *.
  destruct H1 as [Howns Hstate].
  rewrite <- H0.
  split; [easy |].
  destruct Hstate as [Hstate | [j [Hneq Hstate]]].
  { left. rewrite <- H. easy. }
  { right. exists j. split; [easy |]. elim_corece. rewrite <- H. easy. }
Qed.

Lemma other_owns_easy {T} : forall (i : Name T) s ρ t σ, 
  snd s = snd t ->
  PState ρ = PState σ ->
  other_owns i s ρ ->
  other_owns i t σ.
Proof.
  intros.
  unfold other_owns in *.
  destruct H1 as [j [Hneq Howns]].
  exists j. split; [easy |].
  apply i_owns_easy with (s := s)(ρ := ρ); easy.
Qed.

Lemma unowns_easy {T} : forall s ρ t (σ: Poss (VFU T)), 
  snd s = snd t ->
  PState ρ = PState σ ->
  unowns s ρ ->
  unowns t σ.
Proof.
  intros.
  unfold unowns in *.
  rewrite <- H0.
  rewrite <- H.
  easy.
Qed.

Lemma unowns_acq_easy {T} : forall (i : Name T) s ρ t σ, 
  snd s = snd t ->
  PState ρ = PState σ ->
  unowns_acq i s ρ ->
  unowns_acq i t σ.
Proof.
  intros.
  unfold unowns_acq in *.
  destruct H1 as [Howns Hstate].
  rewrite <- H0.
  split; [easy |].
  rewrite <- H.
  easy.
Qed.

Lemma i_owns_rel_easy {T} : forall (i : Name T) s ρ t σ, 
  snd s = snd t ->
  PState ρ = PState σ ->
  i_owns_rel i s ρ ->
  i_owns_rel i t σ.
Proof.
  intros.
  unfold i_owns_rel in *.
  destruct H1 as [Howns Hstate].
  rewrite <- H0.
  split; [easy |].
  rewrite <- H.
  easy.
Qed.

Lemma other_owns_rel_easy {T} : forall (i : Name T) s ρ t σ, 
  snd s = snd t ->
  PState ρ = PState σ ->
  other_owns_rel i s ρ ->
  other_owns_rel i t σ.
Proof.
  intros.
  unfold other_owns_rel in *.
  destruct H1 as [j [Hneq Howns_rel]].
  exists j. split; [easy |].
  apply i_owns_rel_easy with (s := s)(ρ := ρ); easy.
Qed.

Lemma is_ub_state_easy {T} : forall s ρ t (σ: Poss (VFU T)), 
  PState ρ = PState σ ->
  is_ub_state s ρ ->
  is_ub_state t σ.
Proof.
  intros.
  unfold is_ub_state in *.
  destruct H0 as [a [Hstate [o [m HH]]]].
  exists a. split; [rewrite <- H; easy |].
  destruct (snd t).
  eexists. eexists. reflexivity.
Qed.

Lemma is_ub_state_easy2 {T} : forall s (ρ : Poss (VFU T)), 
  (exists a, PState ρ = inr(UBState_, a)) ->
  is_ub_state s ρ.
Proof.
  intros.
  unfold is_ub_state in *.
  destruct H as [a Hstate].
  exists a. split; [easy |].
  destruct (snd s).
  eexists. eexists. reflexivity.
Qed.

Lemma i_not_owns_easy {T} : forall (i : Name T) s ρ t σ, 
  snd s = snd t ->
  PState ρ = PState σ ->
  i_not_owns i s ρ ->
  i_not_owns i t σ.
Proof.
  intros.
  unfold i_not_owns in *.
  destruct H1 as [Howns | [Hunowns | [Hunowns_acq | Howns_rel]]].
  { left. apply other_owns_easy with (s := s)(ρ := ρ); easy. }
  { right. left. apply unowns_easy with (s := s)(ρ := ρ); easy. }
  { right. right. left. destruct Hunowns_acq as [j [Hneq Hunowns_acq]]. exists j. split; [easy |]. apply unowns_acq_easy with (s := s)(ρ := ρ); easy. }
  { right. right. right. apply other_owns_rel_easy with (s := s)(ρ := ρ); easy. }
Qed.

Lemma other_owns_acq_easy {T} : forall (i : Name T) s ρ t σ, 
  snd s = snd t ->
  PState ρ = PState σ ->
  other_owns_acq i s ρ ->
  other_owns_acq i t σ.
Proof.
  intros.
  unfold other_owns_acq in *.
  destruct H1 as [j [Hneq [Howns Hstate]]].
  exists j. split; [easy |]. 
  rewrite <- H. rewrite <- H0. easy.
Qed.

Lemma valid_state_easy {T} : forall (i : Name T) s ρ t σ, 
  snd s = snd t ->
  PState ρ = PState σ ->
  valid_state i s ρ ->
  valid_state i t σ.
Proof.
  intros.
  unfold valid_state in *.
  destruct H1 as [Howns | [Howns | [Howns | [Howns | [Howns | Howns]]]]].
  { left. apply i_owns_easy with (s := s)(ρ := ρ); easy. }
  { right. left. apply other_owns_easy with (s := s)(ρ := ρ); easy. }
  { right. right. left. apply unowns_easy with (s := s)(ρ := ρ); easy. }
  { right. right. right. left. destruct Howns as [j Howns]. exists j. apply unowns_acq_easy with (s := s)(ρ := ρ); easy. }
  { right. right. right. right. left. apply i_owns_rel_easy with (s := s)(ρ := ρ); easy. }
  { right. right. right. right. right. apply other_owns_rel_easy with (s := s)(ρ := ρ); easy. }
Qed.

Lemma i_not_owns_valid {T} : forall (i : Name T) s ρ, 
  i_not_owns i s ρ ->
  valid_state i s ρ.
Proof.
  intros.
  unfold i_not_owns, valid_state in *.
  destruct H as [Howns | [Hunowns | [Hunowns_acq | Howns_rel]]].
  { right. left. easy. }
  { right. right. left. easy. }
  { right. right. right. left. destruct Hunowns_acq as [j [Hneq Hunowns_acq]]. exists j. easy. }
  { right. right. right. right. right. easy. }
Qed.

Lemma i_owns_unowns_exclusive {T} : forall (i : Name T) s ρ, 
  i_owns i s ρ ->
  unowns s ρ ->
  False.
Proof.
  intros.
  unfold i_owns, unowns in *.
  destruct H as [HP1 ?]. destruct H0 as [HP2 ?].
  rewrite HP1 in HP2. inversion HP2.
Qed.

Lemma iowns_inotowns_exclusive {T} : forall (i : Name T) s ρ, 
  i_owns i s ρ ->
  i_not_owns i s ρ ->
  False.
Proof.
  intros.
  unfold i_not_owns in H0.
  destruct H0 as [Howns | [Hunowns | [Hunowns_acq | Howns_rel]]].
  { destruct Howns as [j [Hneq Howns]].
    unfold i_owns in *.
    destruct H as [HP1 ?]. destruct Howns as [HP2 ?].
    rewrite HP1 in HP2. inversion HP2.
    subst j. contradiction.
  }
  { destruct H as [HP1 ?]. destruct Hunowns as [HP2 ?].
    rewrite HP1 in HP2. inversion HP2.
  }
  { destruct H as [HP1 ?]. destruct Hunowns_acq as [j [Hneq [HP2 ?]]].
    rewrite HP1 in HP2. inversion HP2.
  }
  { destruct H as [HP1 ?]. destruct Howns_rel as [j [Hneq [HP2 ?]]].
    rewrite HP1 in HP2. inversion HP2. subst j. contradiction.
  }
Qed.

Lemma iowns_unownsacq_exclusive {T} : forall (i : Name T) s ρ, 
  i_owns i s ρ ->
  unowns_acq i s ρ ->
  False.
Proof. 
  intros.
  unfold i_owns, unowns_acq in *.
  destruct H as [HP1 ?]. destruct H0 as [HP2 ?].
  rewrite HP1 in HP2. inversion HP2.
Qed.

Lemma iowns_iownsrel_exclusive {T} : forall (i : Name T) s ρ, 
  i_owns i s ρ ->
  i_owns_rel i s ρ ->
  False.
Proof.
  intros.
  unfold i_owns, i_owns_rel in *.
  destruct H as [HP1 ?]. destruct H0 as [HP2 ?].
  destruct H.
  { rewrite H in H0. inversion H0. }
  { destruct H as [j [Hneq H]]. rewrite H in H0. inversion H0. }
Qed.

Lemma iowns_isub_exclusive {T} : forall (i : Name T) s ρ, 
  i_owns i s ρ ->
  is_ub_state s ρ ->
  False.
Proof.
  intros.
  unfold i_owns, is_ub_state in *.
  destruct H as [HP1 ?]. destruct H0 as [a [HP2 [o [m ?]]]].
  rewrite HP1 in HP2. inversion HP2.
Qed.

Lemma inotowns_unownsacq_exclusive {T} : forall (i : Name T) s ρ, 
  i_not_owns i s ρ ->
  unowns_acq i s ρ ->
  False.
Proof.
  intros.
  unfold i_not_owns, unowns_acq in *.
  destruct H as [Howns | [Hunowns | [Hunowns_acq | Howns_rel]]].
  { destruct Howns as [j [Hneq Howns]].
    unfold i_owns in *.
    destruct Howns as [HP1 ?]. destruct H0 as [HP2 ?].
    rewrite HP1 in HP2. inversion HP2.
  }
  { destruct Hunowns as [HP1 ?]. destruct H0 as [HP2 ?].
    rewrite H in H0. inversion H0.
  }
  { destruct Hunowns_acq as [j [Hneq [HP2 ?]]]. destruct H0 as [HP1 ?].
    rewrite H in H0. inversion H0. subst j. contradiction. 
  }
  { destruct H0 as [HP1 ?]. destruct Howns_rel as [j [Hneq [HP2 ?]]].
    rewrite HP1 in HP2. inversion HP2.
  }
Qed.

Lemma inotowns_iownsrel_exclusive {T} : forall (i : Name T) s ρ, 
  i_not_owns i s ρ ->
  i_owns_rel i s ρ ->
  False.
Proof.
  intros.
  unfold i_not_owns, i_owns_rel in *.
  destruct H as [Howns | [Hunowns | [Hunowns_acq | Howns_rel]]].
  { destruct Howns as [j [Hneq Howns]].
    unfold i_owns in *.
    destruct H0 as [HP1 ?]. destruct Howns as [HP2 ?].
    rewrite HP1 in HP2. inversion HP2. subst j. contradiction.
  }
  { destruct Hunowns as [HP1 ?]. destruct H0 as [HP2 ?].
    rewrite HP1 in HP2. inversion HP2.
  }
  { destruct Hunowns_acq as [j [Hneq [HP2 ?]]]. destruct H0 as [HP1 ?].
    rewrite HP1 in HP2. inversion HP2.
  }
  { destruct H0 as [HP1 ?]. destruct Howns_rel as [j [Hneq [HP2 ?]]].
    rewrite HP1 in HP2. inversion HP2. subst j. contradiction.
  }
Qed.

Lemma inotowns_isub_exclusive {T} : forall (i : Name T) s ρ, 
  i_not_owns i s ρ ->
  is_ub_state s ρ ->
  False.
Proof.
  intros.
  unfold i_not_owns, is_ub_state in *.
  destruct H as [Howns | [Hunowns | [Hunowns_acq | Howns_rel]]].
  { destruct H0 as [a [HP1 [o [m ?]]]]. destruct Howns as [? [? Howns]].
    unfold i_owns in *.
    destruct Howns as [HP2 ?].
    rewrite HP1 in HP2. inversion HP2.
  }
  { destruct Hunowns as [HP1 ?]. destruct H0 as [a [HP2 [o [m ?]]]].
    rewrite HP1 in HP2. inversion HP2.
  }
  { destruct Hunowns_acq as [j [Hneq [HP2 ?]]]. destruct H0 as [a [HP1 [o [m ?]]]].
    rewrite HP1 in HP2. inversion HP2.
  }
  { destruct H0 as [a [HP1 [o [m ?]]]]. 
    destruct Howns_rel as [j [Hneq [HP2 ?]]].
    rewrite HP1 in HP2. inversion HP2.
  }
Qed.

Lemma unownsacq_iownsrel_exclusive {T} : forall (i : Name T) s ρ, 
  unowns_acq i s ρ ->
  i_owns_rel i s ρ ->
  False.
Proof.
  intros.
  unfold unowns_acq, i_owns_rel in *.
  destruct H as [Howns Hstate]. destruct H0 as [Howns_rel Hstate_rel].
  rewrite Hstate in Hstate_rel. inversion Hstate_rel.
Qed.

Lemma isub_iownsrel_exclusive {T} : forall (i : Name T) s ρ, 
  is_ub_state s ρ ->
  i_owns_rel i s ρ ->
  False.
Proof.
  intros.
  unfold is_ub_state, i_owns_rel in *.
  destruct H as [a [HP1 [o [m ?]]]]. destruct H0 as [HP2 ?].
  rewrite HP1 in HP2. inversion HP2.
Qed.

Lemma iownsrel_unownsacq_exclusive {T} : forall (i : Name T) s ρ, 
  i_owns_rel i s ρ ->
  unowns_acq i s ρ ->
  False.
Proof.
  intros.
  unfold i_owns_rel, unowns_acq in *.
  destruct H as [Howns Hstate]. destruct H0 as [Howns_acq Hstate_acq].
  rewrite Hstate in Hstate_acq. inversion Hstate_acq.
Qed.

Lemma isub_unownsacq_exclusive {T} : forall (i : Name T) s ρ, 
  is_ub_state s ρ ->
  unowns_acq i s ρ ->
  False.
Proof.
  intros.
  unfold is_ub_state, unowns_acq in *.
  destruct H as [a [HP1 [o [m ?]]]]. destruct H0 as [Howns Hstate].
  rewrite HP1 in Howns. inversion Howns.
Qed.

Lemma unownsacq_isub_exclusive {T} : forall (i : Name T) s ρ, 
  unowns_acq i s ρ ->
  is_ub_state s ρ ->
  False.
Proof.
  intros.
  unfold unowns_acq, is_ub_state in *.
  destruct H as [Howns Hstate]. destruct H0 as [a [HP1 [o [m ?]]]].
  rewrite HP1 in Howns. inversion Howns.
Qed.

Lemma iownsrel_isub_exclusive {T} : forall (i : Name T) s ρ, 
  i_owns_rel i s ρ ->
  is_ub_state s ρ ->
  False.
Proof.
  intros.
  unfold i_owns_rel, is_ub_state in *.
  destruct H as [Howns Hstate]. destruct H0 as [a [HP1 [o [m ?]]]].
  rewrite HP1 in Howns. inversion Howns.
Qed.

Lemma isub_otherownsacq_exclusive {T} : forall (i : Name T) s ρ, 
  is_ub_state s ρ ->
  other_owns_acq i s ρ ->
  False.
Proof.
  intros.
  unfold is_ub_state, other_owns_acq in *.
  destruct H as [a [HP1 [o [m ?]]]]. destruct H0 as [j [Hneq [Howns Hstate]]].
  rewrite HP1 in Howns. inversion Howns.
Qed.

Definition stateStepToUBPre {T A} (ρ : Poss (VFU T)) (m: F A) i :=
  MkPoss T F (VFU T) 
         (inr (UBState_, fun j => if i =? j then (Some (existT (fun A => F A) A m))
                                  else (StateWithUB_acf LockStep (acf T) (PState ρ)) j))
         (fun j => if i =? j then CallDone m else PCalls ρ j)
         (fun j => if i =? j then RetIdle else PRets ρ j).

Definition stateStepToUB {T A} (ρ : Poss (VFU T)) i (m: F A) (v: A) :=
  MkPoss T F (VFU T) (inr (UBState_, StateWithUB_acf LockStep (acf T) (PState ρ)))
         (fun j => if i =? j then CallDone m else PCalls ρ j)
         (fun j => if i =? j then RetPoss m v else PRets ρ j).

Lemma stateStepToUBPreErrorStep {T A} (ρ : Poss (VFU T)) (m: F A) i:
  (exists s, PState ρ = inl s /\ acf T s i = None /\ (forall s', ~Step (VF T) s (i, CallEv m) s')) ->
  Step (VFU T) (PState ρ) (i, CallEv m) (PState (stateStepToUBPre ρ m i)).
Proof.
  intros.
  unfold stateStepToUBPre. simpl.
  destruct H as [s [Hs Hstep]].
  rewrite Hs.
  eapply ErrorStep.
  + easy.
  + constructor.
    - easy.
    - rewrite eqb_id. easy.
    - apply differ_pointwise_trivial.
Qed.

Lemma stateStepToUBPreUBStep {T A} (ρ : Poss (VFU T)) (m: F A) i:
  (exists a, PState ρ = inr (UBState_, a)) ->
  StateWithUB_acf LockStep (acf T) (PState ρ) i = None ->
  Step (VFU T) (PState ρ) (i, CallEv m) (PState (stateStepToUBPre ρ m i)).
Proof.
  intros.
  unfold stateStepToUBPre. simpl.
  intros.
  destruct H as [a Hs].
  rewrite Hs in H0. simpl in H0.
  rewrite Hs. simpl.
  eapply UBStep. constructor.
  + easy.
  + rewrite eqb_id. easy.
  + unfold differ_pointwise.
    intros. rewrite eqb_nid; easy.
Qed.

Lemma stateStepToUBPrePossStep {T A} (ρ : Poss (VFU T)) (m: F A) i:
  PCalls ρ i = CallPoss m ->
  PRets ρ i = RetIdle ->
  Step (VFU T) (PState ρ) (i, CallEv m) (PState (stateStepToUBPre ρ m i)) ->
  PossStep i ρ (stateStepToUBPre ρ m i).
Proof.
  intros.
  eapply Logic.PCommitCall with (i := i)(m := m).
  { easy. }
  { easy. }
  { unfold stateStepToUBPre. simpl. rewrite eqb_id. easy. }
  { easy. }
  { unfold stateStepToUBPre. simpl. rewrite eqb_id. easy. }
Qed.

Lemma stateStepToUBPreCall {T A} (ρ : Poss (VFU T)) (m: F A) i:
  forall j : Name T, i <> j -> PCalls ρ j = PCalls (stateStepToUBPre ρ m i) j.
Proof.
  intros.
  unfold stateStepToUBPre. simpl. rewrite eqb_nid; easy.
Qed.

Lemma stateStepToUBPreRet {T A} (ρ : Poss (VFU T)) (m: F A) i:
  forall j : Name T, i <> j -> PRets ρ j = PRets (stateStepToUBPre ρ m i) j.
Proof.
  intros.
  unfold stateStepToUBPre. simpl. rewrite eqb_nid; easy.
Qed.

Lemma stateStepToUBStep {T A} (ρ : Poss (VFU T)) i (m: F A) (v: A):
  StateWithUB_acf LockStep (acf T) (PState ρ) i = None ->
  Step (VFU T) (PState (stateStepToUBPre ρ m i)) (i, RetEv m v) (PState (stateStepToUB ρ i m v)).
Proof.
  unfold stateStepToUBPre, stateStepToUB. simpl.
  econstructor. econstructor.
  + rewrite eqb_id. easy.
  + easy.
  + unfold differ_pointwise. intros j Hneq. rewrite eqb_nid; easy.
Qed.

Lemma stateStepToUBPossStep {T A} (ρ : Poss (VFU T)) i (m: F A) (v: A):
  PCalls ρ i = CallPoss m ->
  PRets ρ i = RetIdle ->
  StateWithUB_acf LockStep (acf T) (PState ρ) i = None ->
  PossStep i (stateStepToUBPre ρ m i) (stateStepToUB ρ i m v).
Proof.
  intros.
  eapply Logic.PCommitRet with (i := i)(m := m)(v := v).
  { apply stateStepToUBStep. easy. }
  { unfold stateStepToUBPre. simpl. rewrite eqb_id. easy. }
  { unfold stateStepToUB. simpl. rewrite eqb_id. easy. }
  { unfold stateStepToUBPre. simpl. rewrite eqb_id. easy. }
  { unfold stateStepToUBPre. simpl. rewrite eqb_id. easy. }
Qed.

Lemma stateStepToUBCall {T A} (ρ : Poss (VFU T)) (m: F A) v i:
  forall j : Name T, i <> j -> PCalls (stateStepToUBPre ρ m i) j = PCalls (stateStepToUB ρ i m v) j.
Proof.
  intros.
  unfold stateStepToUBPre. simpl. rewrite eqb_nid; easy.
Qed.

Lemma stateStepToUBRet {T A} (ρ : Poss (VFU T)) (m: F A) v i:
  forall j : Name T, i <> j -> PRets (stateStepToUBPre ρ m i) j = PRets (stateStepToUB ρ i m v) j.
Proof.
  intros.
  unfold stateStepToUBPre. simpl. rewrite eqb_nid; easy.
Qed.

Lemma stateStepToUBPossSteps {T A} (ρ : Poss (VFU T)) i (m: F A) (v: A):
  PCalls ρ i = CallPoss m ->
  PRets ρ i = RetIdle ->
  StateWithUB_acf LockStep (acf T) (PState ρ) i = None ->
  Step (VFU T) (PState ρ) (i, CallEv m) (PState (stateStepToUBPre ρ m i)) ->
  PossSteps ρ (stateStepToUB ρ i m v).
Proof.
  intros.
  eapply Logic.PossStepsStep with (i := i)(σ := stateStepToUBPre ρ m i).
  { apply stateStepToUBPrePossStep; try easy. }
  { apply stateStepToUBPreCall. }
  { apply stateStepToUBPreRet. }
  eapply Logic.PossStepsStep with (i := i). 4: apply Logic.PossStepsRefl.
  { apply stateStepToUBPossStep; easy. }
  { apply stateStepToUBCall. }
  { apply stateStepToUBRet. }
Qed.

(* Lemma stateStepToUBResult {T A} (ρ : Poss (VFU T)) i (m: F A) (v: A):
PCalls (stateStepToUB ρ i m v) i = CallDone Acq /\
PRets (stateStepToUB ρ i m v) i = RetPoss Acq tt /\
is_ub_state t (stateStepToUB ρ i m v). *)

Lemma differ_pointwise_other {A State : Type} (ist ist' : A -> State) i :
  differ_pointwise ist ist' i -> (forall j , j <> i -> ist j = ist' j).
Proof.
  intros.
  unfold differ_pointwise in H.
  specialize (H j H0).
  easy.
Qed.

Lemma SpinLock_R_refl {T} : forall (i : Name T) s ρ, Rely i s ρ s ρ.
Proof.
  unfold Rely.
  intros.
  exists ρ0.
  repeat split; try easy.
  + intros. left. easy.
  + intros. left. easy.
  + intros. left. easy.
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
  + rewrite H2, H12. easy.
  + intros Howns.
    specialize (H3 Howns).
    destruct H3 as [Howns' | Hub].
    { specialize (H13 Howns'). destruct H13.
      { left. easy. }
      { right. easy. }
    }
    { specialize (H18 Hub). right. easy. }
  + intros Hunowns.
    specialize (H4 Hunowns).
    destruct H4 as [Hunowns' | Hub].
    { specialize (H14 Hunowns'). destruct H14.
      { left. easy. }
      { right. easy. }
    }
    { specialize (H18 Hub). right. easy. }
  + intros Howns_rel.
    specialize (H5 Howns_rel).
    destruct H5 as [Howns' | Hub].
    { specialize (H15 Howns'). destruct H15.
      { left. easy. }
      { right. easy. }
    }
    { specialize (H18 Hub). right. easy. }
  + intros Hunowns_acq.
    specialize (H6 Hunowns_acq).
    destruct H6 as [Hunowns' | Hub].
    { specialize (H16 Hunowns'). destruct H16.
      { left. easy. }
      { right. easy. }
    }
    { specialize (H18 Hub). right. easy. }
  + intros Hother_owns_acq.
    specialize (H7 Hother_owns_acq).
    destruct H7 as [Hother_owns_acq' | Hub].
    { specialize (H17 Hother_owns_acq'). destruct H17.
      { left. easy. }
      { right. easy. }
    }
    { specialize (H18 Hub). right. easy. }
  + intros Hub. specialize (H8 Hub). specialize(H18 H8). easy.
  + rewrite H9, H19. easy.
  + rewrite H10, H20. easy.
  + rewrite H11, H21. easy.
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
  specialize (H5 _ Hneq).
  specialize (H4 _ Hneq).
  specialize (H6 _ Hneq).
  specialize (H7 _ Hneq).
  specialize (H9 _ Hneq).
  specialize (H10 _ Hneq).
  repeat split; try easy.
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
  { intros. unfold i_not_owns in H7.
    destruct H7 as [Hother_owns | [Hunowns | [Hunowns_acq | Hother_owns_rel]]].
    { left. left. apply other_owns_easy with (s := s)(ρ := ρ0); easy. }
    { left. right. left. apply unowns_easy with (s := s)(ρ := ρ0); easy. }
    { left. right. right. left. destruct Hunowns_acq as [j0 [Hneq Hunowns_acq]]. 
      exists j0. split; [easy |]. apply unowns_acq_easy with (s := s)(ρ := ρ0); easy. }
    { left. do 3 right. apply other_owns_rel_easy with (s := s)(ρ := ρ0); easy. }
  }
  split.
  { intros. left. apply i_owns_rel_easy with (s := s)(ρ := ρ0); easy. }
  split.
  { intros. left. apply unowns_acq_easy with (s := s)(ρ := ρ0); easy. }
  split.
  { intros. simpl. left.  apply other_owns_acq_easy with (s := s)(ρ := ρ0); easy. }
  split.
  { intros. unfold is_ub_state in *. destruct H7 as [a [Hstate [o [mm Hsnd]]]].
    exists a. split; [easy |]. exists o, mm. elim_corece. rewrite <- H2. easy.
  }
  split.
  { simpl. rewrite (eqb_nid i j H). easy. }
  split.
  { simpl. rewrite (eqb_nid i j H). easy. }
  { easy. }
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
  { intros. unfold i_not_owns in H6.
    destruct H6 as [Hother_owns | [Hunowns | [Hunowns_acq | Hother_owns_rel]]].
    { left. left. apply other_owns_easy with (s := s)(ρ := ρ0); easy. }
    { left. right. left. apply unowns_easy with (s := s)(ρ := ρ0); easy. }
    { left. right. right. left. destruct Hunowns_acq as [j0 [Hneq Hunowns_acq]]. 
      exists j0. split; [easy |]. apply unowns_acq_easy with (s := s)(ρ := ρ0); easy. }
    { left. do 3 right. apply other_owns_rel_easy with (s := s)(ρ := ρ0); easy. }
  }
  split.
  { intros. left. apply i_owns_rel_easy with (s := s)(ρ := ρ0); easy. }
  split.
  { intros. left. apply unowns_acq_easy with (s := s)(ρ := ρ0); easy. }
  split.
  { intros. simpl. left.  apply other_owns_acq_easy with (s := s)(ρ := ρ0); easy. }
  split.
  { intros. unfold is_ub_state in *. destruct H6 as [a [Hstate [o [mm Hsnd]]]].
    exists a. split; [easy |]. exists o, mm. elim_corece. rewrite <- H2. easy.
  }
  split.
  { simpl. rewrite (eqb_nid i j H). easy. }
  split.
  { simpl. rewrite (eqb_nid i j H). easy. }
  { easy. }
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
    { left. right. right. left. easy. }
    easy.
  + split. 
    { left. right. right. left. easy. }
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
  assert((valid_state i s' ρ' \/ is_ub_state s' ρ') /\ (StateWithUB_acf LockStep (acf T) (PState ρ') i = None)) as Htmp.
  { destruct m; easy. }
  clear H1. pose proof Htmp as H1. clear Htmp.
  cut((valid_state i s ρ \/ is_ub_state s ρ) /\ StateWithUB_acf LockStep (acf T) (PState ρ) i = None).
  { destruct m; easy. }
  + destruct H1 as [[Hvalid | Hub] HIdle].
    - split.
      2: { rewrite <- H11. apply valid_state_idle with (s := s'). easy. }
      destruct Hvalid as [Howns | [Hother_owns | [Hunowns | [Hunowns_acq | [Howns_rel | Hother_owns_rel]]]]].
      * specialize (H3 Howns). destruct H3 as [Howns' | Hub'].
        { left. left. easy. }
        { right. easy. }
      * assert(i_not_owns i s' ρ') as Hnot_owns.
        { unfold i_not_owns. left. easy. }
        specialize (H4 Hnot_owns). destruct H4 as [Hnotowns' | Hub'].
        { left. apply i_not_owns_valid. easy. }
        { right. easy. }
      * assert(i_not_owns i s' ρ') as Hnot_owns.
        { unfold i_not_owns. right. left. easy. }
        specialize (H4 Hnot_owns). destruct H4 as [Hnotowns' | Hub'].
        { left. apply i_not_owns_valid. easy. }
        { right. easy. }
      * destruct Hunowns_acq as [j Hunowns_acq].
        destruct (classicT (i = j)).
        { subst j. specialize (H6 Hunowns_acq). destruct H6 as [Hunowns_acq' | Hub].
          { left. right. right. right. left. exists i. easy. }
          { right. easy. }
        }
        { assert(i_not_owns i s' ρ') as Hnot_owns.
          { unfold i_not_owns. right. right. left. exists j. easy. }
          specialize (H4 Hnot_owns). destruct H4 as [Hnotowns' | Hub'].
          { left. apply i_not_owns_valid. easy. }
          { right. easy. }
        }
      * specialize (H5 Howns_rel). destruct H5 as [Howns_rel' | Hub'].
        { left. right. right. right. right. left. easy. }
        { right. easy. }
      * assert(i_not_owns i s' ρ') as Hnot_owns.
        { unfold i_not_owns. right. right. right. easy. }
        specialize (H4 Hnot_owns). destruct H4 as [Hnotowns' | Hub'].
        { left. apply i_not_owns_valid. easy. }
        { right. easy. }
    - specialize (H8 Hub).
      split.
      { right. easy. }
      { rewrite <- H11. apply HIdle. }
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
  destruct H1 as [ρ2 [? ?]].
  destruct H0 as [ρ2' [ρ [? [? ?]]]].
  pose proof Poss_eq_unique2 _ _ _ H0 H1 as Htmp. subst ρ2'.
  exists ρ. split; [easy |].
  cut((valid_state i s ρ \/ is_ub_state s ρ) /\ StateWithUB_acf LockStep (acf T) (PState ρ) i = None).
  { destruct m2; easy. }
  assert(
      exists v: A,
      (PCalls ρ2 i = CallDone m1 /\ PRets ρ2 i = RetPoss m1 v /\ valid_state i s2 ρ2) \/
      (((PCalls ρ2 i = CallPoss m1 /\ PRets ρ2 i = RetIdle) \/
        (PCalls ρ2 i = CallDone m1 /\ PRets ρ2 i = RetPoss m1 v)) /\
        (is_ub_state s2 ρ2 /\ StateWithUB_acf LockStep (acf T) (PState ρ2) i = None))) as Hpost.
  { destruct m1; exists tt; destruct v.
    { destruct H3; destruct_all.
      { left. repeat split; try easy. left. easy. }
      { right. repeat split; try easy. }
    }
    { destruct H3; destruct_all.
      { left. repeat split; try easy. apply i_not_owns_valid. easy. }
      { right. repeat split; try easy. }
    }
  }
  clear H3 H2.
  destruct Hpost as [v' Hpost].
  assert((s = (fun j : Name T => if i =? j then Idle else fst s2 j, snd s2) /\ mapRetPoss i m1 v ρ2 ρ) \/
         (is_ub_state s ρ /\ StateWithUB_acf LockStep (acf T) (PState ρ) i = None)) as HCs.
  { destruct m1; easy. }
  destruct HCs as [HCs | HCs].
  2: { split; [right |]; easy. }
  destruct HCs as [Hs Hret].
  assert(PState ρ = PState ρ2) as Hρ2. { unfold mapRetPoss in Hret. easy. }
  destruct Hpost as [Hpost | Hub].
  { destruct Hpost as [? [? Hvalid]].
    split.
    { left. apply valid_state_easy with (s := s2)(ρ := ρ2); subst s; easy. }
    { rewrite Hρ2. eapply valid_state_idle. apply Hvalid. }
  }
  { destruct Hub as [Hub ?]. rewrite Hρ2. split; [| easy].
    right. apply is_ub_state_easy with (s := s2)(ρ := ρ2); subst s; easy.
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

Lemma SpinLock_all_return_aux {T} : 
  forall (i: Name T) A m v, ReturnStep i (Guar i) (Posts i A m v) m v (CSs i A m v).
Proof.
  unfold ReturnStep.
  intros.
  destruct H as [s0 [ρs0 ?]].
  unfold Posts in H.
  destruct H as [ρ [? ?]].
  assert(
    (match m with
    | Acq => (PCalls ρ i = CallDone Acq /\ PRets ρ i = RetPoss Acq tt /\ i_owns i s ρ /\ fst s i = Cont m (Return v))
    | Rel => (PCalls ρ i = CallDone Rel /\ PRets ρ i = RetPoss Rel tt /\ i_not_owns i s ρ /\ fst s i = Cont m (Return v))
    end) 
    \/ 
    (match m with
    | Acq =>
      (((PCalls ρ i = CallPoss Acq /\ PRets ρ i = RetIdle) \/
            (PCalls ρ i = CallDone Acq /\ PRets ρ i = RetPoss Acq tt)) /\
          is_ub_state s ρ /\ StateWithUB_acf _ (acf T) (PState ρ) i = None)
    | Rel =>
      (((PCalls ρ i = CallPoss Rel /\ PRets ρ i = RetIdle) \/
            (PCalls ρ i = CallDone Rel /\ PRets ρ i = RetPoss Rel tt)) /\
          is_ub_state s ρ /\ StateWithUB_acf _ (acf T) (PState ρ) i = None)
    end)) as HH.
  { destruct m; simpl in *.
    { destruct H1.
      { left. easy. }
      { right. easy. }
    }
    { destruct H1.
      { left. easy. }
      { right. easy. }
    }
  }
  clear H1. rename HH into H2. 
  destruct H2.
  {
    exists ρs.
    split.
    { exists ρ. rewrite H. reflexivity. }
    split.
    { intros. exists σ. split; [easy | constructor]. }
    split.
    { intros.
      pose proof Poss_eq_unique _ _ _ H H2 as Htmp. subst σ.
      destruct m; destruct v; destruct H1; try easy.
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
      destruct m; left; easy.
    }
    { unfold Guar.
      intros.
      pose proof Poss_eq_unique2 _ _ _ H H2 as Htmp. subst ρ0.
      exists (MkmapRetPoss i m ρ).
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
      { intros. left. apply i_owns_rel_easy with (s := s)(ρ := ρ); easy. }
      split.
      { intros. left. apply unowns_acq_easy with (s := s)(ρ := ρ); easy. }
      split.
      { intros. left. apply other_owns_acq_easy with (s := s)(ρ := ρ); easy. }
      split.
      { intros. apply is_ub_state_easy with (s := s)(ρ := ρ); easy. }
      split.
      { intros. simpl. assert(i <> j) as n by easy. rewrite (eqb_nid _ _ n). easy. }
      { intros. simpl. easy. }
    }
  }
  { assert (exists v', ((PCalls ρ i = CallPoss m /\ PRets ρ i = RetIdle) \/
          (PCalls ρ i = CallDone m /\ PRets ρ i = RetPoss m v')) /\
        is_ub_state s ρ).
    { destruct m.
      { exists tt. easy. }
      { exists tt. easy. }
    }
    destruct H2 as [v' [HPos Hub]].
    destruct HPos.
    { exists (eq (stateStepToUB ρ i m v')).
      split. { eexists. reflexivity. }
      split.
      { intros. exists ρ.
        split; [subst ρs; easy |].
        subst σ.
        apply stateStepToUBPossSteps; try easy.
        { destruct m; easy. }
        { apply stateStepToUBPreUBStep.
          { destruct Hub. exists x. easy. }
          { destruct m; easy. }
        }
      }
      split.
      { intros. subst σ. unfold stateStepToUB. simpl. rewrite eqb_id.
        destruct m; destruct v; destruct v'; easy.
      }
      split.
      { unfold CSs.
        exists ρ.
        exists (MkmapRetPoss i m (stateStepToUB ρ i m v')).
        split; [subst ρs; easy |].
        split.
        { apply MkmapRetPoss_eq. 
          { easy. }
          { unfold stateStepToUB. simpl. rewrite eqb_id. easy. }
          { unfold stateStepToUB. simpl. rewrite eqb_id. destruct m; destruct v; destruct v'; easy. }
        }
        { destruct m.
          { right. split.
            { apply is_ub_state_easy2. eexists. unfold MkmapRetPoss, stateStepToUB. simpl. reflexivity. }
            { unfold MkmapRetPoss, stateStepToUB. simpl. easy. }
          }
          { right. split.
            { apply is_ub_state_easy2. eexists. unfold MkmapRetPoss, stateStepToUB. simpl. reflexivity. }
            { unfold MkmapRetPoss, stateStepToUB. simpl. easy. }
          }
        }
      }
      { unfold Guar.
        intros.
        pose proof Poss_eq_unique2 _ _ _ H H3 as Htmp. subst ρ0.
        exists (MkmapRetPoss i m (stateStepToUB ρ i m v')).
        split.
        { apply MkmapRetPoss_eq. 
          { easy. }
          { unfold stateStepToUB. simpl. rewrite eqb_id. easy. }
          { unfold stateStepToUB. simpl. rewrite eqb_id. destruct m; destruct v; destruct v'; easy. }
        }
        split.
        { intros. simpl. assert(i <> j) as n by easy. rewrite (eqb_nid _ _ n). easy. }
        split.
        { intros. pose proof iowns_isub_exclusive _ _ _ H5 Hub. easy. }
        split.
        { intros. pose proof inotowns_isub_exclusive _ _ _ H5 Hub. easy. }
        split.
        { intros. pose proof iownsrel_isub_exclusive _ _ _ H5 Hub. easy. }
        split.
        { intros. pose proof unownsacq_isub_exclusive _ _ _ H5 Hub. easy. }
        split.
        { intros. pose proof isub_otherownsacq_exclusive _ _ _ Hub H5. easy. }
        split.
        { intros. apply is_ub_state_easy2. unfold MkmapRetPoss, stateStepToUB. simpl. eexists. reflexivity. }
        split.
        { intros. simpl. assert(i <> j) as n by easy. rewrite (eqb_nid _ _ n). easy. }
        { intros. simpl. easy. }
      }
    }
    { exists (eq ρ).
      split; [exists ρ; easy |].
      split.
      { intros. subst. exists σ. split; [easy | constructor]. }
      split.
      { intros. subst. destruct m; destruct v; destruct v'; easy. }
      split.
      { unfold CSs.
        exists ρ, (MkmapRetPoss i m ρ).
        split; [easy |].
        split.
        { apply MkmapRetPoss_eq. 
          { easy. }
          { destruct m; easy. }
          { destruct m; destruct v; destruct v'; easy. }
        }
        { destruct m.
          { right. split.
            { unfold MkmapRetPoss. apply is_ub_state_easy with (s := s) (ρ := ρ); easy. }
            { unfold MkmapRetPoss. simpl. easy. }
          }
          { right. split.
            { unfold MkmapRetPoss. apply is_ub_state_easy with (s := s) (ρ := ρ); easy. }
            { unfold MkmapRetPoss. simpl. easy. }
          }
        }
      }
      { unfold Guar. intros.
        pose proof Poss_eq_unique2 _ _ _ H H3 as Htmp. subst ρ0.
        exists (MkmapRetPoss i m ρ).
        split.
        { apply MkmapRetPoss_eq. 
          { easy. }
          { destruct m; easy. }
          { destruct m; destruct v; destruct v'; easy. }
        }
        split.
        { intros. simpl. assert(i <> j) as n by easy. rewrite (eqb_nid _ _ n). easy. }
        split.
        { intros. pose proof iowns_isub_exclusive _ _ _ H5 Hub. easy. }
        split.
        { intros. pose proof inotowns_isub_exclusive _ _ _ H5 Hub. easy. }
        split.
        { intros. pose proof iownsrel_isub_exclusive _ _ _ H5 Hub. easy. }
        split.
        { intros. pose proof unownsacq_isub_exclusive _ _ _ H5 Hub. easy. }
        split.
        { intros. pose proof isub_otherownsacq_exclusive _ _ _ Hub H5. easy. }
        split.
        { intros. unfold MkmapRetPoss. apply is_ub_state_easy with (s := s) (ρ := ρ); easy. }
        split.
        { intros. simpl. assert(i <> j) as n by easy. rewrite (eqb_nid _ _ n). easy. }
        { intros. simpl. easy. }
      }
    }
  }
Qed.

Lemma ReturnStepWeaken {T} i (A: Type) (m: F A) v P (G Q CS: (ReltU T)):
  ReturnStep i G (ReltToPrec Q) m v CS -> 
  ReturnStep i G (P <<- Q) m v CS.
Proof.
  intros.
  unfold ReturnStep in *.
  intros.
  assert((ReltToPrec Q) s ρs).
  { unfold PrecCompose in H0. destruct H0 as [s' [ρs' [? ?]]].
    exists s', ρs'. easy.
  }
  specialize (H _ _ H2 H1).
  assumption.
Qed.

Lemma SpinLock_all_return {T} : 
  forall (i: Name T) A m v, ReturnStep i (Guar i) (Precs i A m <<-  Posts i A m v) m v (CSs i A m v).
Proof.
  intros. 
  apply ReturnStepWeaken.
  apply SpinLock_all_return_aux.
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
     (unowns_acq i s ρ /\ unowns_acq i t σ) \/
     (i_owns_rel i s ρ /\ i_owns_rel i t σ) \/
     (is_ub_state s ρ /\ is_ub_state t σ)).
Proof.
  extensionality s. extensionality ρs.
  extensionality t. extensionality σs.
  apply propositional_extensionality.
  split; intros.
  { destruct H as [H1 H2].
    destruct H1 as [ρ [Hρ Htmp]].
    assert((valid_state i s ρ \/ is_ub_state s ρ) /\ StateWithUB_acf LockStep (acf T) (PState ρ) i = None) as HPrecs. {
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
    { destruct HPrecs as [Hvalid | Hub].
      { destruct Hvalid as [Howns | [Hother_owns | [Hunowns | [Hunowns_acq | [Howns_rel | Hother_owns_rel]]]]].
        { left. split; [easy |]. apply i_owns_easy with (s := s)(ρ := ρ); easy. }
        { right. left.
          assert(i_not_owns i s ρ) as Hnotowns.
          { left. easy. } 
          split; [easy |]. apply i_not_owns_easy with (s := s)(ρ := ρ); easy.
        } 
        { right. left. 
          assert(i_not_owns i s ρ) as Hnotowns.
          { right. left. easy. } 
          split; [easy |]. apply i_not_owns_easy with (s := s)(ρ := ρ); easy.
        }
        { right.
          destruct Hunowns_acq as [j Hunowns_acq].
          destruct (classicT (i = j)).
          { subst j.
            right. left. 
            split; [easy |]. apply unowns_acq_easy with (s := s)(ρ := ρ); easy.
          } 
          { left. 
            assert(i_not_owns i s ρ) as Hnotowns.
            { right. right. left. exists j. easy. }
            split; [easy |]. apply i_not_owns_easy with (s := s)(ρ := ρ); easy.
          }
        }
        { right. right. right. left. 
          split; [easy |]. apply i_owns_rel_easy with (s := s)(ρ := ρ); easy.
        }
        { right. left. 
          assert(i_not_owns i s ρ) as Hnotowns.
          { right. right. right. easy. } 
          split; [easy |]. apply i_not_owns_easy with (s := s)(ρ := ρ); easy.
        }
      }
      { right. right. right. right. 
        split; [easy |]. apply is_ub_state_easy with (s := s)(ρ := ρ); easy.
      }
    }
  }
  { destruct H as [ρ [σ [Hρ [Hσ H]]]].
    unfold prComp.
    split.
    { unfold Precs.
      exists ρ. split; [easy |].
      cut((valid_state i s ρ \/ is_ub_state s ρ) /\ StateWithUB_acf LockStep (acf T) (PState ρ) i = None).
      { destruct m; easy. }
      { destruct_all. split; [| easy].
        destruct H11 as [Howns | [Hnotowns | [Hunowns_acq | [Howns_rel | Hub]]]].
        { left. left. easy. }
        { left. apply i_not_owns_valid. easy. }
        { left. right. right. right. left. exists i. easy. }
        { left. right. right. right. right. left. easy. }
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
    ((i_owns i s ρ /\ (i_owns i t σ \/ is_ub_state t σ)) \/ 
     (i_not_owns i s ρ /\ (i_not_owns i t σ \/ is_ub_state t σ)) \/
     (unowns_acq i s ρ /\ (unowns_acq i t σ \/ is_ub_state t σ)) \/
     (i_owns_rel i s ρ /\ (i_owns_rel i t σ \/ is_ub_state t σ)) \/
     (is_ub_state s ρ /\ is_ub_state t σ)) /\
    (other_owns_acq i s ρ -> other_owns_acq i t σ \/ is_ub_state t σ).
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
    { destruct_all. rewrite <- H9. rewrite <- H14. easy. }
    { destruct_all. rewrite <- H7. easy. }
    { destruct_all. rewrite <- H8. easy. }
    { destruct_all. destruct H21 as [Howns | [Hnotowns | [Hunowns_acq | [Howns_rel | Hub]]]].
      { left. split; [easy |]. apply H1. easy. }
      { right. left. split; [easy |]. apply H2. easy. }
      { right. right. left. split; [easy |]. apply H4. easy. }
      { right. right. right. left. split; [easy |]. apply H3. easy. }
      { right. right. right. right. split; [easy |]. apply H6. easy. }
    }
    { intros. assert(other_owns_acq i s' ρ'). { apply other_owns_acq_easy with (s := s)(ρ := ρ); easy. }
      destruct_all. apply H7. easy.
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
      destruct H7 as [Howns | [Hnotowns | [Hunowns_acq | [Howns_rel | Hub]]]].
      { left. split; [easy |]. apply i_owns_easy with (s := s)(ρ := ρ); easy. }
      { right. left. split; [easy |]. apply i_not_owns_easy with (s := s)(ρ := ρ); easy. }
      { right. right. left. split; [easy |]. apply unowns_acq_easy with (s := s)(ρ := ρ); easy. }
      { right. right. right. left. split; [easy |]. apply i_owns_rel_easy with (s := s)(ρ := ρ); easy. }
      { right. right. right. right. split; [easy |]. apply is_ub_state_easy with (s := s)(ρ := ρ); easy. }
    }
    { unfold Rely. intros ρ0 Hρ0.
      pose proof Poss_eq_unique3 _ _ Hρ0 as Htmp. subst ρ0. clear Hρ0.
      exists σ.
      simpl. rewrite eqb_id.
      destruct H as [? [? [? [? [? [? [? [? [Hpos Hother_owns_acq]]]]]]]]].
      assert(PState ρ = PState ρ') as Hρ'. { subst ρ'. reflexivity. }
      assert(i_owns i s ρ \/ i_not_owns i s ρ \/ unowns_acq i s ρ \/ i_owns_rel i s ρ \/ is_ub_state s ρ) as HH.
      { destruct Hpos as [Howns | [Hnotowns | [Hunowns_acq | [Howns_rel | Hub]]]].
        { left. easy. }
        { right. left. easy. }
        { right. right. left. easy. }
        { right. right. right. left. easy. } 
        { right. right. right. right. easy. }
      }
      repeat split; try easy.
      { intros Howns. 
        assert(i_owns i s ρ) as Howns'.
        { eapply i_owns_easy. 3: apply Howns. easy. easy. }
        clear Howns.
        destruct Hpos as [Howns | [Hunowns | [Hunowns_acq | [Howns_rel | Hub]]]].
        { destruct Howns as [Howns ?]. easy. }
        { destruct Hunowns as [Hunowns ?].
          pose proof iowns_inotowns_exclusive _ _ _ Howns'. contradiction.
        }
        { destruct Hunowns_acq as [Hunowns_acq ?].
          pose proof iowns_unownsacq_exclusive _ _ _ Howns'. contradiction.
        }
        { destruct Howns_rel as [Howns_rel ?].
          pose proof iowns_iownsrel_exclusive _ _ _ Howns'. contradiction.
        }
        { destruct Hub as [Hub ?].
          pose proof iowns_isub_exclusive _ _ _ Howns'. contradiction.
        }
      }
      { intros Hnotowns.
        assert(i_not_owns i s ρ) as Hnotowns'.
        { eapply i_not_owns_easy. 3: apply Hnotowns. easy. easy. }
        destruct Hpos as [Howns | [Hunowns | [Hunowns | [Howns_rel | Hub]]]].
        { destruct Howns as [Howns ?].
          pose proof iowns_inotowns_exclusive _ _ _ Howns. contradiction.
        }
        { easy. }
        { destruct Hunowns as [Hunowns ?].
          pose proof inotowns_unownsacq_exclusive _ _ _ Hnotowns'. contradiction.
        }
        { destruct Howns_rel as [Howns_rel ?].
          pose proof inotowns_iownsrel_exclusive _ _ _ Hnotowns'. contradiction.
        }
        { destruct Hub as [Hub ?].
          pose proof inotowns_isub_exclusive _ _ _ Hnotowns'. contradiction.
        }
      }
      { intros Howns_rel.
        assert(i_owns_rel i s ρ) as Howns_rel'.
        { eapply i_owns_rel_easy. 3: apply Howns_rel. easy. easy. }
        clear Howns_rel.
        destruct Hpos as [Howns | [Hunowns | [Hunowns | [Howns_rel | Hub]]]].
        { destruct Howns as [Howns ?]. pose proof iowns_iownsrel_exclusive _ _ _ Howns. contradiction. }
        { destruct Hunowns as [Hunowns ?]. pose proof inotowns_iownsrel_exclusive _ _ _ Hunowns. contradiction. }
        { destruct Hunowns as [Hunowns ?]. pose proof unownsacq_iownsrel_exclusive _ _ _ Hunowns. contradiction. }
        { easy. }
        { destruct Hub as [Hub ?]. pose proof isub_iownsrel_exclusive i _ _ Hub. contradiction. }
      }
      { intros Hunowns_acq.
        assert(unowns_acq i s ρ) as Hunowns_acq'.
        { eapply unowns_acq_easy. 3: apply Hunowns_acq. easy. easy. }
        clear Hunowns_acq.
        destruct Hpos as [Howns | [Hunowns | [Hunowns | [Howns_rel | Hub]]]].
        { destruct Howns as [Howns ?]. pose proof iowns_unownsacq_exclusive _ _ _ Howns. contradiction. }
        { destruct Hunowns as [Hunowns ?]. pose proof inotowns_unownsacq_exclusive _ _ _ Hunowns. contradiction. }
        { easy. }
        { destruct Howns_rel as [Howns_rel ?]. pose proof iownsrel_unownsacq_exclusive _ _ _ Howns_rel. contradiction. }
        { destruct Hub as [Hub ?]. pose proof isub_unownsacq_exclusive i _ _ Hub. contradiction. }
      }
      { intros Hother_owns_acq''.
        assert(i_not_owns i s ρ) as Hnotowns'.
        { left. unfold other_owns. unfold other_owns_acq in Hother_owns_acq''.
          destruct Hother_owns_acq'' as [j [Hneq [Hstate Hsnds]]].
          exists j. split; [easy |]. unfold i_owns. 
          split. { elim_corece. rewrite Hρ'. easy. }
          right. exists i. easy. 
        }
        assert(other_owns_acq i s ρ) as Hother_owns_acq'.
        { eapply other_owns_acq_easy. 3: apply Hother_owns_acq''. easy. easy. }
        destruct Hpos as [Howns | [Hunowns | [Hunowns | [Howns_rel | Hub]]]].
        { destruct Howns as [Howns ?].
          pose proof iowns_inotowns_exclusive _ _ _ Howns. contradiction.
        }
        { apply Hother_owns_acq. easy. }
        { destruct Hunowns as [Hunowns ?].
          pose proof inotowns_unownsacq_exclusive _ _ _ Hnotowns'. contradiction.
        }
        { destruct Howns_rel as [Howns_rel ?].
          pose proof inotowns_iownsrel_exclusive _ _ _ Hnotowns'. contradiction.
        }
        { destruct Hub as [Hub ?].
          pose proof inotowns_isub_exclusive _ _ _ Hnotowns'. contradiction.
        }
      }
      { intros Hub.
        assert(is_ub_state s ρ) as Hub'.
        { eapply is_ub_state_easy. 2: apply Hub. easy. }
        clear Hub.
        destruct Hpos as [Howns | [Hunowns | [Hunowns | [Howns_rel | Hub]]]].
        { destruct Howns as [Howns ?]. pose proof iowns_isub_exclusive _ _ _ Howns. contradiction. }
        { destruct Hunowns as [Hunowns ?]. pose proof inotowns_isub_exclusive _ _ _ Hunowns. contradiction. }
        { destruct Hunowns as [Hunowns ?]. pose proof unownsacq_isub_exclusive _ _ _ Hunowns. contradiction. }
        { destruct Howns_rel as [Howns_rel ?]. pose proof iownsrel_isub_exclusive _ _ _ Howns_rel. contradiction. }
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
      StateWithUB_acf _ (acf T) (PState ρ) i = None /\
      (((PCalls ρ i = CallPoss Acq /\ PRets ρ i = RetIdle) /\
        (fst s i = Cont Acq (SpinLockImpl unit Acq)) /\
        (i_owns i s ρ \/ i_not_owns i s ρ \/ unowns_acq i s ρ \/ i_owns_rel i s ρ)) \/ 
      (((PCalls ρ i = CallPoss Acq /\ PRets ρ i = RetIdle) \/
           (PCalls ρ i = CallDone Acq /\ PRets ρ i = RetPoss Acq tt)) /\
          is_ub_state s ρ))).
  2: {
    unfold sub, subRelt.
    intros.
    rename ρ into ρs.
    rename σ into σs.
    destruct H as [ρ [σ [? [? ?]]]].
    exists σ.
    repeat split; try easy.
    destruct_all.
    destruct H9 as [Howns | [Hunowns | [Hunowns_acq | [Howns_rel | Hub]]]].
    { destruct Howns as [Howns HT].
      destruct HT.
      { left. split; [easy |]. split; [easy |]. left. easy. }
      { right. split; [| easy]. left. easy. }
    }
    { destruct Hunowns as [Hunowns HT].
      destruct HT.
      { left. split; [easy |]. split; [easy |]. right. left. easy. }
      { right. split; [| easy]. left. easy. }
    }
    { destruct Hunowns_acq as [Hunowns_acq HT].
      destruct HT.
      { left. split; [easy |]. split; [easy |]. right. right. left. easy. }
      { right. split; [| easy]. left. easy. }
    }
    { destruct Howns_rel as [Howns_rel HT].
      destruct HT.
      { left. split; [easy |]. split; [easy |]. right. right. right. easy. }
      { right. split; [| easy]. left. easy. }
    }
    { right. split; [| easy]. left. easy. }
  }
  eapply weakenPost.
  {
    eapply (lemWhileSkip2
      (I := (fun v _ _ t σs => exists (σ: Poss (VFU T)), σs = eq σ /\
        StateWithUB_acf _ (acf T) (PState σ) i = None /\
        ((v = true /\ 
            fst t i = Cont Acq (Tau (SpinLockImpl unit Acq)) /\
            PCalls σ i = CallPoss Acq /\ PRets σ i = RetIdle /\
            (i_owns i t σ \/ i_not_owns i t σ)) \/
         (v = false /\
            fst t i = Cont Acq (Return tt) /\
            PCalls σ i = CallDone Acq /\ PRets σ i = RetPoss Acq tt /\
            (i_owns i t σ)) \/
         (((PCalls σ i = CallPoss Acq /\ PRets σ i = RetIdle) \/
           (PCalls σ i = CallDone Acq /\ PRets σ i = RetPoss Acq tt)) /\
          is_ub_state t σ))))).
    { apply SpinLock_R_refl. }
    { apply SpinLock_R_trans. } 
    { apply calcSilentPostGuar.
      intros.
      unfold calcSilentPost.
      split. { apply H. }
      repeat split; try easy.
      unfold Guar. intros. exists ρ. simpl.
      repeat split; try easy.
      { intros. simpl. unfold differ_pointwise in H0. specialize (H0 j (ltac:(easy))). easy. }
      { intros. left. apply i_owns_easy with (s := (ths, s))(ρ := ρ); easy. }
      { intros. left. apply i_not_owns_easy with (s := (ths, s))(ρ := ρ); easy. }
      { intros. left. apply i_owns_rel_easy with (s := (ths, s))(ρ := ρ); easy. }
      { intros. left. apply unowns_acq_easy with (s := (ths, s))(ρ := ρ); easy. }
      { intros. left. apply other_owns_acq_easy with (s := (ths, s))(ρ := ρ); easy. }
    }
    { eapply subReltTrans with (R2 :=
      (fun (_ : InterState F (VE T)) (_ : PossSet (VFU T)) (s : (Name T -> ThreadState (CASSig bool) F) * State (VE T))(ρs : Poss (VFU T) -> Prop) =>
        exists ρ : Poss (VFU T), ρs = eq ρ /\ 
          StateWithUB_acf LockStep (acf T) (PState ρ) i = None /\ 
          (((PCalls ρ i = CallPoss Acq /\ PRets ρ i = RetIdle) /\ 
              (fst s i = Cont Acq (SpinLockImpl unit Acq)) /\ 
              (i_owns i s ρ \/ i_not_owns i s ρ \/ unowns_acq i s ρ \/ i_owns_rel i s ρ)) \/ 
           (((PCalls ρ i = CallPoss Acq /\ PRets ρ i = RetIdle) \/
             (PCalls ρ i = CallDone Acq /\ PRets ρ i = RetPoss Acq tt)) /\
            is_ub_state s ρ))) ->> Rely i).
      {
        rewrite <- reltCompAssoc.
        apply reltComposeMono1.
        unfold sub, subRelt. intros.
        rename ρ into ρs.
        rename σ into σs.
        destruct H as [s' [ρs' [? ?]]].
        destruct H as [ρ' [Hρ' ?]].
        destruct_all.
        unfold calcSilentPost in H0.
        destruct H0. destruct H0 as [_ [_ [ρ'' [Hρ'' ?]]]].
        pose proof Poss_eq_unique2 ρs' ρ' ρ'' (ltac:(easy)) Hρ''. subst ρ''. clear Hρ''.
        destruct H2. subst σs.
        exists ρ'.
        repeat split; try easy.
        destruct_all. destruct H6 as [H6 | [H6 | H6]].
        2: { destruct H6. congruence. }
        { destruct_all.
          left. repeat split; try easy.
          { rewrite H7 in H4. inversion H4. subst. dependent destruction H11.
            unfold E. unfold F. rewrite H12. reflexivity. }
          { destruct H10 as [Howns | Hnotowns].
            { left. apply i_owns_easy with (s := s')(ρ := ρ'); easy. }
            { right. left. apply i_not_owns_easy with (s := s')(ρ := ρ'); easy. }
          } 
        }
        { destruct_all. right. split; [easy |].
          apply is_ub_state_easy with (s := s')(ρ := ρ'); easy.
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
        { rewrite <- H9. easy. }
        destruct H10 as [H10 | Hub].
        { destruct_all.
          rewrite <- H7, <- H8, <- H11.
          destruct H12 as [Howns | [Hnotowns | [Hunowns | Howns_rel]]].
          { specialize (H1 Howns). destruct H1.
            { left. repeat split; try easy. left. easy. }
            { right. split; [| easy]. left. easy. }
          }
          { specialize (H2 Hnotowns). destruct H2.
            { left. repeat split; try easy. right. left. easy. }
            { right. split; [| easy]. left. easy. }
          }
          { specialize (H4 Hunowns). destruct H4.
            { left. repeat split; try easy. right. right. left. easy. }
            { right. split; [| easy]. left. easy. }
          }
          { specialize (H3 Howns_rel). destruct H3.
            { left. repeat split; try easy. right. right. right. easy. }
            { right. split; [| easy]. left. easy. }
          }
        }
        { destruct Hub as [? Hub]. specialize (H6 Hub). right. split; [| easy]. rewrite <- H7, <- H8. easy. }
      }
    }
    { eapply lemVis.
      { eapply (lemCall
          (Q := fun s ρs t σs => exists (ρ σ: Poss (VFU T)), ρs = eq ρ /\ σs = eq σ /\
                  StateWithUB_acf _ (acf T) (PState ρ) i = None /\
                  StateWithUB_acf _ (acf T) (PState σ) i = None /\
                  ((PCalls ρ i = CallPoss Acq /\ PRets ρ i = RetIdle /\
                    PCalls σ i = CallPoss Acq /\ PRets σ i = RetIdle /\
                    fst s i = Cont Acq (SpinLockImpl unit Acq) /\
                    fst t i = UCall Acq (CAS None (Some true))
                                (fun x : bool =>
                                whileAux (tmp <- call (CAS None (Some true)); ret (negb tmp)) skip
                                        (tmp <- Return x; ret (negb tmp)) skip) /\
                    ((unowns s ρ /\ unowns_acq i t σ) \/ (other_owns i s ρ /\ other_owns_acq i t σ))) \/
                  (((PCalls σ i = CallPoss Acq /\ PRets σ i = RetIdle) \/
                    (PCalls σ i = CallDone Acq /\ PRets σ i = RetPoss Acq tt)) /\
                    is_ub_state t σ)))
          (S := fun v s ρs t σs => exists (ρ σ: Poss (VFU T)), ρs = eq ρ /\ σs = eq σ /\
                  StateWithUB_acf _ (acf T) (PState ρ) i = None /\
                  StateWithUB_acf _ (acf T) (PState σ) i = None /\                  
                  (((fst s i = UCall Acq (CAS None (Some true))
                              (fun x : bool =>
                              whileAux (tmp <- call (CAS None (Some true)); ret (negb tmp)) skip
                                       (tmp <- Return x; ret (negb tmp)) skip)) /\
                    ((v = true /\ PCalls ρ i = CallPoss Acq /\ PRets ρ i = RetIdle /\
                        PCalls σ i = CallDone Acq /\ PRets σ i = RetPoss Acq tt /\
                        fst t i = Cont Acq (Return tt) /\
                        ((unowns_acq i s ρ /\ i_owns i t σ))) \/
                     (v = false /\ PCalls ρ i = CallPoss Acq /\ PRets ρ i = RetIdle /\
                        PCalls σ i = CallPoss Acq /\ PRets σ i = RetIdle /\
                        fst t i = Cont Acq (Tau (SpinLockImpl unit Acq)) /\
                        ((other_owns_acq i s ρ /\ i_not_owns i t σ))))) \/
                   (((PCalls σ i = CallPoss Acq /\ PRets σ i = RetIdle) \/
                     (PCalls σ i = CallDone Acq /\ PRets σ i = RetPoss Acq tt)) /\
                     is_ub_state t σ)))).
        { unfold Stable, stableRelt, sub, subRelt.
          intros.
          rename ρ into ρs.
          rename σ into σs.
          destruct H as [s' [ρs' [? ?]]].
          destruct H as [ρ [ρ' [Hρ [Hρ' ?]]]].
          destruct H as [Hstateρ [Hstateρ' Hpos]].
          unfold Rely in H0.
          specialize (H0 _ Hρ').
          destruct H0 as [σ [Hσ H0]].
          destruct H0 as [Hfstt [Howns [Hnotowns [Howns_rel [Howns_acq [Hother_owns_acq Hub]]]]]].
          destruct Hub as [Hub [HPcallρ' [HPretρ' Hstateσ]]].
          exists ρ, σ.
          elim_corece. rewrite <- Hstateσ.
          repeat split; try easy.
          destruct Hpos as [HH | HH].
          { destruct HH as [HPcallρi [HRetsρi [HCallsρ [HRetsρ [Hfsts [Hfsts' HH]]]]]].
            elim_corece. rewrite <- Hfstt, <- HPcallρ', <- HPretρ'. 
            destruct HH as [HH | HH].
            { destruct HH as [Hunownsρ Hunowns_acqρ'].
              specialize (Howns_acq Hunowns_acqρ'). destruct Howns_acq as [Howns_acq | Hub']. 
              { left. do 6 (split; [easy |]). left. easy. }
              { right. split; [| easy]. left. easy. }
            }
            { destruct HH as [Hother_ownsρ Hother_ownsρ'].
              specialize (Hother_owns_acq Hother_ownsρ'). destruct Hother_owns_acq as [Hother_owns_acq | Hub'].
              { left. do 6 (split; [easy |]). right. easy. }
              { right. split; [| easy]. left. easy. }
            }
          }
          { right. destruct HH as [? HH]. specialize (Hub HH). split;[| easy]. 
            rewrite <- HPcallρ', <- HPretρ'. easy. }
        }
        { unfold Stable, stablePost, stableRelt, sub, subRelt. 
          intros.
          rename ρ into ρs.
          rename σ into σs.
          destruct H as [s' [ρs' [? ?]]].
          destruct H as [ρ [ρ' [Hρ [Hρ' ?]]]].
          destruct H as [Hstateρ [Hstateρ' Hpos]].
          unfold Rely in H0.
          specialize (H0 _ Hρ').
          destruct H0 as [σ [Hσ H0]].
          destruct H0 as [Hfstt [Howns [Hnotowns [Howns_rel [Howns_acq [Hother_owns_acq Hub]]]]]].
          destruct Hub as [Hub [HPcallρ' [HPretρ' Hstateσ]]].
          exists ρ, σ.
          elim_corece. rewrite <- Hstateσ, <- HPcallρ', <- HPretρ', <- Hfstt.
          do 4 (split; [easy |]).
          destruct Hpos as [HH | HH].
          { destruct HH as [Hfsts HH].
            destruct HH as [HH | HH].
            {
            destruct HH as [Hv [HCallρ [HRetρ [HCallsρ' [HRetsρ' [Hfsts' HH]]]]]].
            destruct HH as [Hsρ HH].
            specialize (Howns HH). destruct Howns. 
              { left. split; [easy |]. left. easy. }
              { right. split; [| easy]. right. easy. }
            }
            { destruct HH as [Hv [HCallρ [HRetρ [HCallsρ' [HRetsρ' [Hfsts' HH]]]]]].
              destruct HH as [Hsρ HH].
              specialize (Hnotowns HH). destruct Hnotowns.
              { left. split; [easy |]. right. easy. }
              { right. split; [| easy]. left. easy. }
            }
          }
          { right. destruct HH as [? HH]. specialize (Hub HH). split; easy. }
        }
        { unfold Commit. intros.
          destruct H as [s0 [ρs0 [ρ [Hρ [Hstateρ HPrec]]]]].
          destruct HPrec as [HPrec | HH].
          { destruct HPrec as [[HPcallρ HPRetsρ] [Hfsts HPrec]].
            assert(fst t i = UCall Acq (CAS None (Some true))
                                (fun x : bool =>
                                whileAux (tmp <- call (CAS None (Some true)); ret (negb tmp)) skip
                                        (tmp <- Return x; ret (negb tmp)) skip)) as Hfstt.
            { elim_corece. rewrite Hfsts in H1. inversion H1. subst.
              dependent destruction H3. rewrite frobProgId in x at 1. cbn in x. dependent destruction x. easy.
            }
            assert(
              (PState ρ = inl (LockOwned i) /\ snd s = CASDef (Some true) None) \/
              (PState ρ = inl (LockUnowned) /\ snd s = CASDef None None) \/
              (exists j, j <> i /\ PState ρ = inl (LockOwned j) /\ snd s = CASDef (Some true) None)) as HCases.
            {
              destruct HPrec as [Howns | [Hunowns | [Hunowns_acq | Howns_rel]]].
              { left. unfold i_owns in Howns. destruct Howns as [Howns Hsnds].
                destruct Hsnds.
                { easy. }
                { destruct H as [j [Hneq Hsnds]].
                  elim_corece. rewrite Hsnds in H2. inversion H2.
                }
              }
              { unfold i_not_owns in Hunowns.
                destruct Hunowns as [Hother_owns | [Hunowns | [Hunowns_acq | Hother_owns_rel]]].
                { unfold other_owns in Hother_owns. destruct Hother_owns as [j [Hneq Hother_owns]].
                  destruct Hother_owns as [Howns Hsnds].
                  destruct Hsnds.
                  { right. right. exists j. easy. }
                  { destruct H as [j0 [Hneq' Hsnds]].
                    elim_corece. rewrite Hsnds in H2. inversion H2.
                  }
                }
                { right. left. unfold i_not_owns in Hunowns. destruct Hunowns as [Hunowns Hsnds].
                  destruct Hsnds. easy.
                }
                { unfold unowns_acq in Hunowns_acq. 
                  destruct Hunowns_acq as [j [Hneq [Hstate Hsnds]]].
                  elim_corece. rewrite Hsnds in H2. inversion H2.
                }
                { unfold other_owns_rel in Hother_owns_rel. 
                  destruct Hother_owns_rel as [j [Hneq [Hstate Hsnds]]].
                  elim_corece. rewrite Hsnds in H2. inversion H2.
                }
              }
              { unfold unowns_acq in Hunowns_acq. 
                destruct Hunowns_acq as [Hstate Hsnds].
                elim_corece. rewrite Hsnds in H2. inversion H2.
              }
              { unfold i_owns_rel in Howns_rel. destruct Howns_rel as [Howns_rel Hsnds].
                elim_corece. rewrite Hsnds in H2. inversion H2.
              }
            }
            destruct HCases as [HH | [HH | HH]].
            { destruct HH as [Hstate Hsnds].
              assert(is_ub_state t (stateStepToUB ρ i Acq tt)) as Hub.
              { unfold is_ub_state. simpl. 
                exists (StateWithUB_acf LockStep (acf T) (PState ρ)).
                split; [easy |].
                eexists. eexists. elim_corece. 
                rewrite Hsnds in H2. inversion H2; subst.
                elim_corece. rewrite <- H7. reflexivity.
              }
              exists (eq (stateStepToUB ρ i Acq tt)).
              split.
              { eexists. reflexivity. }
              split.
              { intros. subst σ. exists ρ.
                split. { rewrite Hρ. reflexivity. }
                apply stateStepToUBPossSteps; try easy.
                rewrite Hstate. constructor.
                { intros. intro. inversion H. }
                { econstructor; try rewrite eqb_id; try easy.
                  unfold differ_pointwise. intros j Hneq. rewrite eqb_nid. 2: easy.
                  rewrite Hstate. easy.
                }
              }
              split.
              { exists ρ, (stateStepToUB ρ i Acq tt).
                repeat split; try easy.
                right. try easy. split; [| easy].
                right. unfold stateStepToUB. simpl. rewrite eqb_id. easy.
              }
              { unfold Guar. intros ρ' Hρ'.
                pose proof Poss_eq_unique2 _ _ _ Hρ Hρ'; subst ρ'. clear Hρ'.
                eexists. split; [reflexivity |].
                split. { apply differ_pointwise_other. easy. } 
                split. { intros. right. easy. } 
                split. { intros. right. easy. }
                split. { intros. right. easy. }
                split. { intros. right. easy. }
                split. { intros. right. easy. } 
                split. { intros. easy. }
                split. { intros. unfold stateStepToUB. simpl. rewrite eqb_nid; easy. }
                { intros. unfold stateStepToUB. simpl. easy. }
              }
            }
            { exists ρs.
              split. { exists ρ. rewrite Hρ. easy. }
              split.
              { intros σ Hσ. pose proof Poss_eq_unique _ _ _ Hρ Hσ; subst σ. clear Hσ.
                exists ρ. split. { rewrite Hρ. reflexivity. }
                constructor.
              } 
              split.
              { destruct HH as [Hstate Hsnds].
                exists ρ, ρ.
                repeat split; try easy.
                left. do 5 (split; [easy |]). split; [easy |].
                left. split; [easy |].
                rewrite Hsnds in H2. inversion H2; subst. unfold unowns_acq. unfold CAS_i_acq.
                elim_corece. rewrite <- H7.
                split; [easy |].
                easy.
              }
              { unfold Guar.
                assert(unowns s ρ) as Hunowns. { unfold unowns. easy. }
                intros ρ' Hρ'.
                pose proof Poss_eq_unique2 _ _ _ Hρ Hρ'; subst ρ'. clear Hρ'.
                exists ρ.
                repeat split; try easy; intros.
                { unfold differ_pointwise in H0. specialize (H0 j (ltac:(easy))). easy. }
                { pose proof i_owns_unowns_exclusive _ _ _ H3 Hunowns. contradiction. }
                { left. unfold i_not_owns. right. right. left.
                  destruct HH as [Hstate Hsnds].
                  exists i. split; [easy |].
                  rewrite Hsnds in H2. inversion H2; subst. easy.
                }
                { assert (i_not_owns j s ρ) as Hnotowns. { right. left. easy. }
                  pose proof inotowns_iownsrel_exclusive _ _ _ Hnotowns H3. contradiction.
                }
                { destruct HH as [Hstate Hsnds].
                  destruct H3. elim_corece. rewrite H4 in Hsnds. inversion Hsnds.
                }
                { destruct HH as [Hstate Hsnds].
                  destruct H3 as [j0 [Hneq' [? H4]]]. elim_corece. rewrite H4 in Hsnds. inversion Hsnds.
                }
                { assert (i_not_owns i s ρ) as Hnotowns. { right. left. easy. }
                  pose proof inotowns_isub_exclusive _ _ _ Hnotowns H. contradiction.
                }
              }
            }
            { destruct HH as [j [Hneq [Hstate Hsnds]]].
              exists ρs.
              split. { exists ρ. rewrite Hρ. easy. }
              split.
              { intros σ Hσ. pose proof Poss_eq_unique _ _ _ Hρ Hσ; subst σ. clear Hσ.
                exists ρ. split. { rewrite Hρ. reflexivity. }
                constructor.
              }
              split.
              { exists ρ, ρ.
                repeat split; try easy.
                left. do 6 (split; [easy |]).
                right. split. { unfold other_owns. exists j. split; [easy |]. unfold i_owns. split; [easy |]. left. easy. } 
                rewrite Hsnds in H2. inversion H2; subst. unfold other_owns_acq. unfold CAS_i_acq.
                unfold other_owns. exists j. split; [easy |]. unfold i_owns. split; [easy |]. easy.
              }
              { unfold Guar.
                assert(other_owns i s ρ) as Howns. { unfold other_owns. exists j. split; [easy |]. unfold i_owns. split; [easy |]. left. easy. }
                intros ρ' Hρ'.
                pose proof Poss_eq_unique2 _ _ _ Hρ Hρ'; subst ρ'. clear Hρ'.
                exists ρ.
                repeat split; try easy; intros.
                { unfold differ_pointwise in H0. specialize (H0 j0 (ltac:(easy))). easy. }
                { left.
                  unfold i_owns in *.
                  destruct H3 as [Hstate' Hsnds'].
                  rewrite Hstate' in Hstate. inversion Hstate; subst.
                  split; [easy |].
                  right. exists i. split; [easy |].
                  rewrite Hsnds in H2. inversion H2; subst. easy.
                }
                { rewrite Hsnds in H2. inversion H2; subst.
                  left. left. exists j.
                  assert(j <> j0).
                  { intro. subst j0. assert(i_owns j s ρ) as Htmp. { unfold i_owns. split; [easy |]. left. easy. }
                    pose proof iowns_inotowns_exclusive _ _ _ Htmp H3. contradiction.
                  }
                  split; [easy |]. split; [easy |]. right. exists i. easy.
                }
                { unfold i_owns_rel in H3. destruct H3 as [Howns_rel Hsnds'].
                  elim_corece. rewrite Hsnds in Hsnds'. inversion Hsnds'.
                }
                { unfold unowns_acq in H3. destruct H3 as [Hstate' Hsnds'].
                  elim_corece. rewrite Hsnds in Hsnds'. inversion Hsnds'.
                }
                { rewrite Hsnds in H2. inversion H2; subst. left. unfold other_owns_acq in H3.
                  destruct H3 as [j' [Hneq' [Hstate' Hsnds']]].
                  elim_corece. rewrite Hsnds' in Hsnds. inversion Hsnds.
                }
                { assert(i_owns j s ρ) as Howns'. { unfold i_owns. split; [easy |]. left. easy. }
                  pose proof iowns_isub_exclusive _ _ _ Howns' H. contradiction.
                }
              }
            }
          }
          { pose proof HH as Hub. unfold is_ub_state in HH.
            destruct HH as [a [Hstate [o [mm Hsnds]]]].
            assert(is_ub_state t ρ) as Hub'.
            { apply is_ub_state_easy with (s := s)(ρ := ρ); easy. }
            exists (eq ρ).
            split.
            { eexists. reflexivity. }
            split.
            { intros. subst σ. exists ρ.
              split. { rewrite Hρ. reflexivity. }
              constructor.
            }
            split.
            { exists ρ, ρ.
              repeat split; try easy.
              right. split; easy.
            }
            { unfold Guar. intros ρ' Hρ'.
              pose proof Poss_eq_unique2 _ _ _ Hρ Hρ'; subst ρ'. clear Hρ'.
              eexists. split; [reflexivity |].
              split. { apply differ_pointwise_other. easy. } 
              split. { intros. right. easy. } 
              split. { intros. right. easy. }
              split. { intros. right. easy. }
              split. { intros. right. easy. }
              split. { intros. right. easy. }
              split. { intros. easy. }
              split. { intros. easy. }
              { intros. easy. }
            }
          }
        }
        { intros v.
          unfold Commit. intros.
          destruct H as [s0 [ρs0 [s1 [ρs1 ?]]]].
          destruct H as [HPrec HPost].
          destruct HPrec as [ρ1 [Hρ1 [Hstateρ1 HPrec]]].
          destruct HPost as [ρ1' [ρ [Hρ1' [Hρ [Hstateρ1' [Hstateρ HPost]]]]]].
          assert((PCalls ρ i = CallPoss Acq /\ PRets ρ i = RetIdle /\ 
                  fst s i = UCall Acq (CAS None (Some true)) (fun x : bool => whileAux (tmp <- call (CAS None (Some true)); ret (negb tmp)) skip (tmp <- Return x; ret (negb tmp)) skip) /\
                  (unowns s1 ρ1' /\ unowns_acq i s ρ \/ other_owns i s1 ρ1' /\ other_owns_acq i s ρ)) \/
                 (((PCalls ρ i = CallPoss Acq /\ PRets ρ i = RetIdle) \/
                   (PCalls ρ i = CallDone Acq /\ PRets ρ i = RetPoss Acq tt)) /\
                  is_ub_state s ρ)) as HPost'.
          { destruct HPost as [HH | HH].
            { destruct HH as [HCallsρ1' [HRetsρ1' [HCallsρ [HRetsρ [Hfsts1 [Hfsts HH]]]]]].
              destruct HH as [HH | HH].
              { left. split; [easy |]. split; [easy |]. split; [easy |]. left. easy. }
              { left. split; [easy |]. split; [easy |]. split; [easy |]. right. easy. }
            }
            { right. easy. }
          }
          clear HPost.
          destruct HPost' as [HCommit | Hub].
          { destruct HCommit as [PCallsρ [PRetsρ [Hfsts HCommit]]].
            destruct HCommit as [HSucc | HFail].
            { destruct HSucc as [_ HSucc].
              pose proof HSucc as HSucc'.
              unfold unowns_acq in HSucc.
              destruct HSucc as [HSρ HSs].
              elim_corece. rewrite HSs in H2.
              unfold CAS_i_acq in H2.
              inversion H2; subst. 2: contradiction.
              dependent destruction H7.
              rewrite Hfsts in H1. inversion H1; subst.
              dependent destruction H3. dependent destruction H6.
              rewrite frobProgId in H9 at 1. cbn in H9.
              remember (@MkPoss T F (VFU T) (inl (LockAcqRan i)) 
                      (fun j => if i =? j then CallDone Acq else PCalls ρ j)
                      (fun j => if i =? j then RetIdle else PRets ρ j)) as ρ'.
              remember (@MkPoss T F (VFU T) (inl (LockOwned i)) 
                      (fun j => if i =? j then CallDone Acq else PCalls ρ' j)
                      (fun j => if i =? j then RetPoss Acq tt else PRets ρ' j)) as ρ''.
              exists (eq ρ'').
              split. { eexists. reflexivity. }
              split.
              { intros. subst σ. exists ρ.
                split. { reflexivity. }
                eapply Logic.PossStepsStep with (i := i) (σ := ρ').
                { subst ρ'. 
                  apply Logic.PCommitCall with (m := Acq); simpl; try rewrite eqb_id; try easy.
                  { rewrite HSρ. constructor. constructor. }
                }
                { subst ρ'. intros. simpl. rewrite eqb_nid; easy. }
                { subst ρ'. intros. simpl. rewrite eqb_nid; easy. }
                eapply Logic.PossStepsStep with (i := i) (σ := ρ'').
                { subst ρ''. subst ρ'.
                  apply Logic.PCommitRet with (m := Acq)(v := tt); simpl; try rewrite eqb_id; try easy.
                  { simpl. constructor. constructor. }
                }
                { subst ρ''. intros. simpl. rewrite eqb_nid; easy. }
                { subst ρ''. intros. simpl. rewrite eqb_nid; easy. }
                constructor.
              }
              split.
              { exists ρ, ρ''.
                repeat split; try easy.
                { subst ρ''. simpl. easy. }
                { left. subst ρ''. simpl. rewrite eqb_id. repeat split; try easy. left. repeat split; try easy. left. easy. } 
              }
              { unfold Guar. intros ρ_ Hρ_.
                pose proof Poss_eq_unique3 _ _ Hρ_; subst ρ_. clear Hρ_.
                eexists. split; [reflexivity |].
                split. { apply differ_pointwise_other. easy. } 
                split. { intros. destruct H3 as [HH ?]. rewrite HSρ in HH. inversion HH. }
                split. 
                { intros. left. left. exists i. split; [easy |].
                  subst ρ''. split; [easy |]. left. easy.
                }
                split. { intros. destruct H3 as [HH ?]. rewrite HSρ in HH. inversion HH. }
                split. { intros. destruct H3 as [? HH]. elim_corece. rewrite HSs in HH. inversion HH. subst j. contradiction. }
                split. { intros. destruct H3 as [? [j0 [? HH]]]. elim_corece. rewrite HSs in HH. inversion HH. }
                split. { intros. destruct H as [a [HH ?]]. elim_corece. rewrite HSρ in HH. inversion HH. }
                split. { intros. subst ρ''. subst ρ'. simpl. rewrite eqb_nid; easy. }
                { intros. subst ρ''. subst ρ'. simpl. rewrite HSρ. easy. }
              }
            }
            { destruct HFail as [_ HFail]. pose proof HFail as HFail'. 
              unfold other_owns_acq in HFail.
              destruct HFail as [j [Hneq [HFρ HFs]]].
              elim_corece. rewrite HFs in H2.
              unfold CAS_i_acq in H2.
              inversion H2; subst. inversion H3.
              dependent destruction H7.
              rewrite Hfsts in H1. inversion H1; subst.
              dependent destruction H4. dependent destruction H7.
              rewrite frobProgId in H10 at 1. cbn in H10.
              replace (whileAux (tmp <- call (CAS None (Some true)); ret (negb tmp)) skip
                               (tmp <- call (CAS None (Some true)); ret (negb tmp)) skip) 
                  with (SpinLockImpl unit Acq) in H10 by easy.
              exists (eq ρ).
              split. { eexists. reflexivity. }
              split. { intros. subst σ. exists ρ. split; [easy | constructor]. }
              split.
              { exists ρ, ρ.
                repeat split; try easy. left. repeat split; try easy. right. repeat split; try easy.
                unfold i_not_owns. left.
                exists j. split; [easy |]. unfold i_owns. split; [easy |]. left. easy.
              }
              { unfold Guar. intros ρ' Hρ'.
                pose proof Poss_eq_unique3 _ _ Hρ'; subst ρ'. clear Hρ'.
                eexists. split; [reflexivity |]. 
                split. { apply differ_pointwise_other. easy. } 
                split. 
                { intros. unfold i_owns in H4. destruct H4 as [HH H4].
                  rewrite HFρ in HH. inversion HH. subst j0.
                  left. unfold i_owns. split; [easy |]. left. easy.
                }
                split.
                { intros. unfold i_not_owns in H4. destruct H4 as [HH | [HH | [HH | HH]]].
                  { unfold other_owns in HH. destruct HH as [j1 [Hneq' [HH H4]]].
                    rewrite HFρ in HH. inversion HH. subst j1.
                    left. left. exists j. split; [easy |]. split; [easy |]. left. easy.
                  }
                  { unfold unowns in HH. destruct HH as [HH H4].
                    rewrite HFρ in HH. inversion HH.
                  }
                  { destruct HH as [j1 [Hneq' H4]].
                    unfold unowns_acq in H4. destruct H4 as [HH H4].
                    rewrite HFρ in HH. inversion HH.
                  }
                  { unfold other_owns_rel in HH. destruct HH as [j1 [Hneq' [? HH]]].
                    elim_corece. rewrite HFs in HH. inversion HH.
                  }
                }
                split. { intros. unfold i_owns_rel in H4. destruct H4 as [H4 HH]. elim_corece. rewrite HFs in HH. inversion HH. }
                split. { intros. unfold unowns_acq in H4. destruct H4 as [HH ?]. rewrite HFρ in HH. inversion HH. }
                split. 
                { intros. unfold other_owns_acq in H4. destruct H4 as [j1 [Hneq' [HH H4]]].
                  elim_corece. rewrite HFs in H4. unfold CAS_i_acq in H4. inversion H4. subst j0.
                  contradiction.
                }
                split. { intros. destruct H as [a [HH H4]]. rewrite HFρ in HH. inversion HH. }
                split; [easy |].
                { intros. easy. }
              }
            }
          }
          { destruct Hub as [? Hub]. pose proof Hub as Hub'.
            destruct Hub as [a [HUρ [m [o HPus]]]].
            rewrite HUρ in Hstateρ. inversion Hstateρ. simpl in *.
            assert(is_ub_state t ρ) as HUbt.
            { apply is_ub_state_easy with (s := s)(ρ := ρ); easy. }
            exists (eq ρ).
            split. { eexists. reflexivity. }
            split. { intros. subst σ. exists ρ. split; [subst ρs; easy | ]. constructor. }
            split.
            { exists ρ, ρ. 
              repeat split; try rewrite HUρ; try easy.
              right. repeat split; try easy.
            }
            { unfold Guar. intros ρ' Hρ'.
              pose proof Poss_eq_unique2 _ _ _ Hρ Hρ'; subst ρ'. clear Hρ'.
              eexists. split; [reflexivity |].
              split. { apply differ_pointwise_other. easy. } 
              split. { intros. right. easy. }
              split. { intros. right. easy. }
              split. { intros. right. easy. }
              split. { intros. right. easy. }
              split. { intros. right. easy. }
              split. { intros. easy. }
              split. { intros. easy. }
              { intros. easy. }
            }
          }
        }
      }
      { intros. apply lemRet.
        unfold sub, subRelt.
        intros.
        rename ρ into ρs.
        rename σ into σs.
        destruct H as [s1 [ρs1 [H0 H]]].
        destruct H as [s2 [ρs2 [H1 H]]].
        destruct H as [ρ2 [σ [Hρ2 [Hσ H]]]].
        destruct H as [Hstateρ2 [Hstateσ HPos]].
        exists σ. split; [easy |].
        split; [easy |].
        destruct HPos as [HPos | Hub].
        { destruct HPos as [Hfsts2 HPos].
          destruct HPos as [Htrue | Hfalse].
          { right.
            destruct Htrue as [Hv [HPCallρ2 [HPRetρ2 [HPCallσ [HPRetσ [Hfstt Hunowns_acqρ2]]]]]].
            subst v. repeat split; try easy. left. easy.
          }
          { left.
            destruct Hfalse as [Hv [HPCallρ2 [HPRetρ2 [HPCallσ [HPRetσ [Hfstt Hunowns_acqρ2]]]]]].
            subst v. repeat split; try easy. right. easy.
          }
        }
        { right. right. easy. }
      }
    }
  }
  { intros. destruct v. unfold UnitRet.
    unfold sub, subRelt.
    intros.
    rename σ into σs.
    rename ρ into ρs.
    destruct H as [σ [Hρ [Hσ Hres]]].
    destruct Hres as [Htrue | [Hfalse | Hub]].
    { destruct Htrue. congruence. }
    { unfold Posts. exists σ.
      split; [easy |].
      left. easy. 
    }
    { unfold Posts. exists σ. split; [easy |].
      right. easy.
    }
  }
Qed.

Lemma SpinLock_Rel_verified {T} :
  forall (i: Name T), 
      VerifyProg i (Rely i) (Guar i) 
      (prComp (Precs i unit Rel) (TInvoke SpinLockImpl i _ Rel) ->> Rely i)
      (SpinLockImpl _ Rel)
      (Posts i unit Rel).
Proof.
  intros.
  simpl.
  unfold SpinLockRel.
  rewrite SpinLock_verify_aux.
  apply weakenPrec with (P := 
    fun _ _ s ρs => exists (ρ: Poss (VFU T)), ρs = eq ρ /\
      StateWithUB_acf _ (acf T) (PState ρ) i = None /\
      (((PCalls ρ i = CallPoss Rel /\ PRets ρ i = RetIdle) /\
        (fst s i = Cont Rel (SpinLockImpl unit Rel)) /\
        (i_owns i s ρ \/ i_not_owns i s ρ \/ unowns_acq i s ρ \/ i_owns_rel i s ρ)) \/ 
      (((PCalls ρ i = CallPoss Rel /\ PRets ρ i = RetIdle) /\
          is_ub_state s ρ)))).
  2: {
    unfold sub, subRelt.
    intros.
    rename ρ into ρs.
    rename σ into σs.
    destruct H as [ρ [σ [? [? ?]]]].
    exists σ.
    repeat split; try easy.
    destruct_all.
    destruct H9 as [Howns | [Hunowns | [Hunowns_acq | [Howns_rel | Hub]]]].
    { destruct Howns as [Howns HT].
      destruct HT.
      { left. split; [easy |]. split; [easy |]. left. easy. }
      { right. split; [| easy]. easy. }
    }
    { destruct Hunowns as [Hunowns HT].
      destruct HT.
      { left. split; [easy |]. split; [easy |]. right. left. easy. }
      { right. split; [| easy]. easy. }
    }
    { destruct Hunowns_acq as [Hunowns_acq HT].
      destruct HT.
      { left. split; [easy |]. split; [easy |]. right. right. left. easy. }
      { right. split; [| easy]. easy. }
    }
    { destruct Howns_rel as [Howns_rel HT].
      destruct HT.
      { left. split; [easy |]. split; [easy |]. right. right. right. easy. }
      { right. split; [| easy]. easy. }
    }
    { right. split; [| easy]. easy. }
  }
  eapply lemVis.
  { eapply (lemCall
      (Q := fun s ρs t σs => exists (ρ σ: Poss (VFU T)), ρs = eq ρ /\ σs = eq σ /\
              StateWithUB_acf _ (acf T) (PState ρ) i = None /\
              StateWithUB_acf _ (acf T) (PState σ) i = None /\
              ((PCalls ρ i = CallPoss Rel /\ PRets ρ i = RetIdle /\
                PCalls σ i = CallPoss Rel /\ PRets σ i = RetIdle /\
                fst s i = Cont Rel (SpinLockImpl unit Rel) /\
                fst t i = UCall Rel (CAS (Some true) None) (fun x : bool => Return x;; ret tt) /\
                ((i_owns i s ρ /\ i_owns_rel i t σ))) \/
              (((PCalls σ i = CallPoss Rel /\ PRets σ i = RetIdle) \/
                (PCalls σ i = CallDone Rel /\ PRets σ i = RetPoss Rel tt)) /\
                is_ub_state t σ)))
      (S := fun v s ρs t σs => exists (ρ σ: Poss (VFU T)), ρs = eq ρ /\ σs = eq σ /\
              StateWithUB_acf _ (acf T) (PState ρ) i = None /\
              StateWithUB_acf _ (acf T) (PState σ) i = None /\                  
              (((fst s i = UCall Rel (CAS (Some true) None) (fun x : bool => Return x;; ret tt)) /\
                ((v = true /\ PCalls ρ i = CallPoss Rel /\ PRets ρ i = RetIdle /\
                    PCalls σ i = CallDone Rel /\ PRets σ i = RetPoss Rel tt /\
                    fst t i = Cont Rel (Return tt) /\
                    ((i_owns_rel i s ρ /\ i_not_owns i t σ))))) \/
                (((PCalls σ i = CallPoss Rel /\ PRets σ i = RetIdle) \/
                  (PCalls σ i = CallDone Rel /\ PRets σ i = RetPoss Rel tt)) /\
                  is_ub_state t σ)))).
        { unfold Stable, stableRelt, sub, subRelt.
          intros.
          rename ρ into ρs.
          rename σ into σs.
          destruct H as [s' [ρs' [? ?]]].
          destruct H as [ρ [ρ' [Hρ [Hρ' ?]]]].
          destruct H as [Hstateρ [Hstateρ' Hpos]].
          unfold Rely in H0.
          specialize (H0 _ Hρ').
          destruct H0 as [σ [Hσ H0]].
          destruct H0 as [Hfstt [Howns [Hnotowns [Howns_rel [Howns_acq [Hother_owns_acq Hub]]]]]].
          destruct Hub as [Hub [HPcallρ' [HPretρ' Hstateσ]]].
          exists ρ, σ.
          elim_corece. rewrite <- Hstateσ.
          repeat split; try easy.
          destruct Hpos as [HH | HH].
          { destruct HH as [HPcallρi [HRetsρi [HCallsρ [HRetsρ [Hfsts [Hfsts' HH]]]]]].
            elim_corece. rewrite <- Hfstt, <- HPcallρ', <- HPretρ'. 
            { destruct HH as [Howns' Howns_rel'].
              specialize (Howns_rel Howns_rel'). destruct Howns_rel as [Howns_rel | Hub']. 
              { left. do 6 (split; [easy |]). easy. } 
              { right. split; [| easy]. left. easy. }
            }
          }
          { right. destruct HH as [? HH]. specialize (Hub HH). split;[| easy]. 
            rewrite <- HPcallρ', <- HPretρ'. easy. }
        }
        { unfold Stable, stablePost, stableRelt, sub, subRelt. 
          intros.
          rename ρ into ρs.
          rename σ into σs.
          destruct H as [s' [ρs' [? ?]]].
          destruct H as [ρ [ρ' [Hρ [Hρ' ?]]]].
          destruct H as [Hstateρ [Hstateρ' Hpos]].
          unfold Rely in H0.
          specialize (H0 _ Hρ').
          destruct H0 as [σ [Hσ H0]].
          destruct H0 as [Hfstt [Howns [Hnotowns [Howns_rel [Howns_acq [Hother_owns_acq Hub]]]]]].
          destruct Hub as [Hub [HPcallρ' [HPretρ' Hstateσ]]].
          exists ρ, σ.
          elim_corece. rewrite <- Hstateσ, <- HPcallρ', <- HPretρ', <- Hfstt.
          do 4 (split; [easy |]).
          destruct Hpos as [HH | HH].
          { destruct HH as [Hfsts HH].
            destruct HH as [Hv [HCallρ [HRetρ [HCallsρ' [HRetsρ' [Hfsts' HH]]]]]].
            destruct HH as [Hsρ HH].
            specialize (Hnotowns HH). destruct Hnotowns. 
              { left. split; [easy |]. easy. }
              { right. split; [| easy]. right. easy. }
          }
          { right. destruct HH as [? HH]. specialize (Hub HH). split; easy. }
        }
        { unfold Commit. intros.
          destruct H as [s0 [ρs0 [ρ [Hρ [Hstateρ HPrec]]]]].
          destruct HPrec as [HPrec | HH].
          { destruct HPrec as [[HPcallρ HPRetsρ] [Hfsts HPrec]].
            assert(fst t i = UCall Rel (CAS (Some true) None) (fun x : bool => Return x;; ret tt)) as Hfstt.
            { elim_corece. rewrite Hfsts in H1. inversion H1. subst.
              dependent destruction H3. rewrite frobProgId in x at 1. cbn in x. dependent destruction x. easy.
            }
            assert(
              (PState ρ = inl (LockOwned i) /\ snd s = CASDef (Some true) None) \/
              (PState ρ = inl (LockUnowned) /\ snd s = CASDef None None) \/
              (exists j, j <> i /\ PState ρ = inl (LockOwned j) /\ snd s = CASDef (Some true) None)) as HCases.
            {
              destruct HPrec as [Howns | [Hunowns | [Hunowns_acq | Howns_rel]]].
              { left. unfold i_owns in Howns. destruct Howns as [Howns Hsnds].
                destruct Hsnds.
                { easy. }
                { destruct H as [j [Hneq Hsnds]].
                  elim_corece. rewrite Hsnds in H2. inversion H2.
                }
              }
              { unfold i_not_owns in Hunowns.
                destruct Hunowns as [Hother_owns | [Hunowns | [Hunowns_acq | Hother_owns_rel]]].
                { unfold other_owns in Hother_owns. destruct Hother_owns as [j [Hneq Hother_owns]].
                  destruct Hother_owns as [Howns Hsnds].
                  destruct Hsnds.
                  { right. right. exists j. easy. }
                  { destruct H as [j0 [Hneq' Hsnds]].
                    elim_corece. rewrite Hsnds in H2. inversion H2.
                  }
                }
                { right. left. unfold i_not_owns in Hunowns. destruct Hunowns as [Hunowns Hsnds].
                  destruct Hsnds. easy.
                }
                { unfold unowns_acq in Hunowns_acq. 
                  destruct Hunowns_acq as [j [Hneq [Hstate Hsnds]]].
                  elim_corece. rewrite Hsnds in H2. inversion H2.
                }
                { unfold other_owns_rel in Hother_owns_rel. 
                  destruct Hother_owns_rel as [j [Hneq [Hstate Hsnds]]].
                  elim_corece. rewrite Hsnds in H2. inversion H2.
                }
              }
              { unfold unowns_acq in Hunowns_acq. 
                destruct Hunowns_acq as [Hstate Hsnds].
                elim_corece. rewrite Hsnds in H2. inversion H2.
              }
              { unfold i_owns_rel in Howns_rel. destruct Howns_rel as [Howns_rel Hsnds].
                elim_corece. rewrite Hsnds in H2. inversion H2.
              }
            }
            destruct HCases as [HH | [HH | HH]].
            { exists ρs.
              destruct HH as [Hstate Hsnds].
              rewrite Hsnds in H2. inversion H2; subst.
              split. { exists ρ. easy. }
              split.
              { intros σ Hσ. subst σ.
                exists ρ. split. { reflexivity. }
                constructor.
              } 
              split.
              { 
                exists ρ, ρ.
                repeat split; try easy.
                left. do 5 (split; [easy |]). split; [easy |].
                split.
                { unfold i_owns. split; [easy |]. left. easy. }
                { unfold i_owns_rel. easy. }
              }
              { unfold Guar.
                assert(i_owns i s ρ) as Howns. { unfold i_owns. split; [easy |]. left. easy. }
                intros ρ' Hρ'.
                pose proof Poss_eq_unique3 _ _ Hρ'; subst ρ'. clear Hρ'.
                exists ρ.
                repeat split; try easy; intros.
                { unfold differ_pointwise in H0. specialize (H0 j (ltac:(easy))). easy. }
                { destruct Howns as [Hi ?]. destruct H3 as [Hj ?].
                  rewrite Hi in Hj. inversion Hj. subst j. congruence.
                }
                { left. unfold i_not_owns. right. right. right.
                  exists i. split; [easy |].
                  unfold i_owns_rel. easy.
                }
                { assert (i_not_owns j s ρ) as Hnotowns. { left. exists i. easy. }
                  pose proof inotowns_iownsrel_exclusive _ _ _ Hnotowns H3. contradiction.
                }
                { destruct H3. elim_corece. rewrite H4 in Hsnds. inversion Hsnds. }
                { destruct H3 as [j0 [Hneq' [? H4]]]. elim_corece. rewrite H4 in Hsnds. inversion Hsnds. }
                { apply is_ub_state_easy with (s := s) (ρ := ρ); easy. }
              }
            }
            { destruct HH as [Hstate Hsnds].
              assert(is_ub_state t (stateStepToUB ρ i Rel tt)) as Hub.
              { unfold is_ub_state. simpl. 
                exists (StateWithUB_acf LockStep (acf T) (PState ρ)).
                split; [easy |].
                eexists. eexists. elim_corece. 
                rewrite Hsnds in H2. inversion H2; subst.
                elim_corece. rewrite <- H7. reflexivity.
              }
              exists (eq (stateStepToUB ρ i Rel tt)).
              split.
              { eexists. reflexivity. }
              split.
              { intros. subst σ. exists ρ.
                split. { rewrite Hρ. reflexivity. }
                apply stateStepToUBPossSteps; try easy.
                rewrite Hstate. constructor.
                { intros. intro. inversion H. }
                { econstructor; try rewrite eqb_id; try easy.
                  unfold differ_pointwise. intros j Hneq. rewrite eqb_nid. 2: easy.
                  rewrite Hstate. easy.
                }
              }
              split.
              { exists ρ, (stateStepToUB ρ i Rel tt).
                repeat split; try easy.
                right. try easy. split; [| easy].
                right. unfold stateStepToUB. simpl. rewrite eqb_id. easy.
              }
              { unfold Guar. intros ρ' Hρ'.
                pose proof Poss_eq_unique2 _ _ _ Hρ Hρ'; subst ρ'. clear Hρ'.
                eexists. split; [reflexivity |].
                split. { apply differ_pointwise_other. easy. } 
                split. { intros. right. easy. } 
                split. { intros. right. easy. }
                split. { intros. right. easy. }
                split. { intros. right. easy. }
                split. { intros. right. easy. } 
                split. { intros. easy. }
                split. { intros. unfold stateStepToUB. simpl. rewrite eqb_nid; easy. }
                { intros. unfold stateStepToUB. simpl. easy. }
              }
            }
            { destruct HH as [j [Hneq [Hstate Hsnds]]].
              assert(is_ub_state t (stateStepToUB ρ i Rel tt)) as Hub.
              { unfold is_ub_state. simpl. 
                exists (StateWithUB_acf LockStep (acf T) (PState ρ)).
                split; [easy |].
                eexists. eexists. elim_corece. 
                rewrite Hsnds in H2. inversion H2; subst.
                elim_corece. rewrite <- H7. reflexivity.
              }
              exists (eq (stateStepToUB ρ i Rel tt)).
              split.
              { eexists. reflexivity. }
              split.
              { intros. subst σ. exists ρ.
                split. { rewrite Hρ. reflexivity. }
                apply stateStepToUBPossSteps; try easy.
                rewrite Hstate. constructor.
                { intros. intro. inversion H; subst. congruence. }
                { econstructor; try rewrite eqb_id; try easy.
                  unfold differ_pointwise. intros j' Hneq'. rewrite eqb_nid. 2: easy.
                  rewrite Hstate. easy.
                }
              }
              split.
              { exists ρ, (stateStepToUB ρ i Rel tt).
                repeat split; try easy.
                right. try easy. split; [| easy].
                right. unfold stateStepToUB. simpl. rewrite eqb_id. easy.
              }
              { unfold Guar. intros ρ' Hρ'.
                pose proof Poss_eq_unique2 _ _ _ Hρ Hρ'; subst ρ'. clear Hρ'.
                eexists. split; [reflexivity |].
                split. { apply differ_pointwise_other. easy. } 
                split. { intros. right. easy. } 
                split. { intros. right. easy. }
                split. { intros. right. easy. }
                split. { intros. right. easy. }
                split. { intros. right. easy. } 
                split. { intros. easy. }
                split. { intros. unfold stateStepToUB. simpl. rewrite eqb_nid; easy. }
                { intros. unfold stateStepToUB. simpl. easy. }
              }
            }
          }
          { pose proof HH as Hub. unfold is_ub_state in HH.
            destruct HH as [a [Hstate [o [mm Hsnds]]]].
            assert(is_ub_state t ρ) as Hub'.
            { apply is_ub_state_easy with (s := s)(ρ := ρ); easy. }
            exists (eq ρ).
            split.
            { eexists. reflexivity. }
            split.
            { intros. subst σ. exists ρ.
              split. { rewrite Hρ. reflexivity. }
              constructor.
            }
            split.
            { exists ρ, ρ.
              repeat split; try easy.
              right. split; [| easy]. 
              left. easy.
            }
            { unfold Guar. intros ρ' Hρ'.
              pose proof Poss_eq_unique2 _ _ _ Hρ Hρ'; subst ρ'. clear Hρ'.
              eexists. split; [reflexivity |].
              split. { apply differ_pointwise_other. easy. } 
              split. { intros. right. easy. } 
              split. { intros. right. easy. }
              split. { intros. right. easy. }
              split. { intros. right. easy. }
              split. { intros. right. easy. }
              split. { intros. easy. }
              split. { intros. easy. }
              { intros. easy. }
            }
          }
        }
        { intros v.
          unfold Commit. intros.
          destruct H as [s0 [ρs0 [s1 [ρs1 ?]]]].
          destruct H as [HPrec HPost].
          destruct HPrec as [ρ1 [Hρ1 [Hstateρ1 HPrec]]].
          destruct HPost as [ρ1' [ρ [Hρ1' [Hρ [Hstateρ1' [Hstateρ HPost]]]]]].
          assert((PCalls ρ i = CallPoss Rel /\ PRets ρ i = RetIdle /\  
                 (fst s i = UCall Rel (CAS (Some true) None) (fun x : bool => Return x;; ret tt)) /\
                  (i_owns i s1 ρ1' /\ i_owns_rel i s ρ)) \/
                 (((PCalls ρ i = CallPoss Rel /\ PRets ρ i = RetIdle) \/
                   (PCalls ρ i = CallDone Rel /\ PRets ρ i = RetPoss Rel tt)) /\
                  is_ub_state s ρ)) as HPost'.
          { destruct HPost as [HH | HH].
            { destruct HH as [HCallsρ1' [HRetsρ1' [HCallsρ [HRetsρ [Hfsts1 [Hfsts HH]]]]]].
              { left. split; [easy |]. split; [easy |]. split; [easy |]. easy. }
            }
            { right. easy. }
          }
          clear HPost.
          destruct HPost' as [HCommit | Hub].
          { destruct HCommit as [PCallsρ [PRetsρ [Hfsts HSucc]]].
            { destruct HSucc as [_ HSucc].
              pose proof HSucc as HSucc'.
              unfold i_owns_rel in HSucc.
              destruct HSucc as [HSρ HSs].
              elim_corece. rewrite HSs in H2.
              unfold CAS_i_rel in H2.
              inversion H2; subst. 2: contradiction.
              dependent destruction H7.
              rewrite Hfsts in H1. inversion H1; subst.
              dependent destruction H3. dependent destruction H6.
              rewrite frobProgId in H9 at 1. cbn in H9.
              remember (@MkPoss T F (VFU T) (inl (LockRelRan i)) 
                      (fun j => if i =? j then CallDone Rel else PCalls ρ j)
                      (fun j => if i =? j then RetIdle else PRets ρ j)) as ρ'.
              remember (@MkPoss T F (VFU T) (inl (LockUnowned)) 
                      (fun j => if i =? j then CallDone Rel else PCalls ρ' j)
                      (fun j => if i =? j then RetPoss Rel tt else PRets ρ' j)) as ρ''.
              exists (eq ρ'').
              split. { eexists. reflexivity. }
              split.
              { intros. subst σ. exists ρ.
                split. { reflexivity. }
                eapply Logic.PossStepsStep with (i := i) (σ := ρ').
                { subst ρ'. 
                  apply Logic.PCommitCall with (m := Rel); simpl; try rewrite eqb_id; try easy.
                  { rewrite HSρ. constructor. constructor. }
                }
                { subst ρ'. intros. simpl. rewrite eqb_nid; easy. }
                { subst ρ'. intros. simpl. rewrite eqb_nid; easy. }
                eapply Logic.PossStepsStep with (i := i) (σ := ρ'').
                { subst ρ''. subst ρ'.
                  apply Logic.PCommitRet with (m := Rel)(v := tt); simpl; try rewrite eqb_id; try easy.
                  { simpl. constructor. constructor. }
                }
                { subst ρ''. intros. simpl. rewrite eqb_nid; easy. }
                { subst ρ''. intros. simpl. rewrite eqb_nid; easy. }
                constructor.
              }
              split.
              { exists ρ, ρ''.
                repeat split; try easy.
                { subst ρ''. simpl. easy. }
                { left. subst ρ''. simpl. rewrite eqb_id. repeat split; try easy. right. left. easy. } 
              }
              { unfold Guar. intros ρ_ Hρ_.
                pose proof Poss_eq_unique3 _ _ Hρ_; subst ρ_. clear Hρ_.
                eexists. split; [reflexivity |].
                split. { apply differ_pointwise_other. easy. } 
                split. { intros. destruct H3 as [HH ?]. rewrite HSρ in HH. inversion HH. subst j. congruence. }
                split. 
                { intros. left. right. left.
                  subst ρ''. split; [easy |]. easy.
                }
                split. { intros. destruct H3 as [HH ?]. rewrite HSρ in HH. inversion HH. subst j; congruence. }
                split. { intros. destruct H3 as [? HH]. elim_corece. rewrite HSs in HH. inversion HH. }
                split. { intros. destruct H3 as [? [j0 [? HH]]]. elim_corece. rewrite HSs in HH. inversion HH. }
                split. { intros. destruct H as [a [HH ?]]. elim_corece. rewrite HSρ in HH. inversion HH. }
                split. { intros. subst ρ''. subst ρ'. simpl. rewrite eqb_nid; easy. }
                { intros. subst ρ''. subst ρ'. simpl. rewrite HSρ. easy. }
              }
            }
          }
          { destruct Hub as [? Hub]. pose proof Hub as Hub'.
            destruct Hub as [a [HUρ [m [o HPus]]]].
            rewrite HUρ in Hstateρ. inversion Hstateρ. simpl in *.
            assert(is_ub_state t ρ) as HUbt.
            { apply is_ub_state_easy with (s := s)(ρ := ρ); easy. }
            exists (eq ρ).
            split. { eexists. reflexivity. }
            split. { intros. subst σ. exists ρ. split; [subst ρs; easy | ]. constructor. }
            split.
            { exists ρ, ρ. 
              repeat split; try rewrite HUρ; try easy.
              right. repeat split; try easy.
            }
            { unfold Guar. intros ρ' Hρ'.
              pose proof Poss_eq_unique2 _ _ _ Hρ Hρ'; subst ρ'. clear Hρ'.
              eexists. split; [reflexivity |].
              split. { apply differ_pointwise_other. easy. } 
              split. { intros. right. easy. }
              split. { intros. right. easy. }
              split. { intros. right. easy. }
              split. { intros. right. easy. }
              split. { intros. right. easy. }
              split. { intros. easy. }
              split. { intros. easy. }
              { intros. easy. }
            }
          }
        }
  }
  { intros. apply lemRet.
    unfold sub, subRelt.
    intros.
    rename σ into σs.
    rename ρ into ρs.
    destruct H as [s2 [ρs2 [H0 H]]].
    destruct H as [s1 [ρs1 [H1 H]]].
    clear H0 H1.
    destruct H as [ρ1 [σ [Hρ1 [Hσ H]]]].
    destruct H as [Hstateρ1 [Hstateσ H]].
    unfold Posts.
    exists σ.
    split; [easy |].
    destruct H as [HH | HH].
    { left.
      destruct HH as [Hfsts1 [Hv [HCallsρ1 [HRetsρ1 [HCallsσ [HRetsσ [Hfstt Howns_rel]]]]]]].
      subst v. repeat split; easy.
    }
    { right.
      destruct HH as [HH Hub].
      split; [| easy].
      easy.
    }
  }
Qed.

Lemma SpinLock_all_verified {T A} :
  forall (i: Name T) (m: F A), 
      VerifyProg i (Rely i) (Guar i) 
      (prComp (Precs i A m) (TInvoke SpinLockImpl i _ m) ->> Rely i)
      (SpinLockImpl _ m)
      (Posts i A m).
Proof.
  intros.
  destruct m.
  { apply SpinLock_Acq_verified. }
  { apply SpinLock_Rel_verified. }
Qed.

Definition SpinLockLayer {T} := ((VE T) :> SpinLockImpl).

Theorem SpinLockCorrect {T} :
  VerifyImpl (SpinLockLayer.(USpec)) (VFU T) Rely Guar Precs (LImpl (T := T) SpinLockLayer) Posts CSs.
Proof.
  constructor.
  { apply SpinLock_R_refl. }
  { apply SpinLock_R_trans. }
  { apply SpinLock_G_in_R. }
  { apply SpinLock_Inv_in_R. }
  { apply SpinLock_Ret_in_R. }
  { apply SpinLock_init_in_P. }
  { apply SpinLock_P_stable. }
  { apply SpinLock_switch_code. }
  { simpl. intros. apply SpinLock_all_verified. }
  { intros. apply SpinLock_all_return. }
Qed.

Theorem SpinLock_Linearizable {T} :
  Lin (overObj SpinLockLayer) (VFU T).
Proof.
  eapply soundness.
  apply SpinLockCorrect.
Qed.