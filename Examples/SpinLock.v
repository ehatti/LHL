From LHL.Core Require Import
  Program
  ProgramRules
  Specs
  Logic
  Tensor
  Traces
  Linearizability
  UBLayer2.

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

(* Definition E := CASSig bool.
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
        True (* To be complete *)
    | Rel =>
        (PState ρ = inl (LockOwned i) /\ snd s = CASDef (Some true) None) \/
        (PState ρ <> inl (LockOwned i) /\ (StateWithUB_acf _ (acf T) (PState ρ) i = None))
    end.

Definition Posts {T} i A (m : LockSig A) : @PostU T A :=
  fun v s ρs t σs => exists ρ σ, ρs = eq ρ /\ σs = eq σ /\
    match m with
    | Acq =>
        True (* To be complete *)
    | Rel =>
        PCalls σ i = CallDone Rel /\
        PRets σ i = RetPoss Rel tt /\
        ((PState ρ = inl (LockOwned i) /\ (forall m, PState σ <> inl (LockDef (Some i) m)) /\ fst t i = Cont m (Return v)) \/
         (exists a, PState σ = inr (UBState_, a)))
    end. *)

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

