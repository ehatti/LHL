From LHL.Core Require Import
  Program
  Specs
  Traces
  Logic
  LogicPaco
  LogicFacts
  ProgramFacts.

From LHL.Util Require Import
  Util
  Tactics
  TransUtil.

From Coq Require Import
  Program.Equality
  Logic.FunctionalExtensionality
  Logic.PropExtensionality
  Relations.Relation_Operators.

From Paco Require Import paco.

Require Import Coq.Program.Equality.

Inductive UBState : Type :=
| UBState_.

Definition StateWithUB {T F} (State : Type) : Type := sum State (UBState * ActiveMap T F).

Definition ActiveMapIdle {T E} : ActiveMap T E := fun _ => None.

Inductive ActiveMapStep {T E} : ActiveMap T E -> ThreadEvent T E -> ActiveMap T E -> Prop :=
| ActiveMapStepCall: forall a a' i A (m: E A),
    a i = None ->
    a' i = Some (existT _ _ m) ->
    differ_pointwise a a' i ->
    ActiveMapStep a (i, CallEv m) a'
| ActiveMapStepRet: forall a a' i A (m: E A) v,
    a i = Some (existT _ _ m) ->
    a' i = None ->
    differ_pointwise a a' i ->
    ActiveMapStep a (i, RetEv m v) a'.

Lemma ActiveMapStepSeqcons {T E}:
  forall a1 a2 (te: @ThreadEvent T E) p,
    ActiveMapStep a1 te a2 -> SeqConsistent a2 p ->
      SeqConsistent a1 (te :: p).
Proof.
  intros.
  destruct te as [i e].
  destruct e.
  + dependent destruction H.
    econstructor; eassumption.
  + dependent destruction H.
    econstructor; eassumption.
Qed.

Definition ActiveFSound {T F} {State: Type} (step: State -> ThreadEvent T F -> State -> Prop) (f: State -> ActiveMap T F) :=
  forall s te s', step s te s' -> ActiveMapStep (f s) te (f s').

Definition ActiveF {T F} {State: Type} (step: State -> ThreadEvent T F -> State -> Prop):= State -> ActiveMap T F.

Inductive StepWithUB {T F} {State: Type}
                     (step: State -> ThreadEvent T F -> State -> Prop)
                     (acf: ActiveF step) : 
      StateWithUB State -> ThreadEvent T F -> StateWithUB State -> Prop :=
| NormalStep: forall s te s', 
      step s te s' -> StepWithUB step acf (inl s) te (inl s')
| ErrorStep: forall s te a', 
      (forall s', (~ step s te s')) -> ActiveMapStep (acf s) te a' -> StepWithUB step acf (inl s) te (inr (UBState_, a'))
| UBStep: forall a te a', 
      ActiveMapStep a te a' -> StepWithUB step acf (inr (UBState_, a)) te (inr (UBState_, a')).

Definition acf_sound {T F} {spec: Spec T F} (acf: ActiveF spec.(Step)) :=
  acf (spec.(Init)) = ActiveMapIdle /\ forall s te s', spec.(Step) s te s' -> ActiveMapStep (acf s) te (acf s').

Definition StateWithUB_acf {T F} {State: Type} (step: State -> ThreadEvent T F -> State -> Prop) (acf: ActiveF step) : ActiveF (StepWithUB step acf) :=
  fun s =>
    match s with
    | inl s' => acf s'
    | inr (_, a') => a'
    end.

Program Definition SpecWithUB {T F} (spec: Spec T F) (acf: ActiveF spec.(Step)) (HAcf: acf_sound acf): Spec T F :=
{|
  State := StateWithUB spec.(State);
  Step := StepWithUB spec.(Step) acf;
  Init := inl spec.(Init);
|}.

Next Obligation.
  replace (fun _ : Name T => None) with ((StateWithUB_acf (Step spec) acf) (@inl (@State T F spec) (prod UBState (ActiveMap T F)) (@Init T F spec))) by (destruct HAcf; auto).
  generalize dependent (@inl (@State T F spec) (prod UBState (ActiveMap T F)) (@Init T F spec)).
  generalize dependent s.
  destruct HAcf as [Hinit HStep].
  induction p.
  + constructor.
  + intros.
    inversion H; subst.
    destruct a as [i e].
    specialize (IHp s st'' H4).
    inversion H2; subst; simpl in *.
    - specialize (HStep _ _ _ H0).
      apply (ActiveMapStepSeqcons _ _ _ _ HStep IHp).
    - apply (ActiveMapStepSeqcons _ _ _ _ H1 IHp).
    - apply (ActiveMapStepSeqcons _ _ _ _ H0 IHp).
Qed.

Definition PossWithUB {T F} {spec: Spec T F} (acf: ActiveF spec.(Step)) (HAcf: acf_sound acf) (ρ: Poss spec) : Poss (SpecWithUB spec acf HAcf).
constructor.
+ exact (inl ρ.(PState)).
+ exact ρ.(PCalls).
+ exact ρ.(PRets).
Defined.

Definition PossSetWithUB {T F} {spec: Spec T F} (acf: ActiveF spec.(Step)) (HAcf: acf_sound acf) (ρs: PossSet spec) : PossSet (SpecWithUB spec acf HAcf) :=
  fun ρ' => exists ρ, ρs ρ /\ ρ' = PossWithUB acf HAcf ρ.

Definition PossSetRemoveUB {T F} {spec: Spec T F} (acf: ActiveF spec.(Step)) (HAcf: acf_sound acf) (ρs: PossSet (SpecWithUB spec acf HAcf)) : PossSet spec :=
  fun ρ => ρs (PossWithUB acf HAcf ρ).

Definition PossSetUBFree {T F} {spec: Spec T F} (acf: ActiveF spec.(Step)) (HAcf: acf_sound acf) (ρs: PossSet (SpecWithUB spec acf HAcf)) : Prop :=
  forall ρ : Poss (SpecWithUB spec acf HAcf), 
    (exists a, PState ρ = inr (UBState_, a)) -> ~ ρs ρ.

Definition PrecWithUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf (prec: Prec VE VF) : Prec VE (SpecWithUB VF acf HAcf) :=
  fun s' ρs' => exists s ρs, prec s ρs /\ s = s' /\ ρs' = PossSetWithUB acf HAcf ρs.

Definition ReltWithUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf (relt: Relt VE VF) : Relt VE (SpecWithUB VF acf HAcf) :=
  fun s1 ρs1 s2 ρs2 => 
    exists t1 σs1 t2 σs2, relt t1 σs1 t2 σs2 /\ t1 = s1 /\ t2 = s2 /\ ρs1 = PossSetWithUB acf HAcf σs1 /\ ρs2 = PossSetWithUB acf HAcf σs2.

Definition PostWithUB {T E F A} {VE: Spec T E} {VF: Spec T F} acf HAcf (post: Post VE VF A) : Post VE (SpecWithUB VF acf HAcf) A :=
  fun v s1 ρs1 s2 ρs2 => 
    exists t1 σs1 t2 σs2, post v t1 σs1 t2 σs2 /\ t1 = s1 /\ t2 = s2 /\ ρs1 = PossSetWithUB acf HAcf σs1 /\ ρs2 = PossSetWithUB acf HAcf σs2.

Lemma PossWithUBUnfold {T F} {spec: Spec T F} (acf: ActiveF spec.(Step)) (HAcf: acf_sound acf) :
  forall ρ, 
    PossWithUB acf HAcf ρ = 
    MkPoss T F (@SpecWithUB T F spec acf HAcf)
      (@inl (@State T F spec) (prod UBState (ActiveMap T F))
      (@PState T F spec ρ))
      (@PCalls T F spec ρ) (@PRets T F spec ρ).
Proof. reflexivity. Qed.

Lemma PossSetEmbedding {T F} {spec: Spec T F} (acf: ActiveF spec.(Step)) (HAcf: acf_sound acf) :
  forall ρs ρ, ρs ρ -> (PossSetWithUB acf HAcf ρs) (PossWithUB acf HAcf ρ).
Proof.
  intros.
  unfold PossSetWithUB, PossWithUB.
  exists ρ. split; easy.
Qed.

Lemma PossSetRemoveEmbedding {T F} {spec: Spec T F} (acf: ActiveF spec.(Step)) (HAcf: acf_sound acf) :
  forall ρs, PossSetUBFree acf HAcf ρs -> 
    ρs = PossSetWithUB acf HAcf (PossSetRemoveUB acf HAcf ρs).
Proof.
  intros.
  unfold PossSetWithUB, PossSetRemoveUB, PossSetUBFree in *.
  extensionality s.
  apply propositional_extensionality.
  split; intros.
  + specialize (H s).
    destruct s; simpl in *.
    destruct PState.
    - clear H.
      exists {| PState := s; PCalls := PCalls; PRets := PRets; |}.
      unfold PossWithUB. simpl.
      easy.
    - destruct H.
      { 
        destruct p. exists a.
        assert(u = UBState_). { destruct u; reflexivity. }
        rewrite H.
        reflexivity.
      }
      easy. 
  + destruct_all.
    subst s.
    apply H0. 
Qed.

Lemma PossUBInv {T F} {spec: Spec T F} (acf: ActiveF spec.(Step)) (HAcf: acf_sound acf) :
  forall ρ1 ρ2, PossWithUB acf HAcf ρ1 = PossWithUB acf HAcf ρ2 -> ρ1 = ρ2.
Proof.
  intros.
  unfold PossWithUB in H.
  inversion H.
  destruct ρ1, ρ2; simpl in *; subst.
  reflexivity.
Qed.

Lemma possSetUBInv_aux {T F} {spec: Spec T F} (acf: ActiveF spec.(Step)) (HAcf: acf_sound acf) (ρs: PossSet spec) (x: Poss spec) :
  (exists ρ : Poss spec, ρs ρ /\ PossWithUB acf HAcf x = PossWithUB acf HAcf ρ) = (ρs x).
Proof.
  apply propositional_extensionality.
  split; intros.
  + destruct H as [ρ [H1 H2]].
    pose proof PossUBInv acf HAcf x ρ H2.
    subst. exact H1.
  + exists x. split; try reflexivity. exact H.
Qed. 

Lemma possSetUBInv {T F} {spec: Spec T F} (acf: ActiveF spec.(Step)) (HAcf: acf_sound acf) :
  forall ρs1 ρs2, PossSetWithUB acf HAcf ρs1 = PossSetWithUB acf HAcf ρs2 -> ρs1 = ρs2.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  apply propositional_extensionality.
  unfold PossSetWithUB in H.
  remember ((fun ρ' : Poss (SpecWithUB spec acf HAcf) =>
    exists ρ : Poss spec,
    ρs1 ρ /\ ρ' = PossWithUB acf HAcf ρ)) as f.
  remember (fun ρ' : Poss (SpecWithUB spec acf HAcf) =>
    exists ρ : Poss spec,
    ρs2 ρ /\ ρ' = PossWithUB acf HAcf ρ) as g.
  assert (f (PossWithUB acf HAcf x) = g (PossWithUB acf HAcf x)) by (rewrite H; reflexivity).
  subst.
  rewrite! possSetUBInv_aux in H0.
  rewrite H0; easy.
Qed.

Lemma reltUBEmbedding {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall (R: Relt VE VF) s ρs t σs,
    R s ρs t σs -> ReltWithUB acf HAcf R s (PossSetWithUB acf HAcf ρs) t (PossSetWithUB acf HAcf σs).
Proof.
  intros.
  unfold ReltWithUB.
  exists s, ρs, t, σs.
  auto.
Qed.

Lemma reltCompUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall R1 R2 : Relt VE VF,
    ReltWithUB acf HAcf (R1 ->> R2) = ReltWithUB acf HAcf R1 ->> ReltWithUB acf HAcf R2.
Proof.
  intros.
  extensionality s.
  extensionality ρs.
  extensionality t.
  extensionality σs.
  apply propositional_extensionality.
  split; intros.
  + unfold ReltCompose in *.
    unfold ReltWithUB in H.
    destruct_all; subst.
    exists x3, (PossSetWithUB acf HAcf x4). 
    split; apply reltUBEmbedding; assumption.
  + unfold ReltCompose in *.
    unfold ReltWithUB in *.
    destruct_all; subst.
    exists s, x6, t, x4.
    repeat split; try reflexivity.
    exists x, x2.
    pose proof possSetUBInv acf HAcf x8 x2 H3.
    subst x8.
    easy.
Qed.

Lemma precToReltComp {T E F} {VE: Spec T E} {VF: Spec T F} :
  forall P (R : Relt VE VF),
    prComp P R = (PrecToRelt P) ->> R.
Proof.
  unfold prComp, PrecToRelt, ReltCompose.
  intros.
  extensionality s.
  extensionality ρs.
  extensionality t.
  extensionality σs.
  apply propositional_extensionality.
  split; intros.
  + exists s, ρs. easy.
  + destruct H as [s' [ρs' [[? [? ?]] H2]]].
    subst.
    easy. 
Qed.

Lemma precToReltUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall P : Prec VE VF, PrecToRelt (PrecWithUB acf HAcf P) = ReltWithUB acf HAcf (PrecToRelt P).
Proof.
  unfold PrecToRelt, PrecWithUB, ReltWithUB.
  intros.
  extensionality s.
  extensionality ρs.
  extensionality t.
  extensionality σs.
  apply propositional_extensionality.
  split; intros.
  + destruct_all; subst.
    exists t, x0, t, x0.
    easy.
  + destruct_all; subst.
    split.
    exists t, x2; easy.
    easy.
Qed.

Lemma reltToPrecUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall R : Relt VE VF, ReltToPrec (ReltWithUB acf HAcf R) = PrecWithUB acf HAcf (ReltToPrec R).
Proof.
  unfold ReltToPrec, PrecWithUB, ReltWithUB.
  intros.
  extensionality s.
  extensionality ρs.
  apply propositional_extensionality.
  split; intros.
  + destruct_all; subst.
    exists s, x4.
    split.
    { exists x, x2; easy. }
    easy.
  + destruct_all; subst.
    exists x1, (PossSetWithUB acf HAcf x2), x1, x2.
    exists s, x0.
    easy.
Qed.

Lemma prCompUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall P (R : Relt VE VF), ReltWithUB acf HAcf (prComp P R) = prComp (PrecWithUB acf HAcf P) (ReltWithUB acf HAcf R).
Proof.
  intros.
  rewrite! precToReltComp.
  rewrite reltCompUB.
  rewrite precToReltUB.
  reflexivity.
Qed.

Lemma reltCompInvokeUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall (R : Relt VE VF) (impl : Impl E F) i A m, (ReltWithUB acf HAcf R) ->> (TInvoke impl i A m) = ReltWithUB acf HAcf (R ->> (TInvoke impl i A m)).
Proof.
  intros.
  extensionality s.
  extensionality ρs.
  extensionality t.
  extensionality σs.
  apply propositional_extensionality.
  split; intros.
  + unfold ReltCompose in *.
    destruct H as [s' [ρs' [? ?]]].
    unfold ReltWithUB in *.
    destruct_all; subst.
    rename x0 into ρs.
    rename x2 into ρs'.
    exists s, ρs, t.
    exists (PossSetRemoveUB acf HAcf σs).
    split.
    { 
      exists s', ρs'.
      split; [exact H |].
      unfold TInvoke in *.
      destruct_all.
      split.
      { 
        unfold TIdle in *.
        destruct_all.
        split; [exact H0 |].
        intros.
        specialize (H4 (PossWithUB acf HAcf ρ)).
        assert(PossSetWithUB acf HAcf ρs' (PossWithUB acf HAcf ρ)).
        { unfold PossSetWithUB. exists ρ. split; easy. }
        specialize (H4 H6).
        destruct H4 as [? ?].
        split.
        {
          unfold PossWithUB in H4.
          simpl in H4.
          apply H4.
        }
        {
          unfold PossWithUB in H7.
          simpl in H7.
          apply H7.
        }
      }
      split; [exact H1 |].
      split; [exact H2 |].
      rewrite H3.
      unfold PossSetRemoveUB.
      extensionality x.
      apply propositional_extensionality.
      split; intros; subst.
      {
        destruct_all.
        exists 
          {| PState := x.(PState);
             PCalls := x0.(PCalls);
             PRets := x0.(PRets);
          |}.
        simpl.
        unfold PossWithUB in *. simpl in *.
        repeat split; try assumption.
        unfold PossSetWithUB in H3.
        destruct H3 as [ρ' [? ?]].
        assert(ρ' = {| PState := PState x; PCalls := PCalls x0; PRets := PRets x0 |}). {
          destruct ρ'; subst; simpl in *.
          f_equal.
          inversion H4.
          reflexivity.
        }
        subst ρ'.
        apply H3.
      }
      {
        destruct_all.
        exists (PossWithUB acf HAcf x0).
        split; [apply PossSetEmbedding; easy |].
        unfold PossWithUB. simpl.
        rewrite H4.
        repeat split; try assumption.
      }
    }
    repeat split; try reflexivity.
    unfold TInvoke in H0.
    destruct_all.
    assert(PossSetUBFree acf HAcf σs). {
      unfold PossSetUBFree.
      intros.
      destruct H4 as [a ?].
      intro.
      rewrite H3 in H5.
      destruct_all.
      unfold PossSetWithUB in H5.
      destruct_all.
      rewrite H11 in H6.
      rewrite H4 in H6.
      unfold PossWithUB in H6; simpl in H6.
      inversion H6.
    }
    apply (PossSetRemoveEmbedding _ _ _ H4).
  + unfold ReltCompose in *.
    unfold ReltWithUB in *.
    destruct H as [s'' [ρs_ [t'' [σs_ [[s' [ρs' [? ?]]] [? [? [? ?]]]]]]]].
    subst.
    exists s', (PossSetWithUB acf HAcf ρs').
    split. { exists s, ρs_, s', ρs'. easy. }
    unfold TInvoke in *.
    destruct_all.
    split.
    { 
      unfold TIdle in *.
      destruct_all.
      split; [exact H0 |].
      intros.
      unfold PossSetWithUB in H5.
      destruct H5 as [ρ0 [? ?]].
      unfold PossWithUB in H6.
      specialize (H4 ρ0 H5).
      destruct H4 as [? ?].
      rewrite H6; simpl.
      easy.
    }
    split; [exact H1 |].
    split; [exact H2 |].
    rewrite H3.
    unfold PossSetWithUB.
    extensionality x.
    apply propositional_extensionality.
    split; intros; subst.
    {
      destruct_all.
      exists (PossWithUB acf HAcf x1).
      rewrite H4. unfold PossWithUB. simpl.
      repeat split; try assumption.
      { exists x1. easy. }
      { rewrite H5. reflexivity. }
    }
    {
      destruct_all.
      exists 
      {| PState := x1.(PState);
          PCalls := fun j => if (eqb i j) then CallPoss m else x1.(PCalls) j;
          PRets := fun j => if (eqb i j) then RetIdle else x1.(PRets) j;
      |}.
      split; simpl.
      { 
        exists x1.
        repeat split; try easy.
        { rewrite eqb_id. reflexivity. }
        { rewrite eqb_id. reflexivity. }
        { apply differ_pointwise_trivial. }
        { apply differ_pointwise_trivial. }
      }
      {
        unfold PossWithUB.
        simpl.
        destruct x; simpl in *.
        f_equal.
        { rewrite H4, H9. unfold PossWithUB. simpl. reflexivity. }
        { rewrite H9 in H7. unfold PossWithUB in H7. simpl in H7.
          extensionality j. destruct (classicT (i = j)).
          { subst. rewrite eqb_id. apply H5. }
          { rewrite (eqb_nid _ _ n). unfold differ_pointwise in H7. apply H7. easy. }
        }
        { rewrite H9 in H8. unfold PossWithUB in H8. simpl in H8.
          extensionality j. destruct (classicT (i = j)).
          { subst. rewrite eqb_id. apply H6. }
          { rewrite (eqb_nid _ _ n). unfold differ_pointwise in H8. apply H8. easy. }
        }
      }
    }
Qed.

Lemma ReltPostUBEmbedding {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall (R : Relt VE VF) Ret (Q: Post VE VF Ret) (v: Ret),
    R ==> (Q v) -> ReltWithUB acf HAcf R ==> (PostWithUB acf HAcf Q v).
Proof.
  unfold sub, subRelt in *.
  intros.
  unfold PostToRelt in *.
  unfold PostWithUB.
  unfold ReltWithUB in H0.
  destruct_all; subst.
  specialize (H _ _ _ _ H0).
  exists s, x0, t, x2.
  easy.
Qed.

Lemma PostValueUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall A (Q: Post VE VF A) v, 
    (PostWithUB acf HAcf Q) v = ReltWithUB acf HAcf (Q v).
Proof.
  intros.
  unfold PostWithUB, ReltWithUB.
  extensionality s.
  extensionality ρs.
  extensionality t.
  extensionality σs.
  split.
Qed.

Lemma reltSubUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall (R Q : Relt VE VF), 
    R ==> Q -> ReltWithUB acf HAcf R ==> ReltWithUB acf HAcf Q.
Proof.
  intros.
  unfold sub, subRelt in *.
  unfold ReltWithUB in *.
  intros.
  destruct_all; subst.
  specialize (H _ _ _ _ H0).
  exists s, x0, t, x2.
  easy.
Qed.

Lemma stableReltUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall (R Q : Relt VE VF), 
    stableRelt R Q -> stableRelt (ReltWithUB acf HAcf R) (ReltWithUB acf HAcf Q).
Proof.
  intros.
  unfold stableRelt in *.
  rewrite <- reltCompUB.
  apply reltSubUB.
  apply H.
Qed.

Lemma stablePostUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall (R : Relt VE VF) Ret (Q: Post VE VF Ret),
    stablePost R Q -> stablePost (ReltWithUB acf HAcf R) (PostWithUB acf HAcf Q).
Proof.
  intros.
  unfold stablePost in *.
  intros v.
  specialize (H v).
  apply stableReltUB, H.
Qed.

Lemma silentStepUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall (i: Name T) (G: Relt VE VF) P Q,
    SilentStep i G P Q -> SilentStep i (ReltWithUB acf HAcf G) (PrecWithUB acf HAcf P) (ReltWithUB acf HAcf Q).
Proof.
  intros.
  unfold SilentStep in *.
  intros.
  unfold PrecWithUB in H0.
  destruct_all; subst.
  specialize (H _ _ _ _ H0 H1 H2).
  destruct H.
  split; apply reltUBEmbedding; easy. 
Qed.

Lemma stepSpecCallUB {T F} {spec: Spec T F} (acf: ActiveF spec.(Step)) (HAcf: acf_sound acf) :
  forall ρ σ A i (m : F A),
    spec.(Step) (PState ρ) (i, CallEv m) (PState σ) ->
    StepWithUB spec.(Step) acf (PState (PossWithUB acf HAcf ρ)) (i, CallEv m) (PState (PossWithUB acf HAcf σ)).
Proof.
  intros.
  constructor.
  exact H.
Qed.

Lemma stepSpecRetUB {T F} {spec: Spec T F} (acf: ActiveF spec.(Step)) (HAcf: acf_sound acf) :
  forall ρ σ A i (m : F A) v,
    spec.(Step) (PState ρ) (i, RetEv m v) (PState σ) ->
    StepWithUB spec.(Step) acf (PState (PossWithUB acf HAcf ρ)) (i, RetEv m v) (PState (PossWithUB acf HAcf σ)).
Proof.
  intros.
  constructor.
  exact H.
Qed.

Lemma stepSpecUB {T F} {spec: Spec T F} (acf: ActiveF spec.(Step)) (HAcf: acf_sound acf) :
  forall ρ σ te,
    spec.(Step) (PState ρ) te (PState σ) ->
    StepWithUB spec.(Step) acf (PState (PossWithUB acf HAcf ρ)) te (PState (PossWithUB acf HAcf σ)).
Proof.
  intros.
  destruct te.
  destruct e.
  + apply stepSpecCallUB, H.
  + apply stepSpecRetUB, H.
Qed.

Lemma possStepUB {T F} {spec: Spec T F} (acf: ActiveF spec.(Step)) (HAcf: acf_sound acf) :
  forall i ρ σ, PossStep i ρ σ -> PossStep i (PossWithUB acf HAcf ρ) (PossWithUB acf HAcf σ).
Proof.
  intros.
  unfold PossWithUB. simpl.
  inversion H.
  + econstructor.
    - apply stepSpecUB, H0.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
  + econstructor 2.
    - apply stepSpecUB, H0.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
Qed.

Lemma possStepsUB {T F} {spec: Spec T F} (acf: ActiveF spec.(Step)) (HAcf: acf_sound acf) :
  forall ρ σ, PossSteps ρ σ -> PossSteps (PossWithUB acf HAcf ρ) (PossWithUB acf HAcf σ).
Proof.
  intros.
  induction H.
  + constructor.
  + inversion H2; subst.
    * unfold PossWithUB. simpl.
      econstructor.
      { apply possStepUB, H. }
      { assumption. }
      { assumption. }
      { assumption. }
    * econstructor.
      { apply possStepUB, H. }
      { assumption. }
      { assumption. }
      { assumption. }
Qed.

Lemma commitUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall i (e: Event E) (G: Relt VE VF) P Q,
    Commit i G P e Q -> 
      Commit i (ReltWithUB acf HAcf G) (PrecWithUB acf HAcf P) e (ReltWithUB acf HAcf Q).
Proof.
  intros.
  unfold Commit in *.
  intros.
  unfold PrecWithUB in H0.
  destruct_all; subst.
  rename x0 into ρs.
  specialize (H _ _ _ H0 H1 H2 H3).
  destruct_all.
  rename x into σs.
  rename x0 into σ.
  exists (PossSetWithUB acf HAcf σs).
  repeat split.
  + exists (PossWithUB acf HAcf σ).
    apply PossSetEmbedding, H.
  + intros.
    destruct σ0.
    destruct PState.
    - unfold PossSetWithUB in H7.
      destruct H7 as [σ' [? ?]].
      unfold PossWithUB in H8.
      inversion H8; subst.
      specialize (H4 σ' H7).
      destruct H4 as [ρ' [? ?]].
      exists (PossWithUB acf HAcf ρ').
      split.
      { apply PossSetEmbedding, H4. }
      { rewrite <- PossWithUBUnfold. apply possStepsUB, H9. } 
    - unfold PossSetWithUB in H7. 
      destruct H7 as [σ' [? ?]].
      unfold PossWithUB in H8.
      inversion H8; subst.
  + apply reltUBEmbedding, H5.
  + apply reltUBEmbedding, H6.
Qed.

Lemma paco_safe_UB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall i A (R: Relt VE VF) (G: Relt VE VF) P (Q: Post VE VF A) prog,
    paco_safe i R G P prog Q -> paco_safe i (ReltWithUB acf HAcf R) (ReltWithUB acf HAcf G) (ReltWithUB acf HAcf P) prog (PostWithUB acf HAcf Q).
Proof.
  intros.
  generalize dependent P.
  generalize dependent prog.
  pcofix rec.
  destruct prog; pfold; intros.
  + (* Bind *)
    punfold H0.
    dependent destruction H0.
    econstructor.
    { apply (stableReltUB _ _ _ _ H). }
    { apply (stablePostUB _ _ _ _ _ H0). }
    {
      rewrite reltToPrecUB.
      apply commitUB, H1.
    }
    {
      intros v.
      specialize (H2 v).
      destruct H2.
      split.
      { 
        rewrite <- reltCompUB.
        rewrite PostValueUB.
        rewrite reltToPrecUB.
        apply commitUB, H2.
      }
      destruct H3. 2: inversion H3.
      unfold paco_safe in rec.
      specialize (rec _ _ H3).
      right.
      rewrite PostValueUB.
      rewrite <- !reltCompUB.
      apply rec. 
    }
  + (* Return *)
    econstructor.
    rewrite <- paco_eqv in H0.
    dependent destruction H0.
    apply ReltPostUBEmbedding, H.
  + (* NoOp*)
    rewrite <- paco_eqv in H0.
    dependent destruction H0.
    econstructor.
    { apply (stableReltUB _ _ _ _ H). }
    {
      rewrite reltToPrecUB.
      apply silentStepUB, H0.
    }
    {
      rewrite <- reltCompUB.
      unfold paco_safe in rec.
      specialize (rec prog (P ->> QS)).
      assert(paco2 (paco_safeF i R G Q) bot2 (P ->> QS) prog).
      {
        rewrite paco_eqv in H1.
        punfold H1.
      }
      specialize (rec H2).
      right. exact rec.
    }
Qed.

Lemma VerifyWithUB
  {T E F}
  {VE : Spec T E}
  {VF : Spec T F}
  {R G : Name T -> Relt VE VF}
  {P : Name T -> forall Ret, F Ret -> Prec VE VF}
  {impl : Impl E F}
  {Q : Name T -> forall Ret, F Ret -> Post VE VF Ret}
  acf HAcf i A m : 
      (VerifyProg i (R i) (G i)
      (prComp (P i A m) (TInvoke impl i _ m) ->> R i)
      (impl _ m)
      (Q i A m)) ->
        (VerifyProg i (ReltWithUB acf HAcf (R i)) (ReltWithUB acf HAcf (G i))
        (prComp (PrecWithUB acf HAcf (P i A m)) (TInvoke impl i _ m) ->> ReltWithUB acf HAcf (R i))
        (impl _ m)
        (PostWithUB acf HAcf (Q i A m))).
Proof.
  unfold VerifyProg.
  rewrite! paco_eqv.
  rewrite! precToReltComp.
  rewrite precToReltUB.
  rewrite reltCompInvokeUB.
  rewrite <- reltCompUB. 
  generalize dependent ((PrecToRelt (P i A m) ->> TInvoke impl i A m) ->> R i).
  generalize dependent (impl A m).
  intros.
  apply (paco_safe_UB acf HAcf i A (R i) (G i) r (Q i A m) p H).
Qed.