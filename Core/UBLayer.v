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
  fun s ρs => prec s (PossSetRemoveUB acf HAcf ρs).

Definition ReltWithUBEmp {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf (relt: Relt VE VF) : Relt VE (SpecWithUB VF acf HAcf) :=
  fun s1 ρs1 s2 ρs2 => 
    exists ρs1' ρs2', relt s1 ρs1' s2 ρs2' /\ ρs1 = PossSetWithUB acf HAcf ρs1' /\ ρs2 = PossSetWithUB acf HAcf ρs2'.

Definition ReltWithUBFull {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf (relt: Relt VE VF) : Relt VE (SpecWithUB VF acf HAcf) :=
  fun s1 ρs1 s2 ρs2 => 
    relt s1 (PossSetRemoveUB acf HAcf ρs1) s2 (PossSetRemoveUB acf HAcf ρs2).

Definition RelyWithUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf (R: Name T -> Relt VE VF) (i: Name T) : Relt VE (SpecWithUB VF acf HAcf) :=
  ReltWithUBFull acf HAcf (R i).

Definition GuarWithUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf (G: Name T -> Relt VE VF) (i: Name T) : Relt VE (SpecWithUB VF acf HAcf) :=
  ReltWithUBFull acf HAcf (G i).

Definition PostWithUBFull {T E F A} {VE: Spec T E} {VF: Spec T F} acf HAcf (post: Post VE VF A) : Post VE (SpecWithUB VF acf HAcf) A :=
  fun v s1 ρs1 s2 ρs2 => 
    post v s1 (PossSetRemoveUB acf HAcf ρs1) s2 (PossSetRemoveUB acf HAcf ρs2).

Definition PostWithUBEmp{T E F A} {VE: Spec T E} {VF: Spec T F} acf HAcf (post: Post VE VF A) : Post VE (SpecWithUB VF acf HAcf) A :=
  fun v s1 ρs1 s2 ρs2 => 
    exists ρs1' ρs2', post v s1 ρs1' s2 ρs2' /\ ρs1 = PossSetWithUB acf HAcf ρs1' /\ ρs2 = PossSetWithUB acf HAcf ρs2'.

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

Lemma PossSetEmbedForgetUB {T F} {spec: Spec T F} (acf: ActiveF spec.(Step)) (HAcf: acf_sound acf) :
  forall ρs, PossSetRemoveUB acf HAcf (PossSetWithUB acf HAcf ρs) = ρs.
Proof.
  unfold PossSetRemoveUB, PossSetWithUB, PossWithUB.
  intros.
  extensionality s.
  apply propositional_extensionality.
  split; intros.
  + destruct_all.
    inversion H0.
    assert(s = x). { destruct s, x; simpl in *; subst. reflexivity. }
    subst s; assumption.
  + exists s. split; [assumption | reflexivity].
Qed.

Lemma reltUBEmbedding {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall (R: Relt VE VF) s ρs t σs,
    R s ρs t σs -> ReltWithUBFull acf HAcf R s (PossSetWithUB acf HAcf ρs) t (PossSetWithUB acf HAcf σs).
Proof.
  intros.
  unfold ReltWithUBFull.
  rewrite !PossSetEmbedForgetUB.
  assumption.
Qed.

Lemma reltCompUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall R1 R2 : Relt VE VF,
    ReltWithUBFull acf HAcf (R1 ->> R2) = ReltWithUBFull acf HAcf R1 ->> ReltWithUBFull acf HAcf R2.
Proof.
  intros.
  extensionality s.
  extensionality ρs.
  extensionality t.
  extensionality σs.
  apply propositional_extensionality.
  split; intros.
  + unfold ReltCompose in *.
    unfold ReltWithUBFull in H.
    destruct_all; subst.
    exists x, (PossSetWithUB acf HAcf x0).
    unfold ReltWithUBFull.
    rewrite !PossSetEmbedForgetUB.
    easy.
  + unfold ReltCompose in *.
    unfold ReltWithUBFull in *.
    destruct_all; subst.
    exists x, (PossSetRemoveUB acf HAcf x0).
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
  forall P : Prec VE VF, PrecToRelt (PrecWithUB acf HAcf P) ==> ReltWithUBFull acf HAcf (PrecToRelt P).
Proof.
  unfold PrecToRelt, PrecWithUB, ReltWithUBFull, sub, subRelt.
  intros.
  destruct_all; subst.
  easy.
Qed.

Lemma reltToPrecUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall R : Relt VE VF, ReltToPrec (ReltWithUBFull acf HAcf R) = PrecWithUB acf HAcf (ReltToPrec R).
Proof.
  unfold ReltToPrec, PrecWithUB, ReltWithUBFull.
  intros.
  extensionality s.
  extensionality ρs.
  apply propositional_extensionality.
  split; intros.
  + destruct_all; subst.
    exists x, (PossSetRemoveUB acf HAcf x0).
    easy.
  + destruct_all; subst.
    exists x, (PossSetWithUB acf HAcf x0).
    rewrite PossSetEmbedForgetUB.  
    easy.
Qed.

(* Lemma prCompUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall P (R : Relt VE VF), ReltWithUBFull acf HAcf (prComp P R) = prComp (PrecWithUB acf HAcf P) (ReltWithUBFull acf HAcf R).
Proof.
  intros.
  rewrite! precToReltComp.
  rewrite reltCompUB.
  rewrite precToReltUB.
  reflexivity.
Qed. *)

Lemma reltCompInvokeUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall (R : Relt VE VF) (impl : Impl E F) i A m, (ReltWithUBFull acf HAcf R) ->> (TInvoke impl i A m) ==> ReltWithUBFull acf HAcf (R ->> (TInvoke impl i A m)).
Proof.
  intros.
  unfold sub, subRelt.
  intros.
  rename ρ into ρs.
  rename σ into σs.
  unfold ReltCompose in *.
  destruct H as [s' [ρs' [? ?]]].
  unfold ReltWithUBFull in *.
  destruct_all; subst.
  exists s', (PossSetRemoveUB acf HAcf ρs').
  split; [easy |].
  unfold TInvoke in *.
  destruct_all.
  subst σs.
  split.
  { 
    unfold PossSetRemoveUB, PossWithUB. unfold TIdle in *. destruct_all.
    split; [easy |].
    intros.
    specialize (H3 _ H4).
    simpl in *. easy.
  }
  split; [easy |].
  split; [easy |].
  unfold PossSetRemoveUB, PossWithUB. unfold TIdle in *. destruct_all.
  simpl in *.
  extensionality x.
  apply propositional_extensionality.
  split; intros.
  - destruct_all.
    destruct x0.
    destruct PState.
    { 
      exists {| PState := s0; PCalls := PCalls; PRets := PRets; |}.
      unfold PossWithUB. simpl in *.
      inversion H5; subst.
      easy.
    }
    {
      simpl in H5.
      inversion H5.
    }
  - destruct_all. 
    exists (PossWithUB acf HAcf x0).
    unfold PossWithUB. simpl in *.
    repeat split; try assumption.
    f_equal. assumption.
Qed.

Lemma ReltPostUBEmbedding {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall (R : Relt VE VF) Ret (Q: Post VE VF Ret) (v: Ret),
    R ==> (Q v) -> ReltWithUBFull acf HAcf R ==> (PostWithUBFull acf HAcf Q v).
Proof.
  unfold sub, subRelt in *.
  intros.
  unfold PostToRelt in *.
  unfold PostWithUBFull.
  unfold ReltWithUBFull in H0.
  destruct_all; subst.
  specialize (H _ _ _ _ H0).
  easy.
Qed.

Lemma PostValueUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall A (Q: Post VE VF A) v, 
    (PostWithUBFull acf HAcf Q) v = ReltWithUBFull acf HAcf (Q v).
Proof.
  intros.
  unfold PostWithUBFull, ReltWithUBFull.
  extensionality s.
  extensionality ρs.
  extensionality t.
  extensionality σs.
  split.
Qed.

Lemma reltSubUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall (R Q : Relt VE VF), 
    R ==> Q -> ReltWithUBFull acf HAcf R ==> ReltWithUBFull acf HAcf Q.
Proof.
  intros.
  unfold sub, subRelt in *.
  unfold ReltWithUBFull in *.
  intros.
  destruct_all; subst.
  specialize (H _ _ _ _ H0).
  easy.
Qed.

Lemma stableReltUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall (R Q : Relt VE VF), 
    stableRelt R Q -> stableRelt (ReltWithUBFull acf HAcf R) (ReltWithUBFull acf HAcf Q).
Proof.
  intros.
  unfold stableRelt in *.
  rewrite <- reltCompUB.
  apply reltSubUB.
  apply H.
Qed.

Lemma stablePostUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall (R : Relt VE VF) Ret (Q: Post VE VF Ret),
    stablePost R Q -> stablePost (ReltWithUBFull acf HAcf R) (PostWithUBFull acf HAcf Q).
Proof.
  intros.
  unfold stablePost in *.
  intros v.
  specialize (H v).
  apply stableReltUB, H.
Qed.

Lemma silentStepUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall (i: Name T) (G: Relt VE VF) P Q,
    SilentStep i G P Q -> SilentStep i (ReltWithUBFull acf HAcf G) (PrecWithUB acf HAcf P) (ReltWithUBFull acf HAcf Q).
Proof.
  intros.
  unfold SilentStep in *.
  intros.
  unfold PrecWithUB in H0.
  destruct_all; subst.
  specialize (H _ _ _ _ H0 H1 H2).
  destruct H.
  split.
  { unfold ReltWithUBFull. easy. }
  { unfold ReltWithUBFull. easy. }
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
      Commit i (ReltWithUBFull acf HAcf G) (PrecWithUB acf HAcf P) e (ReltWithUBFull acf HAcf Q).
Proof.
  intros.
  unfold Commit in *.
  intros.
  unfold PrecWithUB in H0.
  destruct_all; subst.
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
      { unfold PossSetRemoveUB in H4. easy. }
      { rewrite <- PossWithUBUnfold. apply possStepsUB, H9. } 
    - unfold PossSetWithUB in H7. 
      destruct H7 as [σ' [? ?]].
      unfold PossWithUB in H8.
      inversion H8; subst.
  + unfold ReltWithUBFull.
    rewrite PossSetEmbedForgetUB.
    easy.
  + unfold ReltWithUBFull.
    rewrite PossSetEmbedForgetUB.
    easy.
Qed.

Lemma SafeProgUB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall i A (R: Relt VE VF) (G: Relt VE VF) P (Q: Post VE VF A) prog,
    SafeProg i R G P prog Q ->
       SafeProg i (ReltWithUBFull acf HAcf R) (ReltWithUBFull acf HAcf G) (ReltWithUBFull acf HAcf P) prog (PostWithUBFull acf HAcf Q).
Proof.
  intros.
  rewrite paco_eqv.
  rewrite paco_eqv in H.
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
        (VerifyProg i (RelyWithUB acf HAcf R i) (GuarWithUB acf HAcf G i)
        (prComp (PrecWithUB acf HAcf (P i A m)) (TInvoke impl i _ m) ->> (RelyWithUB acf HAcf R i))
        (impl _ m)
        (PostWithUBFull acf HAcf (Q i A m))).
Proof.
  unfold VerifyProg.
  rewrite! precToReltComp.
  intros.
  cut(
    SafeProg i (RelyWithUB acf HAcf R i)
      (GuarWithUB acf HAcf G i)
      ((ReltWithUBFull acf HAcf (PrecToRelt (P i A m)) ->>
          TInvoke impl i A m) ->>
          (RelyWithUB acf HAcf R i))
      (impl A m) 
      (PostWithUBFull acf HAcf (Q i A m))
  ). {
    apply weakenSafe.
    apply reltComposeMono1.
    apply reltComposeMono1.
    apply precToReltUB.
  }
  cut(
    SafeProg i (RelyWithUB acf HAcf R i)
      (GuarWithUB acf HAcf G i)
      (ReltWithUBFull acf HAcf (PrecToRelt (P i A m) ->> (TInvoke impl i A m)) ->>
          (RelyWithUB acf HAcf R i))
      (impl A m) 
      (PostWithUBFull acf HAcf (Q i A m))
  ). {
    apply weakenSafe.
    assert((ReltWithUBFull acf HAcf (PrecToRelt (P i A m)) ->> TInvoke impl i A m) ==>
           ReltWithUBFull acf HAcf (PrecToRelt (P i A m) ->> TInvoke impl i A m)). 
    { apply reltCompInvokeUB. }
    apply reltComposeMono1.
    apply H0.
  }
  unfold RelyWithUB.
  rewrite <- reltCompUB.
  apply SafeProgUB.
  exact H.
Qed.

Definition ReltToPost {T E F} {VE: Spec T E} {VF: Spec T F} A (R: Relt VE VF): Post VE VF A :=
  fun _ s1 ρs1 s2 ρs2 => R s1 ρs1 s2 ρs2.

Definition ClientSpec {T F} (VF: Spec T F) := forall A, F A -> Name T -> (VF.(State)) -> Prop.

Definition vioClientSpecPossSet {T F} {spec: Spec T F} (i: Name T) (A: Type) (m: F A) (client: ClientSpec spec) (ρs: PossSet spec) :=
  exists ρ, ρs ρ /\ ~client A m i (PState ρ).

Definition coClientSpecPrec {T E F} {VE: Spec T E} {VF: Spec T F} (i: Name T) (A: Type) (m: F A) (client: ClientSpec VF) : Prec VE VF :=
  fun s ρs => vioClientSpecPossSet i A m client ρs.

Definition coClientSpecRelt {T E F} {VE: Spec T E} {VF: Spec T F} (i: Name T) (A: Type) (m: F A) (client: ClientSpec VF) : Relt VE VF :=
  fun s1 ρs1 s2 ρs2 => vioClientSpecPossSet i A m client ρs1 /\ vioClientSpecPossSet i A m client ρs2.

Definition coClientSpecPost {T E F} {VE: Spec T E} {VF: Spec T F} (i: Name T) (A B: Type) (m: F A) (client: ClientSpec VF) : Post VE VF B:=
  fun _ s1 ρs1 s2 ρs2 => vioClientSpecPossSet i A m client ρs1 /\ vioClientSpecPossSet i A m client ρs2.

(* Definition clientSpecToRelt {T E F} {VE: Spec T E} {VF: Spec T F} (client: ClientSpec VF) (i: Name T) (A: Type) (m: F A) : Relt VE VF :=
  fun s1 ρs1 s2 ρs2 => s1 = s2 /\ ρs1 = ρs2 /\ (forall ρ, ρs1 ρ -> client A m i (PState ρ)).

Definition coRelt {T E F} {VE: Spec T E} {VF: Spec T F} (R: Relt VE VF) : Relt VE VF :=
  fun s1 ρs1 s2 ρs2 => ~ R s1 ρs1 s2 ρs2. *)

Definition clientSpecSound {T E F} {VE: Spec T E} {VF: Spec T F} (client: ClientSpec VF) (R: Name T -> Relt VE VF) :=
  forall A (m: F A) i, 
    (stableRelt (R i) (coClientSpecRelt i A m client) /\
     forall s, client A m i s -> (forall s', ~VF.(Step) s (i, CallEv m) s')).

Lemma coClientSpecIdem {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf (client: ClientSpec VF) i A (m: F A) :
  (ReltWithUBFull acf HAcf (coClientSpecRelt (E:=E) (VE:=VE) i A m client)) ->>
    ReltWithUBFull acf HAcf (coClientSpecRelt (E:=E) (VE:=VE) i A m client) = 
  ReltWithUBFull acf HAcf (coClientSpecRelt (E:=E) (VE:=VE) i A m client).
Proof.
  unfold ReltCompose.
  extensionality s1.
  extensionality ρs1.
  extensionality s2.
  extensionality ρs2.
  apply propositional_extensionality.
  split; intros.
  + destruct_all.
    unfold ReltWithUBFull, coClientSpecRelt in *; simpl in *.
    easy.
  + unfold ReltWithUBFull, coClientSpecRelt in *; simpl in *.
    exists s1, ρs1.
    easy.
Qed.

Lemma stableReltStablePost {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf (client: ClientSpec VF) i A B (m: F A) (R: Name T -> Relt VE VF):
  stableRelt (R i) (coClientSpecRelt i A m client) -> 
    stablePost (ReltWithUBFull acf HAcf (R i)) (PostWithUBFull acf HAcf (coClientSpecPost i A B m client)).
Proof.
  intros.
  pose proof stableReltUB acf HAcf _ _ H as Hstable.
  easy.
Qed.

Definition Prec_in_UB {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf (prec: Prec VE (SpecWithUB VF acf HAcf)) : Prop :=
  forall s ρs,
    (exists (ρ: Poss(SpecWithUB VF acf HAcf)), ρs ρ) /\
    forall (ρ: Poss(SpecWithUB VF acf HAcf)), prec s ρs -> ρs ρ -> exists a, (PState ρ) = inr (UBState_, a).

Definition UBRelt {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf: Relt VE (SpecWithUB VF acf HAcf) :=
  fun s1 ρs1 s2 ρs2 => 
    (forall ρ1, ρs1 ρ1 -> exists a1, (PState ρ1) = inr (UBState_, a1)) /\
    (forall ρ2, ρs2 ρ2 -> exists a2, (PState ρ2) = inr (UBState_, a2)) /\
    (exists ρ, ρs1 ρ) /\ (exists ρ, ρs2 ρ).

Definition UBPost {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf A: Post VE (SpecWithUB VF acf HAcf) A :=
  fun _ s1 ρs1 s2 ρs2 => 
    (forall ρ1, ρs1 ρ1 -> exists a1, (PState ρ1) = inr (UBState_, a1)) /\
    (forall ρ2, ρs2 ρ2 -> exists a2, (PState ρ2) = inr (UBState_, a2)) /\
    (exists ρ, ρs1 ρ) /\ (exists ρ, ρs2 
    ρ).

Definition GuarUBCom {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf i : Relt VE (SpecWithUB VF acf HAcf) :=
  fun s1 ρs1 s2 (ρs2: PossSet(SpecWithUB VF acf HAcf)) => 
    (forall j, j <> i -> fst s1 j = fst s2 j) /\
    ( (exists ρ1, ρs1 ρ1) ->
      (forall ρ1, ρs1 ρ1 -> exists a1, PState ρ1 = inr (UBState_, a1)) ->
      (exists ρ2, ρs2 ρ2) /\
      (forall ρ2, ρs2 ρ2 -> 
        exists a2, PState ρ2 = inr (UBState_, a2) /\ 
        exists (ρ1: Poss(SpecWithUB VF acf HAcf)) a1, PState ρ1 = inr (UBState_, a1) /\ a1 i = a2 i)).

Definition RelyUBCom {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf i : Relt VE (SpecWithUB VF acf HAcf) :=
  fun s1 ρs1 s2 (ρs2: PossSet(SpecWithUB VF acf HAcf)) => 
    fst s1 i = fst s2 i /\
    ( (exists ρ1, ρs1 ρ1) ->
      (forall ρ1, ρs1 ρ1 -> exists a1, PState ρ1 = inr (UBState_, a1)) ->
      (exists ρ2, ρs2 ρ2) /\
      (forall ρ2, ρs2 ρ2 -> 
        exists a2, PState ρ2 = inr (UBState_, a2) /\ 
        exists (ρ1: Poss(SpecWithUB VF acf HAcf)) a1, PState ρ1 = inr (UBState_, a1) /\ a1 i = a2 i)). 

Lemma UBReltStable {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf (R: Relt VE (SpecWithUB VF acf HAcf)) i:
  R ==> RelyUBCom acf HAcf i ->
    stableRelt R (UBRelt acf HAcf).
Proof.
  intros.
  unfold stableRelt.
  unfold ReltCompose, sub, subRelt.
  intros.
  destruct H0 as [s' [ρ' [? ?]]].
  unfold UBRelt in *.
  destruct H0.
  split; [exact H0 |].
  unfold sub, subRelt in H.
  specialize (H _ _ _ _ H1).
  unfold RelyUBCom in H.
  destruct H.
  destruct H2.
  destruct H4.
  specialize (H3 H5 H2).
  split.
  { 
    intros.
    destruct H3.
    specialize (H7 _ H6).
    destruct H7 as [? [? ?]].
    exists x.
    apply H7.
  }
  destruct_all.
  split.
  { exists x0. apply H4. }
  { exists x1. apply H3. }
Qed.

Lemma UBPostStable {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf A (R: Relt VE (SpecWithUB VF acf HAcf)) i:
  R ==> RelyUBCom acf HAcf i ->
    stablePost R (UBPost acf HAcf A).
Proof.
  intros.
  unfold stablePost, stableRelt.
  unfold ReltCompose, sub, subRelt.
  intros.
  destruct H0 as [s' [ρ' [? ?]]].
  unfold UBRelt in *.
  destruct H0.
  split; [exact H0 |].
  unfold sub, subRelt in H.
  specialize (H _ _ _ _ H1).
  unfold RelyUBCom in H.
  destruct H.
  destruct H2.
  destruct H4.
  specialize (H3 H5 H2).
  split.
  { 
    intros.
    destruct H3.
    specialize (H7 _ H6).
    destruct H7 as [? [? ?]].
    exists x.
    apply H7.
  }
  destruct_all.
  split.
  { exists x0. apply H4. }
  { exists x1. apply H3. }
Qed.

Lemma UBPostUBRelt {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall A (v: A), (@UBPost T E F VE VF acf HAcf A v) = UBRelt acf HAcf.
Proof. reflexivity. Qed.

Lemma UBReltID {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf: 
  forall s ρs t, 
    (exists ρ, ρs ρ) ->
    (forall ρ: Poss(SpecWithUB VF acf HAcf), ρs ρ -> exists a, (PState ρ) = inr (UBState_, a)) ->
      (@UBRelt T E F VE VF acf HAcf) s ρs t ρs.
Proof.
  unfold UBRelt.
  intros.
  repeat split; intros.
  { specialize (H0 ρ1 H1). destruct H0. exists x. easy. }
  { specialize (H0 ρ2 H1). destruct H0. exists x. easy. }
  { apply H. }
  { apply H. }
Qed.

Lemma UBPostId {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf A: 
  forall v s ρs t, 
    (exists ρ, ρs ρ) ->
    (forall ρ: Poss(SpecWithUB VF acf HAcf), ρs ρ -> exists a, (PState ρ) = inr (UBState_, a)) ->
      (@UBPost T E F VE VF acf HAcf A) v s ρs t ρs.
Proof.
  unfold UBPost.
  intros.
  repeat split; intros.
  { specialize (H0 ρ1 H1). destruct H0. exists x. easy. }
  { specialize (H0 ρ2 H1). destruct H0. exists x. easy. }
  { apply H. }
  { apply H. }
Qed.

Lemma UBReltIdem {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  (@UBRelt T E F VE VF acf HAcf) ->> (UBRelt acf HAcf) = UBRelt acf HAcf.
Proof.
  unfold sub, subRelt, ReltCompose.
  extensionality s1.
  extensionality ρs1.
  extensionality s2.
  extensionality ρs2.
  apply propositional_extensionality.
  split; intros.
  + destruct H as [s [ρs [? ?]]].
    unfold UBRelt in *.
    destruct_all.
    repeat split.
    { apply H. }
    { apply H1. }
    { exists x2. apply H5. }
    { exists x. apply H3. }
  + exists s1, ρs1.
    split; [ | easy].
    unfold UBRelt in *.
    destruct_all.
    repeat split.
    { apply H. }
    { apply H. }
    { exists x0. apply H1. }
    { exists x0. apply H1. }
Qed.

Lemma UB_verify_UB
  {T E F}
  {VE : Spec T E}
  {VF : Spec T F}
  {acf HAcf}
  (R G : Relt VE (SpecWithUB VF acf HAcf))
  (P : Relt VE (SpecWithUB VF acf HAcf)) :
    forall A (prog : Prog E A) (i: Name T),
      P ==> UBRelt acf HAcf ->
      R ==> RelyUBCom acf HAcf i ->
      GuarUBCom acf HAcf i ==> G ->
      VerifyProg i R G P prog (UBPost acf HAcf A).
Proof.
  unfold VerifyProg.
  intros.
  rewrite paco_eqv.
  generalize dependent P.
  generalize dependent prog.
  pcofix rec. 
  destruct prog; intros.
  + pfold.
    econstructor.
    { eapply UBReltStable. apply H0. }
    { eapply UBPostStable. apply H0. }
    { unfold Commit. intros.
      exists ρs.
      unfold ReltToPrec in H.
      destruct H as [s' [ρ' ? ]].
      subst.
      unfold sub, subRelt, PrecToRelt in H2.
      specialize (H2 s' ρ' s ρs (ltac:(auto))).
      destruct H2 as [? [? [? ?]]].
      split; [exact H8 |].
      split.
      { intros.
        exists σ.
        split; [exact H9 |].
        constructor.
      }
      split.
      {
        unfold UBRelt.
        repeat split; intros.
        { specialize (H6 _ H9). apply H6. }
        { specialize (H6 _ H9). apply H6. }
        { apply H8. }
        { apply H8. }
      }
      {
        unfold sub, subRelt in H1.
        apply H1. clear H1.
        unfold GuarUBCom.
        repeat split; intros.
        { unfold differ_pointwise in H3. specialize (H3 _ H1). easy. }
        { apply H1. }
        { specialize (H6 _ H10).
          destruct H6 as [a2 ?].
          exists a2.
          split; [exact H6 |].
          exists ρ2, a2.
          easy.
        }
      }
    }
    {
      intros.
      split.
      { 
        unfold Commit; intros.
        exists ρs.
        split.
        { destruct H as [s' [ρ' [? [? [? ?]]]]].
          unfold UBRelt in H6.
          destruct H6 as [? [? [? ?]]].
          apply H9.
        }
        split.
        { intros. exists σ. split; [exact H6 | constructor]. }
        split.
        { unfold ReltCompose in H.
          destruct H as [s' [ρ' [? [? [? ?]]]]].
          unfold UBRelt in H6.
          destruct H6 as [? [? [? ?]]].
          apply UBPostId.
          { apply H9. }
          { intros. apply H7, H10. }
        }
        { apply H1. unfold GuarUBCom.
          split; intros.
          { unfold differ_pointwise in H3. specialize (H3 _ H6). easy. }
          { unfold ReltCompose in H.
            destruct H as [s' [ρ' [? [? [? ?]]]]].
            destruct H8 as [? [? [? ?]]].
            repeat split; intros.
            { apply H11. }
            { specialize(H9 _ H12).
              destruct H9 as [a2 ?].
              exists a2.
              split; [exact H9 |].
              exists ρ2, a2.
              easy.
            }
          }
        }
      }
      {
        right.
        apply rec.
        rewrite UBPostUBRelt.
        rewrite UBReltIdem.
        apply (subReltTrans _ (UBRelt acf HAcf ->> UBRelt acf HAcf)).
        { apply reltComposeMono1, H2. }
        { rewrite UBReltIdem. easy. }
      }
    }
  + pfold. constructor.
    rewrite UBPostUBRelt.
    apply H2.
  + pfold. econstructor. 
    { eapply UBReltStable. apply H0. }
    { unfold SilentStep.
      intros.
      unfold ReltToPrec in H.
      destruct H as [s' [ρ' ? ]].
      specialize (H2 _ _ _ _ H).
      destruct H2 as [? [? [? ?]]].
      split.
      { apply UBReltID.
        { apply H7. }
        { apply H5. }
      }
      { apply H1.
        unfold GuarUBCom.
        repeat split; intros.
        { unfold differ_pointwise in H3. specialize (H3 _ H8). easy. }
        { apply H7. }
        { specialize (H5 _ H10).
          destruct H5 as [a2 ?].
          exists a2.
          split; [exact H5 |].
          exists ρ2, a2.
          easy.
        }
      }
    }
    { right.
      apply rec.
      apply (subReltTrans _ (UBRelt acf HAcf ->> UBRelt acf HAcf)).
      { apply reltComposeMono1, H2. }
      { rewrite UBReltIdem. easy. }
    }
Qed.

(* 
Definition UBRelt2 {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf A (m: F A) i: Relt VE (SpecWithUB VF acf HAcf) :=
  fun s1 ρs1 s2 ρs2 => 
    (forall ρ1, ρs1 ρ1 -> exists a1, (PState ρ1) = inr (UBState_, a1)) /\
    (forall ρ2, ρs2 ρ2 -> exists a2, (PState ρ2) = inr (UBState_, a2) /\ (PCalls ρ2 i = CallDone m) /\ (exists v, (PRets ρ2 i = RetPoss m v))) /\
    (exists ρ, ρs1 ρ) /\ (exists ρ, ρs2 ρ).

Definition UBPost2 {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf A (m: F A) i: Post VE (SpecWithUB VF acf HAcf) A :=
  fun v s1 ρs1 s2 ρs2 => 
    (forall ρ1, ρs1 ρ1 -> exists a1, (PState ρ1) = inr (UBState_, a1)) /\
    (forall ρ2, ρs2 ρ2 -> exists a2, (PState ρ2) = inr (UBState_, a2) /\ (PCalls ρ2 i = CallDone m) /\ (PRets ρ2 i = RetPoss m v)) /\
    (exists ρ, ρs1 ρ) /\ (exists ρ, ρs2 ρ).

Definition GuarUBCom2 {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf i : Relt VE (SpecWithUB VF acf HAcf) :=
  fun s1 ρs1 s2 (ρs2: PossSet(SpecWithUB VF acf HAcf)) => 
    (forall j, j <> i -> fst s1 j = fst s2 j) /\
    ( (exists ρ1, ρs1 ρ1) ->
      (forall ρ1, ρs1 ρ1 -> exists a1, PState ρ1 = inr (UBState_, a1)) ->
      (exists ρ2, ρs2 ρ2) /\
      (forall ρ2, ρs2 ρ2 -> 
        exists a2, PState ρ2 = inr (UBState_, a2) /\ 
        exists (ρ1: Poss(SpecWithUB VF acf HAcf)) a1, PState ρ1 = inr (UBState_, a1) /\ a1 i = a2 i)).

Definition RelyUBCom2 {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf i : Relt VE (SpecWithUB VF acf HAcf) :=
  fun s1 ρs1 s2 (ρs2: PossSet(SpecWithUB VF acf HAcf)) => 
    fst s1 i = fst s2 i /\
    ( (exists ρ1, ρs1 ρ1) ->
      (forall ρ1, ρs1 ρ1 -> exists a1, PState ρ1 = inr (UBState_, a1)) ->
      (exists ρ2, ρs2 ρ2) /\
      (forall ρ2, ρs2 ρ2 -> 
        exists a2, PState ρ2 = inr (UBState_, a2) /\ 
        exists (ρ1: Poss(SpecWithUB VF acf HAcf)) a1, PState ρ1 = inr (UBState_, a1) /\ a1 i = a2 i)). 

Lemma UBReltStable2 {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf (R: Relt VE (SpecWithUB VF acf HAcf)) i:
  R ==> RelyUBCom2 acf HAcf i ->
    stableRelt R (UBRelt2 acf HAcf).
Proof.
  intros.
  unfold stableRelt.
  unfold ReltCompose, sub, subRelt.
  intros.
  destruct H0 as [s' [ρ' [? ?]]].
  unfold UBRelt in *.
  destruct H0.
  split; [exact H0 |].
  unfold sub, subRelt in H.
  specialize (H _ _ _ _ H1).
  unfold RelyUBCom in H.
  destruct H.
  destruct H2.
  destruct H4.
  specialize (H3 H5 H2).
  split.
  { 
    intros.
    destruct H3.
    specialize (H7 _ H6).
    destruct H7 as [? [? ?]].
    exists x.
    apply H7.
  }
  destruct_all.
  split.
  { exists x0. apply H4. }
  { exists x1. apply H3. }
Qed.

Lemma UBPostStable {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf A (R: Relt VE (SpecWithUB VF acf HAcf)) i:
  R ==> RelyUBCom acf HAcf i ->
    stablePost R (UBPost acf HAcf A).
Proof.
  intros.
  unfold stablePost, stableRelt.
  unfold ReltCompose, sub, subRelt.
  intros.
  destruct H0 as [s' [ρ' [? ?]]].
  unfold UBRelt in *.
  destruct H0.
  split; [exact H0 |].
  unfold sub, subRelt in H.
  specialize (H _ _ _ _ H1).
  unfold RelyUBCom in H.
  destruct H.
  destruct H2.
  destruct H4.
  specialize (H3 H5 H2).
  split.
  { 
    intros.
    destruct H3.
    specialize (H7 _ H6).
    destruct H7 as [? [? ?]].
    exists x.
    apply H7.
  }
  destruct_all.
  split.
  { exists x0. apply H4. }
  { exists x1. apply H3. }
Qed.

Lemma UBPostUBRelt {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  forall A (v: A), (@UBPost T E F VE VF acf HAcf A v) = UBRelt acf HAcf.
Proof. reflexivity. Qed.

Lemma UBReltID {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf: 
  forall s ρs t, 
    (exists ρ, ρs ρ) ->
    (forall ρ: Poss(SpecWithUB VF acf HAcf), ρs ρ -> exists a, (PState ρ) = inr (UBState_, a)) ->
      (@UBRelt T E F VE VF acf HAcf) s ρs t ρs.
Proof.
  unfold UBRelt.
  intros.
  repeat split; intros.
  { specialize (H0 ρ1 H1). destruct H0. exists x. easy. }
  { specialize (H0 ρ2 H1). destruct H0. exists x. easy. }
  { apply H. }
  { apply H. }
Qed.

Lemma UBPostId {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf A: 
  forall v s ρs t, 
    (exists ρ, ρs ρ) ->
    (forall ρ: Poss(SpecWithUB VF acf HAcf), ρs ρ -> exists a, (PState ρ) = inr (UBState_, a)) ->
      (@UBPost T E F VE VF acf HAcf A) v s ρs t ρs.
Proof.
  unfold UBPost.
  intros.
  repeat split; intros.
  { specialize (H0 ρ1 H1). destruct H0. exists x. easy. }
  { specialize (H0 ρ2 H1). destruct H0. exists x. easy. }
  { apply H. }
  { apply H. }
Qed.

Lemma UBReltIdem {T E F} {VE: Spec T E} {VF: Spec T F} acf HAcf:
  (@UBRelt T E F VE VF acf HAcf) ->> (UBRelt acf HAcf) = UBRelt acf HAcf.
Proof.
  unfold sub, subRelt, ReltCompose.
  extensionality s1.
  extensionality ρs1.
  extensionality s2.
  extensionality ρs2.
  apply propositional_extensionality.
  split; intros.
  + destruct H as [s [ρs [? ?]]].
    unfold UBRelt in *.
    destruct_all.
    repeat split.
    { apply H. }
    { apply H1. }
    { exists x2. apply H5. }
    { exists x. apply H3. }
  + exists s1, ρs1.
    split; [ | easy].
    unfold UBRelt in *.
    destruct_all.
    repeat split.
    { apply H. }
    { apply H. }
    { exists x0. apply H1. }
    { exists x0. apply H1. }
Qed.

Lemma UB_verify_UB2
  {T E F}
  {VE : Spec T E}
  {VF : Spec T F}
  {acf HAcf}
  (R G : Relt VE (SpecWithUB VF acf HAcf))
  (P : Relt VE (SpecWithUB VF acf HAcf)) :
    forall A (prog : Prog E A) (i: Name T) m,
      P ==> UBRelt2 acf HAcf A m i ->
      R ==> RelyUBCom2 acf HAcf i ->
      GuarUBCom2 acf HAcf i ==> G ->
      VerifyProg i R G P prog (UBPost2 acf HAcf A m i).
Proof.
  unfold VerifyProg.
  intros.
  rewrite paco_eqv.
  generalize dependent P.
  generalize dependent prog.
  pcofix rec. 
  destruct prog; intros.
  + pfold.
    econstructor.
    { eapply UBReltStable. apply H0. }
    { eapply UBPostStable. apply H0. }
    { unfold Commit. intros.
      exists ρs.
      unfold ReltToPrec in H.
      destruct H as [s' [ρ' ? ]].
      subst.
      unfold sub, subRelt, PrecToRelt in H2.
      specialize (H2 s' ρ' s ρs (ltac:(auto))).
      destruct H2 as [? [? [? ?]]].
      split; [exact H8 |].
      split.
      { intros.
        exists σ.
        split; [exact H9 |].
        constructor.
      }
      split.
      {
        unfold UBRelt.
        repeat split; intros.
        { specialize (H6 _ H9). apply H6. }
        { specialize (H6 _ H9). apply H6. }
        { apply H8. }
        { apply H8. }
      }
      {
        unfold sub, subRelt in H1.
        apply H1. clear H1.
        unfold GuarUBCom.
        repeat split; intros.
        { unfold differ_pointwise in H3. specialize (H3 _ H1). easy. }
        { apply H1. }
        { specialize (H6 _ H10).
          destruct H6 as [a2 ?].
          exists a2.
          split; [exact H6 |].
          exists ρ2, a2.
          easy.
        }
      }
    }
    {
      intros.
      split.
      { 
        unfold Commit; intros.
        exists ρs.
        split.
        { destruct H as [s' [ρ' [? [? [? ?]]]]].
          unfold UBRelt in H6.
          destruct H6 as [? [? [? ?]]].
          apply H9.
        }
        split.
        { intros. exists σ. split; [exact H6 | constructor]. }
        split.
        { unfold ReltCompose in H.
          destruct H as [s' [ρ' [? [? [? ?]]]]].
          unfold UBRelt in H6.
          destruct H6 as [? [? [? ?]]].
          apply UBPostId.
          { apply H9. }
          { intros. apply H7, H10. }
        }
        { apply H1. unfold GuarUBCom.
          split; intros.
          { unfold differ_pointwise in H3. specialize (H3 _ H6). easy. }
          { unfold ReltCompose in H.
            destruct H as [s' [ρ' [? [? [? ?]]]]].
            destruct H8 as [? [? [? ?]]].
            repeat split; intros.
            { apply H11. }
            { specialize(H9 _ H12).
              destruct H9 as [a2 ?].
              exists a2.
              split; [exact H9 |].
              exists ρ2, a2.
              easy.
            }
          }
        }
      }
      {
        right.
        apply rec.
        rewrite UBPostUBRelt.
        rewrite UBReltIdem.
        apply (subReltTrans _ (UBRelt acf HAcf ->> UBRelt acf HAcf)).
        { apply reltComposeMono1, H2. }
        { rewrite UBReltIdem. easy. }
      }
    }
  + pfold. constructor.
    rewrite UBPostUBRelt.
    apply H2.
  + pfold. econstructor. 
    { eapply UBReltStable. apply H0. }
    { unfold SilentStep.
      intros.
      unfold ReltToPrec in H.
      destruct H as [s' [ρ' ? ]].
      specialize (H2 _ _ _ _ H).
      destruct H2 as [? [? [? ?]]].
      split.
      { apply UBReltID.
        { apply H7. }
        { apply H5. }
      }
      { apply H1.
        unfold GuarUBCom.
        repeat split; intros.
        { unfold differ_pointwise in H3. specialize (H3 _ H8). easy. }
        { apply H7. }
        { specialize (H5 _ H10).
          destruct H5 as [a2 ?].
          exists a2.
          split; [exact H5 |].
          exists ρ2, a2.
          easy.
        }
      }
    }
    { right.
      apply rec.
      apply (subReltTrans _ (UBRelt acf HAcf ->> UBRelt acf HAcf)).
      { apply reltComposeMono1, H2. }
      { rewrite UBReltIdem. easy. }
    }
Qed. *)