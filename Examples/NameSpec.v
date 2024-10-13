From LHL.Core Require Import
  Program
  ProgramFacts
  Tensor
  Specs
  LogicPaco
  Logic
  LogicFacts
  ProgramRules.

From LHL.Util Require Import
  Tactics
  TransUtil
  Util.

From Paco Require Import paco.

From Coq Require Import
  Logic.FunctionalExtensionality
  Logic.PropExtensionality.

Variant NameSig {T} : ESig :=
| Self : NameSig (Name T).
Arguments NameSig : clear implicits.

Definition NameState T := option (Name T).

Variant NameStep {T} : NameState T -> ThreadEvent T (NameSig T) -> NameState T -> Prop :=
| CallSelf i : NameStep None (i, CallEv Self) (Some i)
| RetSelf i : NameStep (Some i) (i, RetEv Self i) None.

Program Definition nameSpec {T} : Spec T (NameSig T) := {|
  State := NameState T;
  Step := NameStep;
  Init := None
|}.

Admit Obligations.

Lemma trimProg {E A B} :
  forall (C : Prog E B) (v : A),
  (Return v;; C) = C.
intros.
rewrite frobProgId at 1. simpl.
destruct C; easy.
Qed.

Lemma simpProg {E A B} :
  forall (C : A -> Prog E B) (v : A),
  (x <- Return v; C x) = C v.
intros.
rewrite frobProgId at 1. simpl.
destruct C; easy.
Qed.

CoInductive selfProgWF {E P R} (C : P -> Prog E R) := {
  returnWF :
    forall x v,
      C x = Return v ->
      forall y, exists w,
        C y = Return w /\
        (x = y -> v = w);
  bindWF :
    forall x A (m1 : E A) k1,
      C x = Bind m1 k1 ->
      forall y, exists (m2 : P -> E A) k2,
        C y = Bind (m2 y) (k2 y) /\
        m1 = m2 x /\
        k1 = k2 x /\
        (forall z, selfProgWF (fun i' => k2 i' z));
  noopWF :
    forall x k1,
      C x = NoOp k1 ->
      forall y, exists k2,
        C y = NoOp (k2 y) /\
        k1 = k2 x /\
        selfProgWF k2
}.

Lemma lemBindSelf {T E F A} {VE : Spec T E} {VF : Spec T F}
  {P R G : Relt (tensorSpec nameSpec VE) VF}
  {Q : Post (tensorSpec nameSpec VE) VF A}
  {C : Name T -> Prog (NameSig T |+| E) A} :
  selfProgWF C ->
  forall i : Name T,
  VerifyProg i R G P (_ <- call Self; C i) Q ->
  VerifyProg i R G P (i' <- call Self; C i') Q.
intros WF. intros. ddestruct H.
{
  rewrite frobProgId with (p:=_;;_) in x.
  simpl in x. ddestruct x.
}
2:{
  rewrite frobProgId with (p:=_;;_) in x.
  simpl in x. ddestruct x.
}
rewrite frobProgId with (p:=_;;_) in x.
simpl in x. ddestruct x.
rewrite frobProgId at 1. cbn.
eapply SafeBind with
  (QI:=QI)
  (QR:=fun v s xs t ys => i = v /\ QR v s xs t ys).
easy.
{
  unfold Stable, stablePost, stableRelt, sub, subRelt.
  intros. psimpl. split. easy.
  apply H0. psplit. exact H5. easy.
}
easy.
intros. specialize (H2 v). destruct H2.
split.
{
  clear - H2.
  unfold Commit in *. intros.
  cbn in *. destruct H3. ddestruct H3.
  cut (
    exists σs : Poss VF -> Prop,
    (exists σ : Poss VF, σs σ) /\
    (forall σ : Poss VF, σs σ -> exists ρ : Poss VF, ρs ρ /\ PossSteps ρ σ) /\
    QR i s ρs t σs /\ G s ρs t σs
  ).
  {
    intros. psimpl. exists x1.
    split. exists x2. easy.
    easy.
  }
  eapply H2. all: try easy.
  rewrite <- x0, <- x.
  repeat (easy || constructor).
}
{
  rewrite trimProg in H3.
  rewrite simpProg.
  clear - H3 WF.
  revert H3.
  cut (
    forall C P P',
    selfProgWF C ->
    (P' ==> P) ->
    SafeProg i R G P (C i) Q ->
    SafeProg i R G
    (fun s xs t ys => i = v /\ P' s xs t ys) (C v) Q
  ).
  {
    intros. eapply weakenPrec.
    eapply H with
      (P:= P ->> QI ->> QR v)
      (P':= P ->> QI ->> QR v).
    easy. easy.
    exact H3.
    unfold sub, subRelt.
    intros. psimpl.
    split. easy.
    psplit. exact H0.
    psplit. exact H1.
    easy.
  }
  clear. setoid_rewrite paco_eqv.
  pcofix rec. intros C P P' WF imp.
  intros H0. punfold H0. ddestruct H0;
  pfold; symmetry in x; destruct WF.
  {
    apply returnWF0 with (y:=v) in x.
    psimpl. rewrite H0.
    constructor. unfold sub, subRelt.
    intros. psimpl.
    specialize (H1 eq_refl). subst.
    apply H, imp. easy.
  }
  {
    apply bindWF0 with (y:=v) in x.
    destruct x as [m' [k']].
    psimpl. rewrite H3.
    econstructor.
    { exact H. }
    { exact H0. }
    {
      unfold Commit. intros. psimpl.
      eapply H1.
      {
        exists x, x0.
        apply imp. easy.
      }
      { easy. }
      { easy. }
      { easy. }
    }
    {
      intros.
      specialize (H2 v0).
      split.
      {
        unfold Commit. intros. psimpl.
        eapply H2.
        {
          exists x, x0. psplit.
          apply imp. exact H11.
          easy.
        }
        { easy. }
        { easy. }
        { easy. }
      }
      {
        right.
        assert (
          ((fun s xs t ys => i = v /\ P' s xs t ys) ->> QI ->> QR v0) =
          (fun s xs t ys => i = v /\ (P' ->> QI ->> QR v0) s xs t ys)
        ).
        {
          extensionality s. extensionality xs.
          extensionality t. extensionality ys.
          apply propositional_extensionality.
          split; intros; psimpl.
          {
            split. easy.
            psplit. exact H8.
            psplit. exact H7.
            easy.
          }
          {
            psplit.
            split. easy.
            exact H5.
            psplit.
            exact H8.
            easy.
          }
        }
        rewrite H4 at 1.
        eapply rec with (C:=fun i' => k' i' v0).
        { apply H6. }
        2:{
          psimpl.
          pclearbot. exact u.
        }
        {
          unfold sub, subRelt.
          intros. psimpl.
          psplit. apply imp. exact H5.
          psplit. exact H8.
          easy.
        }
      }
    }
  }
  {
    apply noopWF0 with (y:=v) in x.
    psimpl. rewrite H2.
    econstructor.
    { exact H. }
    {
      unfold SilentStep.
      intros. psimpl.
      eapply H0.
      {
        exists x0, x1.
        now apply imp.
      }
      { easy. }
      { easy. }
    }
    {
      right.
      assert (
        ((fun s xs t ys => i = v /\ P' s xs t ys) ->> QS) =
        (fun s xs t ys => i = v /\ (P' ->> QS) s xs t ys)
      ).
      {
        extensionality s. extensionality xs.
        extensionality t. extensionality ys.
        apply propositional_extensionality.
        split; intros; psimpl.
        {
          split. easy.
          psplit. exact H6.
          easy.
        }
        {
          psplit.
          split. easy.
          exact H5.
          easy.
        }
      }
      rewrite H3.
      eapply rec with (P:= P ->> QS).
      { easy. }
      {
        unfold sub, subRelt.
        intros. psimpl.
        psplit. apply imp. exact H5.
        easy.
      }
      {
        pclearbot.
        unfold paco_safe.
        easy.
      }
    }
  }
}
Qed.