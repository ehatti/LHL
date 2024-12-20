From LHL.Core Require Import
  Program
  Specs
  Traces
  Logic
  LogicPaco
  LogicFacts
  ProgramFacts.

From Coq Require Import
  Program.Equality
  Logic.PropExtensionality
  Logic.FunctionalExtensionality.

From LHL.Util Require Import
  Tactics.

From Paco Require Import paco.

Ltac ddestruct H := dependent destruction H.

Definition IsAtomic {T E A} (VE : Spec T E) (m : E A) :=
  forall i s t e r,
    VE.(Step) s (i, CallEv m) t ->
    VE.(Step) t e r ->
    exists v,
      e = (i, RetEv m v).

Section rules.

Context
  {T}
  {i : Name T}
  {E F : ESig}
  {VE : Spec T E}
  {VF : Spec T F}
  {R G : Relt VE VF}.

Lemma weakenPost {A P} {C : Prog E A} :
  forall Q Q',
  VerifyProg i R G P C Q ->
  (forall v, Q v ==> Q' v) ->
  VerifyProg i R G P C Q'.
unfold VerifyProg. intros.
repeat rewrite paco_eqv in *.
generalize dependent P. generalize dependent C.
pcofix rec. intros.
punfold H1. pfold.
dependent destruction H1.
{
  econstructor. unfold sub, subRelt in *.
  intros. apply H0. apply H. easy.
}
{
  econstructor. exact H. exact H1. easy.
  intros. specialize (H3 v). destruct_all.
  split. easy.
  destruct H4. 2: destruct H4.
  right. eapply rec. easy.
}
{
  destruct H2. 2: destruct H2.
  econstructor. exact H. easy.
  right. apply rec. easy.
}
Qed.

Lemma weakenPrec {A Q} {C : Prog E A} :
  forall P P',
  VerifyProg i R G P C Q ->
  P' ==> P ->
  VerifyProg i R G P' C Q.
intros.
eapply weakenSafe.
exact H0. easy.
Qed.

Lemma lemNoOp {A Q} {P : Relt VE VF} {C : Prog E A} :
  forall QS,
  Stable R QS ->
  SilentStep i G P QS ->
  VerifyProg i R G (P ->> QS) C Q ->
  VerifyProg i R G P (NoOp C) Q.
intros.
econstructor. exact H. easy. easy.
Qed.

Lemma lemRet {A P Q} {v : A} :
  P ==> Q v ->
  VerifyProg i R G P (ret v) Q.
intros.
constructor.
unfold sub, subRelt, id.
intros. psimpl.
apply H. easy.
Qed.

Lemma lemCall {A Q S} {P : Relt VE VF} {m : E A} :
  Stable R Q ->
  Stable R S ->
  Commit i G P (CallEv m) Q ->
  (forall v, Commit i G (P ->> Q) (RetEv m v) (S v)) ->
  VerifyProg i R G P (call m) (fun v => P ->> Q ->> S v).
intros.
econstructor. exact H. exact H0.
unfold Commit, id.
intros. psimpl.
apply H1.
exists x, x0.
easy. easy. easy. easy.
intros. specialize (H2 v).
split. easy.
econstructor. unfold sub, subRelt. intros.
easy.
Qed.

Lemma lemForget {A} {P Q : Relt VE VF} {S : Post VE VF A} {C : Prog E A} :
  VerifyProg i R G (fun _ _ t ys => exists s xs, Q s xs t ys) C S ->
  VerifyProg i R G (P ->> Q) C S.
intros.
eapply weakenPrec. exact H.
unfold sub, subRelt.
intros. psimpl.
exists x, x0. easy.
Qed.

Lemma lemBind {A B P S} {C : Prog E A} {k : A -> Prog E B} :
  forall Q,
  VerifyProg i R G P C Q ->
  (forall v, VerifyProg i R G (Q v) (k v) S) ->
  VerifyProg i R G P (x <- C; k x) S.
unfold VerifyProg.
intros.
repeat rewrite paco_eqv in *.
generalize dependent P. generalize dependent C. generalize dependent Q.
generalize dependent k. generalize dependent A.
pcofix rec. intros.
punfold H1. dependent destruction H1.
{
  rewrite frobProgId at 1. simpl.
  assert (k v = match k v with
  | @Bind _ _ A0 e f => Bind e f
  | Return a => Return a
  | NoOp p' => NoOp p'
  end) by (destruct (k v); easy). rewrite <- H1. clear H1.
  specialize (H0 v).
  rewrite paco_eqv in H0. punfold H0.
  clear rec.
  generalize dependent P. generalize dependent (Q v).
  generalize dependent (k v). clear k v Q.
  pcofix rec. intros.
  pfold. dependent destruction H0.
  {
    econstructor.
    unfold sub, subRelt in *.
    auto.
  }
  {
    econstructor.
    exact H. exact H0.
    eapply weakenCommitPre. exact H3. easy.
    intros. specialize (H2 v). destruct_all.
    split.
    eapply weakenCommitPre with (P:= P ->> QI).
    unfold sub, subRelt, ReltCompose. intros. destruct_all.
    repeat eexists.
    apply H3. exact H5. easy.
    easy.
    destruct H4.
    punfold H4.
    right. eapply rec. exact H4.
    unfold sub, subRelt, ReltCompose. intros. destruct_all. repeat eexists.
    apply H3. exact H5. exact H6. easy.
    destruct H4.
  }
  {
    destruct H1. 2: destruct H1.
    econstructor. exact H.
    unfold SilentStep. intros. apply H0.
    unfold ReltToPrec in *. destruct_all. repeat eexists.
    apply H2. exact H3.
    easy. easy.
    punfold H1.
    right. eapply rec. exact H1.
    unfold sub, subRelt, ReltCompose. intros. destruct_all. repeat eexists.
    apply H2. exact H3. easy.
  }
}
{
  rewrite frobProgId at 1. simpl. pfold. econstructor.
  exact H. exact H1. easy.
  intros. specialize (H3 v). destruct_all.
  split. easy.
  destruct H4. 2: destruct H4.
  punfold H4.
  right.
  eapply rec. exact H0.
  pfold. easy.
}
{
  rewrite frobProgId at 1. simpl. pfold. econstructor.
  exact H. easy.
  destruct H2. 2: destruct H2.
  punfold H2. right.
  eapply rec. exact H0.
  pfold. easy.
}
Qed.

Lemma lemIf {A} {B : Prog E bool} {CT CF : Prog E A} {P : Relt VE VF} {Q : Post VE VF A} :
  forall PT PF : Relt VE VF,
  VerifyProg i R G P B (fun b => if b then PT else PF) ->
  VerifyProg i R G PT CT Q ->
  VerifyProg i R G PF CF Q ->
  VerifyProg i R G P (b <- B; if b then CT else CF) Q.
intros.
eapply lemBind. exact H.
intros. now destruct v.
Qed.

Lemma foldProg {A} :
  forall p : Prog E A,
  match p with
  | Return v => Return v
  | Bind m k => Bind m k
  | NoOp p => NoOp p
  end = p.
intros.
destruct p; easy.
Qed.

Definition SomeRet {T A E F VE VF} (Q : @Post T E F VE VF A) : Post VE VF unit :=
  fun _ s ρ t σ => exists v, Q v s ρ t σ.

Definition UnitRet {T E F VE VF} (Q : @Relt T E F VE VF) : Post VE VF unit :=
  fun _ => Q.

Lemma lemWhile {P} {I : Post VE VF bool} {B : Prog E bool} {C : Prog E unit} {S : Relt VE VF} :
  Stable R S ->
  SilentStep i G I S ->
  I ->> S ==> P ->
  VerifyProg i R G P B I ->
  VerifyProg i R G (I true) C (SomeRet I) ->
  VerifyProg i R G P (while B C) (UnitRet (I false)).
unfold while, VerifyProg.
intros S_stable S_step imp.
repeat rewrite paco_eqv.
intros.
cut (
  forall B' P',
  paco_safe i R G P' B' I ->
  paco_safe i R G P' (whileAux B C B' C) (UnitRet (I false))
).
{ intros. apply H1 with (P':=P). easy. }
pcofix rec. intros. punfold H2. dependent destruction H2.
{
  destruct v.
  2:{
    pfold.
    rewrite frobProgId at 1. cbn.
    econstructor. easy.
  }
  rewrite <- paco_eqv in H0.
  eapply weakenPrec with (P':=P0) in H0. 2: easy.
  unfold VerifyProg in H0. rewrite paco_eqv in H0.
  cut (
    forall (P0' : Relt VE VF) C',
    paco_safe i R G P0' C' (SomeRet I) ->
    paco2 (paco_safeF i R G (UnitRet (I false))) r P0' (whileAux B C (Return true) C')
  ).
  {
    intros. apply H2. easy.
  }
  pcofix rec'. intros. punfold H3. dependent destruction H3.
  {
    rewrite frobProgId at 1. cbn.
    pfold. econstructor. exact S_stable.
    {
      unfold SilentStep. intros. apply S_step.
      unfold ReltToPrec in *. destruct_all.
      apply H2 in H3. destruct H3.
      repeat eexists.
      exact H3.
      easy. easy.
    }
    {
      right. eapply rec.
      rewrite <- paco_eqv.
      eapply weakenPrec with (P:=P).
      unfold VerifyProg. rewrite paco_eqv.
      easy.
      unfold sub, subRelt. intros.
      apply imp. psimpl.
      apply H2 in H3. destruct H3.
      repeat eexists. exact H3. easy.
    }
  }
  {
    rewrite frobProgId at 1. cbn. pfold. econstructor.
    exact H2. exact H3. easy.
    intros. specialize (H5 v). destruct_all.
    split. easy.
    destruct H6. 2: destruct H6.
    right. eapply rec'. easy.
  }
  {
    rewrite frobProgId at 1. cbn. pfold. econstructor.
    exact H2. easy.
    destruct H4. 2: destruct H4.
    right. eapply rec'. easy.
  }
}
{
  pfold. rewrite frobProgId at 1. cbn.
  econstructor. exact H1. exact H2. easy.
  intros.
  specialize (H4 v). destruct_all.
  split. easy.
  destruct H5. 2: destruct H5.
  right. eapply rec. easy.
}
{
  pfold. rewrite frobProgId at 1. cbn.
  econstructor. exact H1. easy.
  destruct H3. 2: destruct H3.
  right. eapply rec. easy.
}
Qed.

Lemma lemWhile2 {P} {I : Post VE VF bool} {B : Prog E bool} {C : Prog E unit} {Q: Post VE VF unit} {S : Relt VE VF} :
  Stable R S ->
  SilentStep i G Q S ->
  Q ->> S ==> P ->
  VerifyProg i R G P B I ->
  VerifyProg i R G (I true) C Q ->
  VerifyProg i R G P (while B C) (UnitRet (I false)).
Proof.
  unfold while, VerifyProg.
  rewrite ! paco_eqv.
  intros S_stable H_silent HInv HPI HIQ. 
  cut (
    forall B' P',
    paco_safe i R G P' B' I ->
    paco_safe i R G P' (whileAux B C B' C) (UnitRet (I false))
  ).
  { intros. apply H. easy. }
  pcofix rec. intros. punfold H0. dependent destruction H0.
  { destruct v.
    { cut(
        forall C' P',
        paco_safe i R G P' C' Q ->
        paco2 (paco_safeF i R G (UnitRet (I false))) r P' (whileAux B C (Return true) C')).
      { intros. apply H0. rewrite <- paco_eqv. eapply weakenPrec. 
        { unfold VerifyProg. rewrite paco_eqv. apply HIQ. }
        { apply H. }
      }
      pcofix rec'. intros. punfold H1. dependent destruction H1.
      { rewrite frobProgId. cbn. pfold. econstructor. exact S_stable.
        { unfold SilentStep in *.
          intros.
          destruct v.
          assert(ReltToPrec (PostToRelt Q) (ths, s) ρs).
          { unfold PostToRelt. unfold ReltToPrec.
            unfold ReltToPrec in H1.
            destruct H1 as [s' [ρs' ?]].
            specialize (H0 _ _ _ _ H1).
            do 3 eexists.
            apply H0.
          }
          specialize (H_silent s ths ρs tht H4 H2 H3).
          easy.
        }
        { right. apply rec. rewrite <- paco_eqv. eapply weakenPrec. 
          { unfold VerifyProg. rewrite paco_eqv. eapply HPI. }
          { eapply subReltTrans. 2: apply HInv.
            apply reltComposeMono1. destruct v. unfold PostToRelt.
            unfold sub, subRelt. intros. exists tt. apply H0. apply H1.
          }
        }
      }
      { rewrite frobProgId. cbn. pfold. econstructor.
        { apply H0. }
        { apply H1. }
        { apply H2. }
        { intros. specialize (H3 v). destruct H3.
          split; [easy |]. 
          destruct H4. 2: inversion H4.
          right. apply rec'. easy.
        }
      }
      { rewrite frobProgId. cbn. pfold. econstructor.
        { apply H0. }
        { apply H1. }
        { right. apply rec'. destruct H2. 2: inversion H2. easy. }
      }
    }
    { rewrite frobProgId. cbn. pfold. econstructor. unfold UnitRet. easy. }
  }
  { rewrite frobProgId. cbn. pfold. econstructor. exact H. exact H0. easy.
    intros. specialize (H2 v). destruct H2. split; [easy |].
    destruct H3. 2: inversion H3. right. apply rec. easy.
  }
  { rewrite frobProgId. cbn. pfold. econstructor. exact H. easy.
    destruct H1. 2: inversion H1. right. apply rec. easy.
  }
Qed.

Lemma strongCommit {P Q : Relt VE VF} {e} :
  Commit i G P e Q ->
  Commit i G P e (prComp P Q).
unfold Commit. intros.
assert (H0' := H0).
apply H with (t:=t) in H0.
all: try easy. psimpl.
exists x.
split. exists x0. easy.
split. easy.
split.
{
  split. exists x1, x2.
  easy. easy.
}
easy.
Qed.

End rules.

Lemma disjCommit {T E F} {VE : Spec T E} {VF : Spec T F} {PL PR QL QR GL GR  : Relt VE VF} {i e} :
  Commit i GL PL e QL ->
  Commit i GR PR e QR ->
  Commit i (GL \4/ GR) (ReltToPrec (PL \4/ PR)) e (QL \4/ QR).
unfold Commit. intros.
unfold ReltToPrec in H1. destruct_all. destruct H1.
{
  apply H with (t:=t) (ρs:=ρs) in H4.
  destruct_all. exists x1. split. exists x2. easy.
  split. easy.
  split.
  left. easy.
  left. easy.
  exists x, x0. easy.
  easy.
  easy.
}
{
  apply H0 with (t:=t) (ρs:=ρs) in H4.
  destruct_all. exists x1. split. exists x2. easy.
  split. easy.
  split.
  right. easy.
  right. easy.
  exists x, x0. easy.
  easy.
  easy.
}
Qed.