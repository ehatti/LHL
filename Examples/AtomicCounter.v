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
  RacyCounterSpec
  AtomicCounterSpec
  LockSpec.

From Coq Require Import
  Logic.FunctionalExtensionality.

Definition Underlay := LockSig |+| CntSig.

Definition inc : Prog Underlay unit :=
  call Acq;;
  call Inc;;
  call Rel;;
  ret tt.

Definition get : Prog Underlay nat :=
  call Acq;;
  n <- call Get;
  call Rel;;
  ret n.

Definition atomicCntImpl : Impl (LockSig |+| CntSig) CntSig :=
  fun _ m => match m with
  | Inc => inc
  | Get => get
  end.

Definition E := Underlay.
Definition F := CntSig.
Definition VE T :=
  tensorSpec (T:=T)
    (SpecWithUB lockSpec lockClientSpec _ LockActiveMapSound)
    rcntSpec.
Definition VF T := acntSpec (T:=T).

Definition Relt T := SRelt (VE T) (VF T).
Definition Prec T := SPrec (VE T) (VF T).

Notation cntSt s := (RState (snd s)).
Notation locSt s := (LState (snd s)).

(*
We start with the lock being unowned and the underlay counter equaling the overlay counter, and after R this should should still be true. We then proceed to acquiring the lock, and after R should now do nothing.
*)

Record Inv {T}
  (s : InterState F (VE T)) (ρ : Poss (VF T))
:= {
  cnt_def :
    exists k,
      cntSt s = RCntDef (CntIdle k) /\
      PState ρ = CntIdle k;
  loc_def :
    exists s',
      locSt s = inl s'
}.

Lemma Inv_pres {T} :
  forall s ρ t σ,
  Inv (T:=T) s ρ ->
  snd s = snd t ->
  PState ρ = PState σ ->
  Inv t σ.
intros.
destruct H.
constructor.
{
  setoid_rewrite <- H0.
  setoid_rewrite <- H1.
  easy.
}
{ now setoid_rewrite <- H0. }
Qed.

Notation owner s := (
  match s with
  | LockDef o _ => o
  end
).

Definition OwnsLock {T} (i : Name T) (s : (SpecWithUB lockSpec lockClientSpec _ LockActiveMapSound).(State)) := (
  exists s',
    s = inl s' /\
    owner s' = Some i
).

Record InvUnowned {T} (i : Name T)
  (s : InterState F (VE T)) (ρ : Poss (VF T))
:= {
  unown_inv : Inv s ρ;
  loc_unown : ~OwnsLock i (locSt s)
}.

Record InvOwned {T} (i : Name T)
  (s : InterState F (VE T)) (ρ : Poss (VF T))
:= {
  own_inv : Inv s ρ;
  loc_own : OwnsLock i (locSt s)
}.

Record Rely {T} (i : Name T)
  (s : InterState F (VE T)) (ρ : Poss (VF T))
  (t : InterState F (VE T)) (σ : Poss (VF T))
:= {
  call_pres : PCalls ρ i = PCalls σ i;
  ret_pres : PRets ρ i = PRets σ i;
  own_pres : InvOwned i s ρ -> InvOwned i t σ;
  unown_pres : InvUnowned i s ρ -> InvUnowned i t σ;
}.

Definition Guar {T} (i : Name T) : Relt T :=
  fun s ρ t σ =>
    forall j, i <> j -> Rely j s ρ t σ.

Ltac commit :=
  unfold Commit, Guar;
  unfold LiftSPrec, LiftSRelt;
  unfold id; intros; do 2 psimpl.
Ltac stable :=
  unfold SStable, stableSPrec, stablePost, stableSRelt;
  unfold ssub, subSRelt, subSPrec;
  unfold Guar; intros; psimpl.

Lemma eq_inj {A} :
  forall x y : A,
  eq x = eq y ->
  x = y.
intros. now rewrite H.
Qed.

Ltac eq_inj H := apply eq_inj in H; subst.

Require Import Coq.Logic.Classical.

Lemma not_forall {A} {P : A -> Prop} :
  (forall x, ~P x) -> ~(exists x, P x).
unfold not. intros. psimpl.
now apply H with (x:=x).
Qed.

Theorem atomicCntCorrect T :
  VerifyImpl (VE T) (VF T)
    (fun i => LiftSRelt (Rely i))
    (fun i => LiftSRelt (Guar i))
    (fun i _ _ => LiftSPrec (InvUnowned i))
    atomicCntImpl
    (fun i _ _ _ _ _ => LiftSPrec (InvUnowned i))
    (TReturn atomicCntImpl).
constructor.
{
  unfold LiftSRelt.
  intros. subst. exists x.
  repeat (easy || constructor).
}
{
  unfold LiftSRelt, sub, subRelt.
  intros. psimpl.
  specialize (H x eq_refl). psimpl.
  specialize (H1 x2 eq_refl). psimpl.
  exists x1. split. easy. destruct H0, H1.
  constructor; (congruence || tauto).
}
{
  unfold Guar, sub, subRelt, LiftSRelt.
  intros. psimpl. specialize (H0 x eq_refl).
  psimpl. exists x0. split. easy.
  now apply H1.
}
{
  unfold InvokeAny, TInvoke.
  unfold sub, subRelt, LiftSRelt.
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
      exists x.
      split. easy.
      cbn. rewrite eqb_id.
      auto using differ_pointwise_trivial.
    }
  }
  {
    assert (PState x = PState (invPoss i x x1))
      by easy.
    constructor; cbn.
    { now rewrite eqb_nid. }
    { now rewrite eqb_nid. }
    {
      intros. destruct H4.
      constructor.
      {
        eapply Inv_pres.
        exact own_inv0.
        all: easy.
      }
      { now rewrite <- H3 at 1. }
    }
    {
      intros. destruct H4.
      constructor.
      {
        eapply Inv_pres.
        exact unown_inv0.
        all: easy.
      }
      { now rewrite <- H3 at 1. }
    }
  } 
}
{
  unfold ReturnAny, TReturn.
  unfold sub, subRelt, LiftSRelt.
  intros. psimpl. exists (retPoss i x).
  split.
  {
    set_ext y. unfold mapRetPoss, retPoss.
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
      exists x.
      split. easy.
      cbn. rewrite eqb_id.
      destruct H2. ddestruct H1.
      cbn in *. symmetry in x4.
      apply H0 in x4. specialize (x4 x3 eq_refl).
      psimpl. repeat split; try easy.
      apply differ_pointwise_trivial.
      apply differ_pointwise_trivial.
    }
  }
  {
    assert (PState x = PState (retPoss i x))
      by easy.
    constructor; cbn.
    { now rewrite eqb_nid. }
    { now rewrite eqb_nid. }
    {
      intros. destruct H4.
      constructor.
      {
        eapply Inv_pres.
        exact own_inv0.
        all: easy.
      }
      { now rewrite <- H3 at 1. }
    }
    {
      intros. destruct H4.
      constructor.
      {
        eapply Inv_pres.
        exact unown_inv0.
        all: easy.
      }
      { now rewrite <- H3 at 1. }
    }
  }
}
{
  unfold LiftSPrec. intros.
  eexists. split. easy.
  constructor.
  {
    constructor.
    { now exists 0. }
    { now exists LockUnowned. }
  }
  {
    unfold not, OwnsLock.
    cbn. intros. psimpl.
    now ddestruct H.
  }
}
{
  intros.
  apply liftSPrecStable.
  stable. now apply H0.
}
{
  unfold sub, subPrec.
  unfold LiftSRelt, LiftSPrec.
  unfold TReturn, InterOStep.
  intros. psimpl. ddestruct H1.
  cbn in *. ddestruct H.
  exists (retPoss i x3).
  split.
  {
    unfold mapRetPoss, retPoss.
    set_ext y. split; intros; psimpl.
    {
      destruct x5, y. cbn in *.
      f_equal. easy.
      {
        extensionality j.
        dec_eq_nats i j.
        { now rewrite eqb_id. }
        { now rewrite eqb_nid, H9. }
      }
      {
        extensionality j.
        dec_eq_nats i j.
        { now rewrite eqb_id. }
        { now rewrite eqb_nid, H10. }
      }
    }
    {
      symmetry in x2.
      apply H0 in x2.
      specialize (x2 x3 eq_refl).
      psimpl. exists x3. split. easy.
      cbn. rewrite eqb_id.
      repeat split; try easy.
      apply differ_pointwise_trivial.
      apply differ_pointwise_trivial.
    }
  }
  {
    destruct H5.
    constructor.
    {
      eapply Inv_pres.
      exact unown_inv0.
      all: easy.
    }
    { now rewrite <- H2 at 1. }
  }
}
{
  intros.
  eapply weakenPrec with
    (P:=fun _ _ => LiftSPrec (fun s x =>
      InvUnowned i s x /\
      Waiting i m x)).
  2:{
    unfold sub, subRelt, LiftSPrec, LiftSRelt.
    unfold TInvoke. intros. psimpl.
    specialize (H0 (invPoss i x1 m)).
    eassert _.
    {
      apply H0.
      set_ext y. unfold invPoss.
      split; intros; psimpl.
      {
        destruct x0, y. cbn in *.
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
        exists x1.
        split. easy.
        cbn. rewrite eqb_id.
        auto using differ_pointwise_trivial.
      }
    }
    {
      clear H0. psimpl.
      exists x0.
      split.
      { easy. }
      split.
      {
        apply H0.
        destruct H5.
        constructor.
        {
          eapply Inv_pres.
          exact unown_inv0.
          all: easy.
        }
        { now rewrite <- H3 at 1. }
      }
      {
        destruct H0. cbn in *.
        rewrite eqb_id in *.
        now constructor.
      }
    }
  }
  destruct m; cbn;
  unfold inc, get.
  {
    repeat (
      eapply lemVis;
      intros
    ).
    {
      eapply (lemCall
        (Q:=fun _ _ => LiftSPrec (InvOwned i))
        (S:=fun _ _ _ => LiftSPrec (InvOwned i))).
      {
        unfold Stable, stableRelt, sub, subRelt.
        unfold LiftSPrec, LiftSRelt. intros. psimpl.
        specialize (H0 x1 eq_refl). psimpl.
        exists x0. split. easy. now apply H0.
      }
      {
        unfold Stable, stablePost, stableRelt, sub, subRelt.
        unfold LiftSPrec, LiftSRelt. intros. psimpl.
        specialize (H0 x1 eq_refl). psimpl.
        exists x0. split. easy. now apply H0.
      }
      {
        commit.
        exists (eq x1).
        split.
        { repeat econstructor. }
        split.
        {
          intros. subst.
          repeat econstructor.
        }
        ddestruct H; cbn in *.
        2:{
          exfalso. destruct H3.
          destruct unown_inv0. psimpl.
          rewrite H3 in x2. ddestruct x2.
          unfold OwnsLock in loc_unown0.
        }
        2:{
          destruct H3, unown_inv0.
          psimpl. now rewrite H3 in x2.
        }
      }
    }
  }
}