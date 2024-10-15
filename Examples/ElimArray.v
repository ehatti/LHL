From LHL.Core Require Import
  ProgramRules
  LogicFacts
  SingConds
  Program
  VisPoss
  ProgramFacts
  Traces
  Tensor
  Logic
  Specs.

From LHL.Util Require Import
  TransUtil
  Tactics
  Util.

From LHL.Examples Require Import
  ExchangerSpec
  RandomSpec
  ArraySpec
  NameSpec.

From Coq Require Import
  Lists.List
  Logic.FunctionalExtensionality
  Logic.PropExtensionality.
Import ListNotations.

Definition E T A :=
  RandSig |+| ArraySig (ExchSig A) T.

Definition VE T A : Spec T (E T A) :=
  tensorSpec
    randSpec
    (arraySpec T (@exchSpec T A)).

Definition F A := ExchSig A.

Definition VF T A : Spec T (F A) :=
  exchSpec.

Definition exch {T A} (v : A) : Prog (E T A) (option A) :=
  k <- call (Random T);
  r <- call (At k (Exch v));
  ret r.

Definition elimArray T A : Impl (E T A) (F A) :=
  fun _ m => match m with
  | Exch v => exch v
  end.

Definition Prec T A := SPrec (VE T A) (VF T A).
Definition Relt T A := SRelt (VE T A) (VF T A).
Definition Post T A R := R -> SRelt (VE T A) (VF T A).

Notation exchSt s n := (RState (snd s) n).

Notation pendSet s n := (
  match exchSt s n with
  | ExchDef ps _ => ps
  end
).

Notation doneSet s n := (
  match exchSt s n with
  | ExchDef _ ds => ds
  end
).

Record PIdle {T F} {VF : Spec T F} (i : Name T) (x : Poss VF) := {
  call_idle : PCalls x i = CallIdle;
  ret_idle : PRets x i = RetIdle
}.

Record Ready {T A} (i : Name T)
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
:= {
  state_idle : PState x = ExchDef {} {};
  self_in_pend :
    forall n v,
      contains (i, v) (pendSet s n) ->
      doneSet s n <> {}
}.

Record Offered {T A} (i : Name T) (v : A) (n : nat)
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
:= {
  self_pends_lazy :
    forall m w,
      n <> m ->
      contains (i, w) (pendSet s m) ->
      doneSet s m <> {};
  self_pend_active :
    contains (i, v) (pendSet s n);
  self_done_empty :
    doneSet s n = {};
  self_idle : PState x = ExchDef {} {};
  self_waiting :
    forall j w, i <> j ->
      contains (j, w) (pendSet s n) ->
      Waiting j (Exch w) x;
}.

Record Accepted {T A} (i j : Name T) (v w : A) (n : nat)
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
:= {
  self_pends_ready :
    forall m w,
      n <> m ->
      contains (i, w) (pendSet s m) ->
      doneSet s m <> {};
  self_done_active :
    exchSt s n = ExchDef {j => w} {i => v}
}.

Notation IStep s i e t :=
  (InterStep (elimArray _ _) s (i, UEvent (Some e)) t).

Variant EATran {T A} : Name T -> Relt T A :=
| EARandCall s x t i n :
    IStep s i (CallEv (inl (Random n))) t ->
    EATran i s x t x
| EARandRet s x t i n k :
    IStep s i (RetEv (inl (Random n)) k) t ->
    EATran i s x t x
| EAOffer s x t i v n :
    forall (i_wait : Waiting i (Exch v) x),
    IStep s i (CallEv (inr (At n (Exch v)))) t ->
    EATran i s x t x
| EAAccept (s : InterState (F A) (VE T A)) x t y i j v w n :
    exchSt s n = ExchDef {i => v, j => w} {} ->
    IStep s i (RetEv (inr (At n (Exch v))) (Some w)) t ->
    VisPossSteps
      x
      [(i, CallEv (Exch v));
       (j, CallEv (Exch w));
       (i, RetEv (Exch v) (Some w));
       (j, RetEv (Exch w) (Some v))]
      y ->
    EATran i s x t y
| EAFinish (s : InterState (F A) (VE T A)) x t i j v w n :
    exchSt s n = ExchDef {j => w} {i => v} ->
    IStep s i (RetEv (inr (At n (Exch v))) (Some w)) t ->
    EATran i s x t x
| EARevoke s x t y i v n :
    IStep s i (RetEv (inr (At n (Exch v))) None) t ->
    VisPossSteps
      x
      [(i, CallEv (Exch v));
       (i, RetEv (Exch v) None)]
      y ->
    EATran i s x t y.

Definition Guar {T A} (i : Name T) : Relt T A :=
  EATran i.

Definition OtherTran {A T} (i : Name T) (R : Name T -> Relt T A) : Relt T A :=
  fun s x t y => exists j, i <> j /\ R j s x t y.

Definition Rely {T A} (i : Name T) : Relt T A :=
  SRTC (OtherTran i EATran).

Ltac begin_commit :=
  unfold Commit, LiftSPrec; intros.

Lemma eq_inj {A} {x y : A} :
  eq x = eq y -> x = y.
intros. now rewrite H.
Qed.

Ltac eq_inj H :=
  apply eq_inj in H; subst.

Ltac contr := unfold not at 1; intros.

Lemma specf {A B} {f g : A -> B} :
  f = g ->
  forall x,
  f x = g x.
intros. now rewrite H.
Qed.

Ltac specf H v := apply specf with (x:=v) in H.

Ltac simp_sets :=
  repeat match goal with
  | [ H : {?i => ?v} = {} |- _ ] =>
      now apply disj_cons in H
  | [ H : {} = {?i => ?v} |- _ ] =>
      symmetry in H;
      now apply disj_cons in H
  | [ H : insert ?x ?xs = insert ?y ?ys |- _ ] =>
      let H2 := fresh in
      let H3 := fresh in
      apply insert_cong in H;
      destruct H as [H2 H3];
      ddestruct H2
  | [ H : emp = emp |- _ ] =>
      clear H
  end.

Lemma done_ready_stable {T A} (i : Name T) (v : A) (w : option A) :
  forall s x t y,
  (Ready i s x /\ Done i (Exch v) w x) ->
  Rely i s x t y ->
  Ready i t y /\ Done i (Exch v) w y.
intros. induction H0. easy.
apply IHSRTC. clear IHSRTC H1.
psimpl. destruct H, H0, H.
rename x into j.
ddestruct H0.
{
  ddestruct H0. cbn in *.
  psimpl. ddestruct H2.
  split.
  {
    constructor. easy. intros.
    specf H6 n0. rewrite <- H6 at 1.
    apply (self_in_pend0 n0 v0).
    now rewrite H6.
  }
  { easy. }
}
{
  ddestruct H0. cbn in *.
  psimpl. ddestruct H2.
  split.
  {
    constructor. easy. intros.
    specf H6 n0. rewrite <- H6 at 1.
    apply (self_in_pend0 n0 v0).
    now rewrite H6.
  }
  { easy. }
}
{
  ddestruct H0. cbn in *. psimpl.
  ddestruct H2. cbn in *. ddestruct H3.
  {
    split.
    {
      constructor. easy. intros.
      assert (n0 <> n).
      {
        contr. subst.
        specf x n. rewrite eqb_id in x.
        rewrite <- x in H3 at 1.
        apply contains_invert in H3.
        destruct H3. now ddestruct H3.
        now apply contains_contr in H3.
      }
      specf x2 n0. specf x n0.
      rewrite eqb_nid in *; auto.
      rewrite <- x, x2 at 1.
      apply (self_in_pend0 n0 v1).
      now rewrite <- x2, x at 1.
    }
    { easy. }
  }
  {
    split.
    {
      constructor. easy. intros.
      assert (n0 <> n).
      {
        contr. subst.
        specf x0 n. rewrite eqb_id in x0.
        rewrite <- x0 in H8 at 1.
        apply contains_invert in H8.
        destruct H8. now ddestruct H8.
        apply contains_invert in H8.
        destruct H8. ddestruct H8.
        2: now apply contains_contr in H8.
        specf x2 n. rewrite eqb_id in x2.
        exfalso. apply (self_in_pend0 n x).
        rewrite <- x2. apply contains_triv.
        rewrite <- x2. easy.
      }
      specf x2 n0. specf x0 n0.
      rewrite eqb_nid in *; auto.
      rewrite <- x0, x2 at 1.
      apply (self_in_pend0 n0 v1).
      now rewrite <- x2, x0 at 1.
    }
    { easy. }
  }
}
{
  ddestruct H2. cbn in *. psimpl.
  ddestruct H3. cbn in *. ddestruct H4.
  2:{
    specf x2 n. rewrite eqb_id in x2.
    rewrite H0 in x2. ddestruct x2.
    simp_sets.
  }
  assert (j0 = j /\ y0 = w0).
  {
    specf x2 n. rewrite eqb_id in x2.
    rewrite H0 in x2. ddestruct x2.
    now simp_sets.
  }
  psimpl.
  split.
  {
    constructor.
    {
      destruct_big_steps.
      ddestruct H9.
      2:{
        rewrite state_idle0 in x4.
        ddestruct x4. simp_sets.
      }
      ddestruct H16.
      {
        rewrite <- x5 in x4.
        ddestruct x4. simp_sets.
      }
      ddestruct H23.
      2:{
        rewrite <- x8 in x9.
        ddestruct x9. simp_sets.
      }
      ddestruct H30.
      {
        rewrite <- x10 in x9.
        ddestruct x9. simp_sets.
      }
      easy.
    }
    intros.
    assert (n0 <> n).
    {
      contr. subst.
      specf x n. rewrite eqb_id in x. 
      rewrite <- x in H10 at 1.
      apply contains_invert in H10.
      destruct H10. now ddestruct H10.
      now apply contains_contr in H10.
    }
    specf x2 n0. specf x n0.
    rewrite eqb_nid in *; auto.
    rewrite <- x, x2 at 1.
    apply (self_in_pend0 n0 v1).
    now rewrite <- x2, x at 1.
  }
  {
    assert (i <> j).
    {
      contr. subst.
      destruct H1. destruct_big_steps.
      rewrite <- H13 in call_done; auto.
      now rewrite call_done in H16.
    }
    destruct_big_steps. destruct H1.
    constructor.
    { now rewrite H35, H28, H21, H14. }
    { now rewrite H36, H29, H22, H15. }
  }
}
{
  ddestruct H2. cbn in *. psimpl.
  ddestruct H3. cbn in *. ddestruct H4.
  2:{
    split.
    {
      constructor. easy. intros.
      assert (n0 <> n).
      {
        contr. subst.
        specf x0 n. rewrite eqb_id in x0.
        rewrite <- x0 in H9 at 1.
        now apply contains_contr in H9.
      }
      specf x2 n0. specf x0 n0.
      rewrite eqb_nid in *; auto.
      rewrite <- x0, x2 at 1.
      apply (self_in_pend0 n0 v1).
      now rewrite <- x2, x0 at 1.
    }
    { easy. }
  }
  {
    specf x2 n. rewrite eqb_id in x2.
    rewrite H0 in x2. ddestruct x2.
    simp_sets.
  }
}
{
  ddestruct H0. cbn in *. psimpl.
  ddestruct H2. cbn in *. ddestruct H3.
  split.
  {
    constructor.
    {
      destruct_big_steps.
      now ddestruct H14.
    }
    intros.
    assert (n0 <> n).
    {
      contr. subst.
      specf x n. rewrite eqb_id in x.
      rewrite <- x in H3 at 1.
      now apply contains_contr in H3.
    }
    specf x2 n0. specf x n0.
    rewrite eqb_nid in *; auto.
    rewrite <- x, x2 at 1.
    apply (self_in_pend0 n0 v1).
    now rewrite <- x2, x at 1.
  }
  {
    destruct_big_steps.
    destruct H1.
    constructor.
    { now rewrite H19, H12. }
    { now rewrite H20, H13. }
  }
}
Qed.

Lemma wait_ready_stable {T A} (i : Name T) (v : A) :
  forall s x t y,
  (Ready i s x /\ Waiting i (Exch v) x) ->
  Rely i s x t y ->
  Ready i t y /\ Waiting i (Exch v) y.
intros. induction H0. easy.
apply IHSRTC. clear IHSRTC H1.
psimpl. destruct H, H0, H.
rename x into j.
ddestruct H0.
{
  ddestruct H0. cbn in *.
  psimpl. split.
  {
    constructor. easy. intros. specf H6 n0.
    rewrite <- H6 at 1.
    eapply self_in_pend0.
    rewrite H6 at 1.
    exact H7.
  }
  { easy. }
}
{
  ddestruct H0. cbn in *.
  psimpl. split.
  {
    constructor. easy. intros. specf H6 n0.
    rewrite <- H6 at 1.
    eapply self_in_pend0.
    rewrite H6 at 1.
    exact H7.
  }
  { easy. }
}
{
  ddestruct H0. cbn in *. psimpl.
  ddestruct H2. cbn in *. ddestruct H3.
  {
    split.
    {
      constructor. easy. intros.
      assert (n <> n0).
      {
        contr. subst.
        specf x n0. rewrite eqb_id in x.
        rewrite <- x in H3 at 1.
        apply contains_invert in H3.
        destruct H3. now ddestruct H3.
        now apply contains_contr in H3.
      }
      specf x2 n0. specf x n0.
      rewrite eqb_nid in *; auto.
      rewrite <- x, x2 at 1.
      eapply self_in_pend0.
      rewrite <- x2, x at 1.
      exact H3.
    }
    { easy. }
  }
  {
    split.
    {
      assert (i <> i1).
      {
        contr. subst. specf x2 n.
        rewrite eqb_id in x2.
        eapply (self_in_pend0 n).
        {
          rewrite <- x2 at 1.
          apply contains_triv.
        }
        { now rewrite <- x2 at 1. }
      }
      constructor. easy. intros.
      assert (n <> n0).
      {
        contr. subst.
        specf x0 n0. rewrite eqb_id in x0.
        rewrite <- x0 in H9 at 1.
        apply contains_invert in H9.
        destruct H9. now ddestruct H9.
        apply contains_invert in H9.
        destruct H9. now ddestruct H9.
        now apply contains_contr in H9.
      }
      specf x2 n0. specf x0 n0.
      rewrite eqb_nid in *; auto.
      rewrite <- x0, x2 at 1.
      eapply self_in_pend0.
      rewrite <- x2, x0 at 1.
      exact H9.
    }
    { easy. }
  }
}
{
  rename i0 into k, v0 into u.
  assert (i <> j).
  {
    unfold not. intro. subst.
    specialize (self_in_pend0 n w).
    rewrite H0 in self_in_pend0.
    exfalso. apply self_in_pend0.
    {
      rewrite insert_perm.
      apply contains_triv.
    }
    { easy. }
  }
  split.
  {
    ddestruct H2. cbn in *. psimpl.
    ddestruct H3. cbn in *. ddestruct H4.
    2:{
      specf x2 n. rewrite eqb_id in x2.
      rewrite H0 in x2. ddestruct x2.
      simp_sets.
    }
    rename y0 into o, j0 into l.
    assert (i <> l).
    {
      contr. subst.
      specf x2 n. rewrite eqb_id in x2.
      specialize (self_in_pend0 n o).
      rewrite <- x2 in self_in_pend0.
      apply self_in_pend0.
      {
        rewrite insert_perm.
        apply contains_triv.
      }
      { easy. }
    }
    constructor.
    {
      destruct_big_steps.
      rewrite state_idle0 in H5.
      ddestruct H5. 2: simp_sets.
      rewrite <- x in H16.
      ddestruct H16. simp_sets.
      rewrite <- x in H23.
      ddestruct H23. 2: simp_sets.
      rewrite <- x in H30.
      ddestruct H30. simp_sets.
      easy.
    }
    intros.
    assert (x2' := x2).
    specf x2' n. rewrite eqb_id in x2'.
    rewrite H0 in x2'. ddestruct x2'.
    simp_sets.
    dec_eq_nats n n0.
    {
      specf x0 n0. rewrite eqb_id in x0.
      rewrite <- x0 at 1. apply disj_cons.
    }
    {
      specf x2 n0. specf x0 n0.
      rewrite eqb_nid in *; auto.
      rewrite <- x0, x2 at 1.
      eapply self_in_pend0.
      rewrite <- x2, x0 at 1.
      exact H12.
    }
  }
  {
    destruct_big_steps.
    destruct H1.
    constructor;
    rewrite
      ?H29, ?H30, ?H22, ?H23,
      ?H15, ?H16, ?H8, ?H9.
    all: easy.
  }
}
{
  ddestruct H2. cbn in *. psimpl.
  ddestruct H3. cbn in *. ddestruct H4.
  {
    specf x2 n. rewrite eqb_id in x2.
    rewrite H0 in x2. ddestruct x2.
    simp_sets.
  }
  assert (x2' := x2).
  specf x2' n. rewrite eqb_id in x2'.
  rewrite H0 in x2'. ddestruct x2'.
  simp_sets. split.
  {
    constructor. easy. intros.
    assert (n <> n0).
    {
      contr. subst. specf x0 n0.
      rewrite eqb_id in x0.
      rewrite <- x0 in H9 at 1.
      now apply contains_contr in H9.
    }
    specf x2 n0. specf x0 n0.
    rewrite eqb_nid in *; auto.
    rewrite <- x0, x2 at 1.
    eapply self_in_pend0.
    rewrite <- x2, x0 at 1.
    exact H9.
  }
  { easy. }
}
{
  split.
  {
    constructor.
    {
      destruct_big_steps.
      now ddestruct H9.
    }
    intros.
    ddestruct H0. cbn in *. psimpl.
    ddestruct H2. cbn in *. ddestruct H3.
    assert (n <> n0).
    {
      contr. subst.
      specf x n0. rewrite eqb_id in x.
      rewrite <- x in H9.
      now apply contains_contr in H9.
    }
    specf x2 n0. specf x n0.
    rewrite eqb_nid in *; auto.
    rewrite <- x, x2 at 1.
    eapply self_in_pend0.
    rewrite <- x2, x at 1.
    exact H9.
  }
  {
    destruct_big_steps.
    destruct H1.
    constructor;
    now rewrite ?H14, ?H15, ?H7, ?H8.
  }
}
Qed.

Variant AfterOffer {T A} (i : Name T) (v : A) : Prec T A :=
| AOOffered n s x :
    Offered i v n s x ->
    Waiting i (Exch v) x ->
    AfterOffer i v s x
| AOAccepted n j w s x :
    Accepted i j v w n s x ->
    Done i (Exch v) (Some w) x ->
    AfterOffer i v s x.

Lemma after_offer_stable {T A} (i : Name T) (v : A) :
  forall s x t y,
  AfterOffer i v s x ->
  Rely i s x t y ->
  AfterOffer i v t y.
intros. induction H0. easy.
apply IHSRTC. clear IHSRTC H1.
destruct H0, H0. rename x into j.
ddestruct H.
{
  destruct H, H0.
  ddestruct H2.
  {
    ddestruct H. cbn in *.
    psimpl. ddestruct H0.
    apply AOOffered
      with (n:=n).
    {
      constructor. intros.
      specf H5 m0. rewrite <- H5 at 1.
      eapply self_pends_lazy0. easy.
      rewrite H5 at 1. exact H6.
      specf H5 n. now rewrite <- H5 at 1.
      specf H5 n. now rewrite <- H5 at 1.
      easy.
      {
        intros. specf H5 n.
        eapply self_waiting0. easy.
        now rewrite H5.
      }
      {
        admit.
      }
    }
    { constructor; easy. }
  }
  {
    ddestruct H. cbn in *.
    psimpl. ddestruct H0.
    apply AOOffered
      with (n:=n).
    {
      constructor. intros.
      specf H5 m0. rewrite <- H5 at 1.
      eapply self_pends_lazy0. easy.
      rewrite H5 at 1. exact H7.
      specf H5 n. now rewrite <- H5 at 1.
      specf H5 n. now rewrite <- H5 at 1.
      easy.
      {
        intros. specf H5 n.
        eapply self_waiting0. easy.
        now rewrite H5.
      }
      {
        admit.
      }
    }
    { constructor; easy. }
  }
  {
    ddestruct H. cbn in *. psimpl.
    ddestruct H0. cbn in *. ddestruct H2.
    {
      apply AOOffered
        with (n:=n).
      {
        constructor.
        {
          intros.
          assert (n0 <> m).
          {
            contr. subst.
            specf x m. rewrite eqb_id in x.
            rewrite <- x in H7 at 1.
            apply contains_invert in H7.
            destruct H7. now ddestruct H7.
            now apply contains_contr in H7.
          }
          specf x2 m. specf x m.
          rewrite eqb_nid in *; auto.
          rewrite <- x, x2 at 1.
          eapply self_pends_lazy0. easy.
          rewrite <- x2, x at 1.
          exact H7.
        }
        {
          assert (n0 <> n).
          {
            contr. subst.
            specf x2 n. rewrite eqb_id in x2.
            rewrite <- x2 in self_pend_active0.
            now apply contains_contr in self_pend_active0.
          }
          specf x2 n. specf x n.
          rewrite eqb_nid in *; auto.
          rewrite <- x, x2 at 1. easy.
        }
        {
          assert (n0 <> n).
          {
            contr. subst.
            specf x2 n. rewrite eqb_id in x2.
            rewrite <- x2 in self_pend_active0.
            now apply contains_contr in self_pend_active0.
          }
          specf x2 n. specf x n.
          rewrite eqb_nid in *; auto.
          rewrite <- x, x2 at 1. easy.
        }
        easy.
        {
          intros.
          eapply self_waiting0. easy.
          assert (n0 <> n).
          {
            contr. subst.
            specf x2 n. rewrite eqb_id in x2.
            rewrite <- x2 in self_pend_active0.
            now apply contains_contr in self_pend_active0.
          }
          specf x2 n. specf x n.
          rewrite eqb_nid in *; auto.
          now rewrite <- x2, x at 1.
        }
        {
          admit.
        }
      }
      { constructor; easy. }
    }
    {
      apply AOOffered
        with (n:=n).
      {
        constructor.
        {
          intros.
          assert (n0 <> m).
          {
            contr. subst.
            specf x0 m. rewrite eqb_id in x0.
            rewrite <- x0 in H8 at 1.
            apply contains_invert in H8.
            destruct H8. now ddestruct H8.
            apply contains_invert in H8.
            destruct H8. ddestruct H8.
            2: now apply contains_contr in H8.
            apply (self_pends_lazy0 m x). easy.
            {
              specf x2 m. rewrite eqb_id in x2.
              rewrite <- x2. apply contains_triv.
            }
            {
              specf x2 m. rewrite eqb_id in x2.
              rewrite <- x2. easy.
            }
          }
          specf x2 m. specf x0 m.
          rewrite eqb_nid in *; auto.
          rewrite <- x0, x2 at 1.
          eapply self_pends_lazy0. easy.
          rewrite <- x2, x0 at 1.
          exact H8.
        }
        {
          dec_eq_nats n n0.
          {
            specf x2 n0. rewrite eqb_id in x2.
            rewrite <- x2 in self_pend_active0.
            apply contains_invert in self_pend_active0.
            destruct self_pend_active0. ddestruct H7.
            2: now apply contains_contr in H7.
            specf x0 n0. rewrite eqb_id in x0.
            rewrite <- x0, insert_perm at 1.
            apply contains_triv.
          }
          {
            specf x2 n. specf x0 n.
            rewrite eqb_nid in *; auto.
            now rewrite <- x0, x2 at 1.
          }
        }
        {
          dec_eq_nats n n0.
          {
            specf x2 n0. rewrite eqb_id in x2.
            rewrite <- x2 in self_pend_active0.
            apply contains_invert in self_pend_active0.
            destruct self_pend_active0. ddestruct H7.
            2: now apply contains_contr in H7.
            specf x0 n0. rewrite eqb_id in x0.
            rewrite <- x0 at 1. easy.
          }
          {
            specf x2 n. specf x0 n.
            rewrite eqb_nid in *; auto.
            now rewrite <- x0, x2 at 1.
          }
        }
        easy.
        {
          intros.
          dec_eq_nats n0 n.
          {
            specf x2 n. rewrite eqb_id in x2.
            move self_pend_active0 after x2.
            rewrite <- x2 in self_pend_active0.
            apply contains_invert in self_pend_active0.
            destruct self_pend_active0. ddestruct H9.
            2: now apply contains_contr in H9.
            rename j into k, i1 into j, i0 into i.
            assert (i = k /\ v0 = w).
            {
              specf x0 n. rewrite eqb_id in x0.
              rewrite <- x0 in H8 at 1.
              apply contains_invert in H8.
              destruct H8. now ddestruct H8.
              apply contains_invert in H8.
              destruct H8. now ddestruct H8.
              now apply contains_contr in H8.
            }
            now psimpl.
          }
          {
            specf x2 n. specf x0 n.
            rewrite eqb_nid in *; auto.
            apply self_waiting0. easy.
            rewrite <- x2, x0 at 1.
            easy.
          }
        }
        {
          admit.
        }
      }
      { constructor; easy. }
    }
  }
  {
    ddestruct H0. cbn in *. psimpl.
    ddestruct H2. cbn in *. ddestruct H3.
    2:{
      specf x2 n0. rewrite eqb_id in x2.
      rewrite H in x2. ddestruct x2.
      simp_sets.
    }
    assert (j0 = j /\ y0 = w).
    {
      specf x2 n0. rewrite eqb_id in x2.
      rewrite H in x2. ddestruct x2.
      now simp_sets.
    }
    psimpl.
    dec_eq_nats n0 n.
    {
      assert (x2' := x2).
      specf x2 n. rewrite eqb_id in x2.
      rewrite <- x2 in self_pend_active0.
      apply contains_invert in self_pend_active0.
      destruct self_pend_active0. now ddestruct H9.
      apply contains_invert in H9.
      destruct H9. ddestruct H9.
      2: now apply contains_contr in H9.
      rename i0 into i, v0 into v.
      apply AOAccepted
        with (n:=n) (i:=j) (j:=i) (v:=w) (w:=v).
      {
        constructor.
        {
          intros.
          specf x2' m. specf x m.
          rewrite eqb_nid in *; auto.
          rewrite <- x, x2' at 1.
          apply (self_pends_lazy0 m w0). easy.
          rewrite <- x2', x at 1. easy.
        }
        { specf x n. now rewrite eqb_id in x. }
      }
      {
        destruct_big_steps.
        constructor; easy.
      }
    }
    {
      apply AOOffered
        with (n:=n).
      {
        constructor. intros.
        assert (n0 <> m).
        {
          contr. subst.
          specf x m. rewrite eqb_id in x.
          rewrite <- x in H11 at 1.
          apply contains_invert in H11.
          destruct H11. now ddestruct H11.
          now apply contains_contr in H11.
        }
        specf x2 m. specf x m.
        rewrite eqb_nid in *; auto.
        rewrite <- x, x2 at 1.
        apply (self_pends_lazy0 m w0). easy.
        { now rewrite <- x2, x at 1. }
        {
          specf x2 n. specf x n.
          rewrite eqb_nid in *; auto.
          now rewrite <- x, x2 at 1.
        }
        {
          specf x2 n. specf x n.
          rewrite eqb_nid in *; auto.
          now rewrite <- x, x2 at 1.
        }
        {
          destruct_big_steps.
          clear - self_idle0 H8 H15 H22 H29.
          rewrite self_idle0 in H8.
          ddestruct H8. 2: simp_sets.
          rewrite <- x in H15.
          ddestruct H15. simp_sets.
          rewrite <- x in H22.
          ddestruct H22. 2: simp_sets.
          rewrite <- x in H29.
          ddestruct H29. simp_sets.
          easy.
        }
        {
          admit.
        }
        {
          admit.
        }
      }
      {
        assert (i <> j).
        {
          contr. subst.
          apply (self_pends_lazy0 n0 w). easy.
          {
            rewrite H, insert_perm.
            apply contains_triv.
          }
          {
            specf x2 n0. rewrite eqb_id in x2.
            rewrite <- x2. easy.
          }
        }
        clear - H1 H10 H8 call_waiting ret_waiting.
        destruct_big_steps.
        constructor.
        { now rewrite H26, H19, H12, H5. }
        { now rewrite H27, H20, H13, H6. }
      }
    }
  }
  {
    ddestruct H0. cbn in *. psimpl.
    ddestruct H2. cbn in *. ddestruct H3.
    {
      specf x2 n0. rewrite eqb_id in x2.
      rewrite H in x2. ddestruct x2.
      simp_sets.
    }
    assert (i1 = j /\ x = w).
    {
      specf x2 n0. rewrite eqb_id in x2.
      rewrite H in x2. ddestruct x2.
      now simp_sets.
    }
    psimpl.
    assert (n <> n0).
    {
      contr. subst.
      rewrite H in self_done_empty0.
      simp_sets.
    }
    apply AOOffered
      with (n:=n).
    {
      constructor. intros.
      assert (n0 <> m).
      {
        contr. subst.
        specf x0 m. rewrite eqb_id in x0.
        rewrite <- x0 in H10 at 1.
        now apply contains_contr in H10.
      }
      specf x2 m. specf x0 m.
      rewrite eqb_nid in *; auto.
      rewrite <- x0, x2 at 1.
      apply (self_pends_lazy0 m w0). easy.
      { now rewrite <- x2, x0 at 1. }
      {
        specf x2 n. specf x0 n.
        rewrite eqb_nid in *; auto.
        now rewrite <- x0, x2 at 1.
      }{
        specf x2 n. specf x0 n.
        rewrite eqb_nid in *; auto.
        now rewrite <- x0, x2 at 1.
      }
      easy.
    }
    { constructor; easy. }
  }
  {
    ddestruct H. cbn in *. psimpl.
    ddestruct H0. cbn in *. ddestruct H2.
    apply AOOffered
      with (n:=n).
    {
      constructor.
      {
        intros.
        assert (n0 <> m).
        {
          contr. subst.
          specf x m. rewrite eqb_id in x.
          rewrite <- x in H8 at 1.
          now apply contains_contr in H8.
        }
        specf x2 m. specf x m.
        rewrite eqb_nid in *; auto.
        rewrite <- x, x2 at 1.
        apply (self_pends_lazy0 m w). easy.
        { now rewrite <- x2, x at 1. }
      }
      {
        assert (n0 <> n).
        {
          contr. subst.
          specf x2 n. rewrite eqb_id in x2.
          rewrite <- x2 in self_pend_active0.
          apply contains_invert in self_pend_active0.
          destruct self_pend_active0. now ddestruct H2.
          now apply contains_contr in H2.
        }
        specf x2 n. specf x n.
        rewrite eqb_nid in *; auto.
        now rewrite <- x, x2 at 1.
      }
      {
        assert (n0 <> n).
        {
          contr. subst.
          specf x2 n. rewrite eqb_id in x2.
          rewrite <- x2 in self_pend_active0.
          apply contains_invert in self_pend_active0.
          destruct self_pend_active0. now ddestruct H2.
          now apply contains_contr in H2.
        }
        specf x2 n. specf x n.
        rewrite eqb_nid in *; auto.
        now rewrite <- x, x2 at 1.
      }
      {
        destruct_big_steps.
        clear - self_idle0 H2 H13.
        rewrite self_idle0 in H2.
        ddestruct H2. 2: simp_sets.
        rewrite <- x in H13.
        now ddestruct H13.
      }
    }
    {
      destruct_big_steps.
      constructor.
      { now rewrite H18, H11. }
      { now rewrite H19, H12. }
    }
  }
}
{
  destruct H. ddestruct H2.
  {
    ddestruct H. cbn in *.
    psimpl. ddestruct H2.
    eapply AOAccepted with
      (j:=j) (w:=w) (n:=n).
    {
      constructor.
      {
        intros.
        specf H6 m0. rewrite <- H6 at 1.
        eapply self_pends_ready0. easy.
        rewrite H6. exact H7.
      }
      {
        specf H6 n.
        now rewrite <- H6 at 1.
      }
    }
    { easy. }
  }
  {
    ddestruct H. cbn in *.
    psimpl. ddestruct H2.
    apply AOAccepted with
      (j:=j) (w:=w) (n:=n).
    {
      constructor.
      {
        intros.
        specf H6 m0. rewrite <- H6 at 1.
        eapply self_pends_ready0. easy.
        rewrite H6. exact H8.
      }
      {
        specf H6 n.
        now rewrite <- H6 at 1.
      }
    }
    { easy. }
  }
  {
    ddestruct H. cbn in *. psimpl.
    ddestruct H2. cbn in *. ddestruct H3.
    {
      assert (n <> n0).
      {
        contr. subst.
        specf x2 n0. rewrite eqb_id in x2.
        rewrite self_done_active0 in x2.
        ddestruct x2. simp_sets.
      }
      apply AOAccepted with
        (j:=j) (w:=w) (n:=n).
      {
        constructor.
        {
          intros.
          assert (n0 <> m).
          {
            contr. subst.
            specf x m. rewrite eqb_id in x.
            rewrite <- x in H9 at 1.
            apply contains_invert in H9.
            destruct H9. now ddestruct H9.
            now apply contains_contr in H9.
          }
          specf x2 m. specf x m.
          rewrite eqb_nid in *; auto.
          rewrite <- x, x2 at 1.
          eapply self_pends_ready0. easy.
          rewrite <- x2, x at 1.
          exact H9.
        }
        {
          specf x2 n. specf x n.
          rewrite eqb_nid in *; auto.
          now rewrite <- x, x2 at 1.
        }
      }
      { easy. }
    }
    {
      assert (n <> n0).
      {
        contr. subst.
        specf x2 n0. rewrite eqb_id in x2.
        rewrite self_done_active0 in x2.
        ddestruct x2. simp_sets.
      }
      apply AOAccepted with
        (j:=j) (w:=w) (n:=n).
      {
        constructor.
        {
          intros.
          assert (n0 <> m).
          {
            contr. subst.
            specf x0 m. rewrite eqb_id in x0.
            rewrite <- x0 in H10 at 1.
            apply contains_invert in H10.
            destruct H10. now ddestruct H10.
            apply contains_invert in H10.
            destruct H10. ddestruct H10.
            2: now apply contains_contr in H10.
            apply (self_pends_ready0 m x). easy.
            {
              specf x2 m. rewrite eqb_id in x2.
              rewrite <- x2. apply contains_triv.
            }
            {
              specf x2 m. rewrite eqb_id in x2.
              rewrite <- x2. easy.
            }
          }
          specf x2 m. specf x0 m.
          rewrite eqb_nid in *; auto.
          rewrite <- x0, x2 at 1.
          eapply self_pends_ready0. easy.
          rewrite <- x2, x0 at 1.
          exact H10.
        }
        {
          specf x2 n. specf x0 n.
          rewrite eqb_nid in *; auto.
          now rewrite <- x0, x2 at 1.
        }
      }
      { easy. }
    }
  }
  {
    assert (n <> n0).
    {
      contr. subst.
      rewrite self_done_active0 in H.
      ddestruct H. simp_sets.
    }
    ddestruct H2. cbn in *. psimpl.
    ddestruct H3. cbn in *. ddestruct H4.
    {
      apply AOAccepted with
        (n:=n) (j:=j) (w:=w).
      {
        constructor.
        {
          intros.
          assert (n0 <> m).
          {
            contr. subst.
            specf x m. rewrite eqb_id in x.
            rewrite <- x in H12 at 1.
            apply contains_invert in H12.
            destruct H12. now ddestruct H12.
            now apply contains_contr in H12.
          }
          specf x2 m. specf x m.
          rewrite eqb_nid in *; auto.
          rewrite <- x, x2 at 1.
          apply (self_pends_ready0 m w1). easy.
          { now rewrite <- x2, x at 1. }
        }
        {
          specf x2 n. specf x n.
          rewrite eqb_nid in *; auto.
          now rewrite <- x, x2 at 1.
        }
      }
      {
        assert (i <> j0).
        {
          contr. subst.
          destruct H0. destruct_big_steps.
          rewrite H13 in H16; try easy.
          now rewrite call_done in H16.
        }
        destruct H0.
        destruct_big_steps.
        constructor.
        { now rewrite H34, H27, H20, H13. }
        { now rewrite H35, H28, H21, H14. }
      }
    }
    {
      specf x2 n0. rewrite eqb_id in x2.
      rewrite H in x2. ddestruct x2.
      simp_sets.
    }
  }
  {
    assert (n0 <> n).
    {
      contr. subst.
      rewrite self_done_active0 in H.
      ddestruct H. now simp_sets.
    }
    ddestruct H2. cbn in *. psimpl.
    ddestruct H3. cbn in *. ddestruct H4.
    {
      specf x2 n0. rewrite eqb_id in x2.
      rewrite H in x2. ddestruct x2.
      simp_sets.
    }
    {
      eapply AOAccepted
        with (n:=n) (j:=j) (w:=w).
      {
        constructor.
        {
          intros.
          assert (n0 <> m).
          {
            contr. subst.
            specf x0 m. rewrite eqb_id in x0.
            rewrite <- x0 in H11 at 1.
            now apply contains_contr in H11.
          }
          specf x2 m. specf x0 m.
          rewrite eqb_nid in *; auto.
          rewrite <- x0, x2 at 1.
          apply (self_pends_ready0 m w1). easy.
          { now rewrite <- x2, x0. }
        }
        {
          specf x2 n. specf x0 n.
          rewrite eqb_nid in *; auto.
          now rewrite <- x0, x2 at 1.
        }
      }
      { easy. }
    }
  }
  {
    ddestruct H. cbn in *. psimpl.
    ddestruct H2. cbn in *. ddestruct H3.
    assert (n0 <> n).
    {
      contr. subst.
      specf x2 n. rewrite eqb_id in x2.
      rewrite self_done_active0 in x2.
      ddestruct x2. simp_sets.
    }
    eapply AOAccepted
      with (n:=n) (j:=j) (w:=w).
    {
      constructor.
      {
        intros.
        assert (n0 <> m).
        {
          contr. subst.
          specf x m. rewrite eqb_id in x.
          rewrite <- x in H10 at 1.
          now apply contains_contr in H10.
        }
        specf x2 m. specf x m.
        rewrite eqb_nid in *; auto.
        rewrite <- x, x2 at 1.
        apply (self_pends_ready0 m w0). easy.
        now rewrite <- x2, x at 1.
      }
      {
        specf x2 n. specf x n.
        rewrite eqb_nid in *; auto.
        now rewrite <- x, x2 at 1.
      }
    }
    {
      destruct H0.
      destruct_big_steps.
      constructor.
      { now rewrite H18, H11. }
      { now rewrite H19, H12. }
    }
  }
}
Qed.

Lemma conj_assoc {A B C : Prop} :
  (A /\ B /\ C) = ((A /\ B) /\ C).
now apply propositional_extensionality.
Qed.

Lemma exch_correct {T A} {i : Name T} {v : A} :
  VerifyProg i (LiftSRelt (Rely i)) (LiftSRelt (Guar i))
    (prComp (LiftSPrec (Ready i)) (TInvoke (elimArray T A) i _ (Exch v)) ->>
     LiftSRelt (Rely i))
    (exch v)
    (fun r _ _ => LiftSPrec (fun s x =>
      Ready i s x /\
      Done i (Exch v) r x)).
eapply weakenPrec with
  (P:=fun _ _ => LiftSPrec (fun s x =>
    Ready i s x /\
    Waiting i (Exch v) x)).
2:{
  unfold sub, subRelt, LiftSPrec, LiftSRelt.
  intros. psimpl. unfold TInvoke in H1.
  psimpl.
  eassert _.
  {
    eapply H0 with (x:= invPoss i x1 (Exch v)).
    unfold invPoss. set_ext y. split; intros; psimpl.
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
  psimpl. clear H0.
  exists x0. split. easy.
  eapply wait_ready_stable.
  2: exact H5. split.
  {
    constructor.
    { now destruct H2. }
    destruct H2.
    now setoid_rewrite <- H3.
  }
  {
    constructor; cbn;
    now rewrite eqb_id.
  }
}
unfold exch.
eapply lemBind.
{
  eapply (lemCall
    (Q:=fun _ _ => LiftSPrec (fun s x =>
      Ready i s x /\
      Waiting i (Exch v) x))
    (S:=fun r _ _ => LiftSPrec (fun s x =>
      Ready i s x /\
      Waiting i (Exch v) x /\
      r < T))).
  {
    unfold Stable, stableRelt, sub, subRelt.
    unfold LiftSPrec, LiftSRelt. intros. psimpl.
    specialize (H0 x1 eq_refl). psimpl.
    exists x0. split. easy.
    eapply wait_ready_stable.
    split. exact H1. easy.
    easy.
  }
  {
    unfold Stable, stablePost, stableRelt, sub, subRelt.
    unfold LiftSPrec, LiftSRelt. intros. psimpl.
    specialize (H0 x1 eq_refl). psimpl.
    exists x0. split. easy.
    rewrite conj_assoc.
    split. 2: easy.
    eapply wait_ready_stable.
    split. exact H1. easy.
    easy.
  }
  {
    begin_commit.
    cbn in *. psimpl.
    ddestruct H2.
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
      exists x1. split. easy.
      split.
      {
        destruct H7. constructor. easy.
        intros.
        apply equal_f with (x:=n) in H6.
        rewrite <- H6 at 1.
        eapply self_in_pend0.
        rewrite H6 at 1.
        exact H.
      }
      { easy. }
    }
    {
      exists x1. split. easy.
      eq_inj H. eapply EARandCall
        with (n:=T).
      constructor; cbn.
      {
        constructor; cbn. easy.
        intros. now rewrite H0.
      }
      {
        rewrite <- x2, <- x at 1.
        repeat (easy || constructor).
      }
    }
  }
  intros.
  {
    begin_commit.
    cbn in *. psimpl.
    ddestruct H2.
    exists (eq x3).
    split.
    { repeat econstructor. }
    split.
    {
      intros. subst.
      repeat econstructor.
    }
    split.
    {
      exists x3. split. easy.
      rewrite conj_assoc.
      split. 2: easy.
      split.
      {
        destruct H8. constructor. easy. intros.
        apply equal_f with (x:=n) in H6.
        rewrite <- H6 at 1.
        eapply self_in_pend0.
        rewrite H6 at 1.
        exact H2.
      }
      { easy. }
    }
    {
      exists x3. split. easy.
      eq_inj H2. eapply EARandRet
        with (n:=T) (k:=v0).
      constructor; cbn.
      {
        constructor; cbn. easy.
        intros. now rewrite H0.
      }
      {
        rewrite <- x5, <- x at 1.
        repeat (easy || constructor).
      }
    }
  }
}
intros.
eapply lemBind.
{
  eapply (lemCall
    (Q:=fun _ _ => LiftSPrec (AfterOffer i v))
    (S:=fun w _ _ => LiftSPrec (fun s x =>
      Ready i s x /\
      Done i (Exch v) w x))).
  {
    unfold Stable, stableRelt, sub, subRelt.
    unfold LiftSPrec, LiftSRelt. intros. psimpl.
    specialize (H0 x1 eq_refl). psimpl.
    exists x0. split. easy.
    eapply after_offer_stable.
    exact H1. easy.
  }
  {
    unfold Stable, stablePost, stableRelt, sub, subRelt.
    unfold LiftSPrec, LiftSRelt. intros. psimpl.
    specialize (H0 x1 eq_refl). psimpl.
    exists x0. split. easy.
    eapply done_ready_stable.
    split. exact H1. easy.
    easy.
  }
  {
    unfold LiftSPrec, LiftSRelt.
    begin_commit. do 2 psimpl.
    ddestruct H. cbn in *.
    ddestruct H2.
    {
      exists (eq x5).
      split.
      { repeat econstructor. }
      split.
      {
        intros. subst.
        repeat econstructor.
      }
      split.
      {
        exists x5. split. easy.
        eapply AOOffered with (n:=v0).
        {
          constructor.
          {
            intros.
            specf x8 m. specf x m.
            rewrite eqb_nid in *; auto.
            destruct H5.
            rewrite <- x, x8 in H14 at 1.
            apply self_in_pend0 in H14.
            now rewrite <- x, x8 at 1.
          }
          {
            specf x v0. rewrite eqb_id in x.
            rewrite <- x at 1. apply contains_triv.
          }
          {
            specf x v0. rewrite eqb_id in x.
            rewrite <- x at 1. easy.
          }
          now destruct H5.
        }
        { easy. }
      }
      {
        intros. eq_inj H2.
        exists x2. split. easy.
        eapply EAOffer with
          (n:=v0) (v:=v).
        constructor.
        {
          constructor; cbn. easy.
          intros. now rewrite H0.
        }
        {
          cbn. rewrite <- x8, <- x at 1.
          repeat (easy || constructor).
        }
      }
    }
    {
      exists (eq x5).
      split.
      { repeat econstructor. }
      split.
      {
        intros. subst.
        repeat econstructor.
      }
      split.
      {
        exists x5. split. easy.
        eapply AOOffered with (n:=v0).
        {
          constructor.
          {
            intros.
            specf x8 m. specf x2 m.
            rewrite eqb_nid in *; auto.
            destruct H5.
            rewrite <- x2, x8 in H15 at 1.
            apply self_in_pend0 in H15.
            now rewrite <- x2, x8 at 1.
          }
          {
            specf x2 v0. rewrite eqb_id in x2.
            rewrite <- x2 at 1. apply contains_triv.
          }
          {
            specf x2 v0. rewrite eqb_id in x2.
            rewrite <- x2 at 1. easy.
          }
          now destruct H5.
        }
        { easy. }
      }
      {
        intros. eq_inj H14.
        exists x9. split. easy.
        eapply EAOffer with
          (n:=v0) (v:=v).
        constructor.
        {
          constructor; cbn. easy.
          intros. now rewrite H0.
        }
        {
          cbn. rewrite <- x8, <- x2 at 1.
          repeat (easy || constructor).
        }
      }
    }
  }
  {
    unfold LiftSPrec, LiftSRelt.
    begin_commit. do 2 psimpl.
    ddestruct H. cbn in *.
    move H4 at bottom. destruct H4.
    {
      destruct H4.
      ddestruct H2.
      {
        rename y into w.
        pose (p' :=
          comRetPoss j
            (comRetPoss i
              (comInvPoss j
                (comInvPoss i
                  x4
                  (Exch v)
                  (ExchDef {i => v} {}))
                (Exch w)
                (ExchDef {i => v, j => w} {}))
              (Exch v)
              (ExchDef {i => v} {j => w})
              (Some w))
            (Exch w)
            (ExchDef {} {})
            (Some v)
        ).
        assert (
          VisPossSteps
            x4
            ([] ++
             [(i, CallEv (Exch v))] ++ [(j, CallEv (Exch w))] ++
             [(i, RetEv (Exch v) (Some w))] ++ [(j, RetEv (Exch w) (Some v))])
            p'
        ).
        {
          repeat rewrite app_assoc.
          apply retStep. apply retStep.
          apply callStep. apply callStep.
          constructor.
          {
            destruct H15.
            rewrite self_idle0.
            repeat (easy || constructor).
          }
          {
            cbn. rewrite eqb_nid; auto.
            des
          }
        }
        exists (eq p').
        split.
        { repeat econstructor. }
      }
    }
  }
}
intros.
apply lemRet.
{
  unfold sub, subRelt, LiftSPrec.
  intros. psimpl. now exists x4.
}
