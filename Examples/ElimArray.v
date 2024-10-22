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
  Logic.PropExtensionality
  Logic.Classical.
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

Record Inv {T A}
  {s : InterState (F A) (VE T A)} {x : Poss (VF T A)}
:= {
  state_idle : PState x = ExchDef {} {};
  wait_inv :
    forall n i v,
      contains (i, v) (pendSet s n) ->
      doneSet s n = {} ->
      Waiting i (Exch v) x;
  done_inv :
    forall n i j v w,
      i <> j ->
      contains (i, v) (pendSet s n) ->
      contains (j, w) (doneSet s n) ->
      Done j (Exch w) (Some v) x;
  wait_uniq :
    forall n m i v w,
      n <> m ->
      contains (i, v) (pendSet s n) ->
      doneSet s n = {} ->
      contains (i, w) (pendSet s m) ->
      doneSet s m <> {}
}.
Arguments Inv {T A} s x.

Record Ready {T A} {i : Name T}
  {s : InterState (F A) (VE T A)} {x : Poss (VF T A)}
:= {
  ready_inv : Inv s x;
  ready_lazy :
    forall n v,
      contains (i, v) (pendSet s n) ->
      doneSet s n <> {}
}.
Arguments Ready {T A} i s x.

Record Complete {T A} {n : nat} {i : Name T}
  {s : InterState (F A) (VE T A)} {x : Poss (VF T A)}
:= {
  comp_inv : Inv s x;
  comp_pres : exists v, contains (i, v) (pendSet s n);
  comp_nemp : doneSet s n = {};
  comp_lazy :
    forall m v,
      n <> m ->
      contains (i, v) (pendSet s m) ->
      doneSet s m <> {}
}.
Arguments Complete {T A} n i s x.

Record Offered {T A} {n : nat} {i : Name T} {v : A}
  {s : InterState (F A) (VE T A)} {x : Poss (VF T A)}
:= {
  offered_inv : Inv s x;
  offer_present : contains (i, v) (pendSet s n);
  offer_waiting : doneSet s n = {}
}.
Arguments Offered {T A} n i v s x.

Record Accepted {T A} {n : nat} {i j : Name T} {v w : A}
  {s : InterState (F A) (VE T A)} {x : Poss (VF T A)}
:= {
  accepted_inv : Inv s x;
  accept_done : contains (i, v) (doneSet s n);
  accept_wait : contains (j, w) (pendSet s n)
}.
Arguments Accepted {T A} n i j v w s x.

Notation IStep s i e t :=
  (InterStep (elimArray _ _) s (i, UEvent (Some e)) t).

Variant EATran {T A} : Name T -> Relt T A :=
| EARandCall s x t i n :
    IStep s i (CallEv (inl (Random n))) t ->
    EATran i s x t x
| EARandRet s x t i n k :
    IStep s i (RetEv (inl (Random n)) k) t ->
    EATran i s x t x
| EAOffer (s : InterState (F A) (VE T A)) x t i v n :
    forall (i_wait : Waiting i (Exch v) x),
    forall (i_uniq :
      forall m w,
        n <> m ->
        contains (i, w) (pendSet s m) ->
        doneSet s m <> {}),
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
  unfold Commit, LiftSPrec, LiftSRelt;
  intros; do 2 psimpl.

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
  | [ H : contains ?x (insert ?y ?s) |- _ ] =>
      let HL := fresh in
      let HR := fresh in
      apply contains_invert in H;
      destruct H as [HL | HR];
      [ddestruct HL | idtac]
  | [ H : contains ?x emp |- _ ] =>
      now apply contains_contr in H
  end.

Lemma conj_assoc {A B C : Prop} :
  (A /\ B /\ C) = ((A /\ B) /\ C).
now apply propositional_extensionality.
Qed.

Lemma ready_wait_stable {T A} (i : Name T) (v : A) :
  forall s x t y,
  (Ready i s x /\ Waiting i (Exch v) x) ->
  Rely i s x t y ->
  Ready i t y /\ Waiting i (Exch v) y.
intros. induction H0. easy.
apply IHSRTC. clear IHSRTC H1.
destruct H0, H0. rename x into j.
destruct H, H, H2, ready_inv0.
ddestruct H1.
{
  ddestruct H. cbn in *.
  psimpl. ddestruct H1.
  split.
  {
    constructor.
    {
      constructor.
      { easy. }
      {
        intros n0. specf H5 n0.
        setoid_rewrite <- H5.
        apply wait_inv0.
      }
      {
        intros n0. specf H5 n0.
        setoid_rewrite <- H5.
        apply done_inv0.
      }
      {
        intros n0 m0. assert (H5':=H5).
        specf H5 n0. specf H5' m0.
        setoid_rewrite <- H5.
        setoid_rewrite <- H5'.
        apply wait_uniq0.
      }
    }
    {
      intros n0. specf H5 n0.
      setoid_rewrite <- H5.
      apply ready_lazy0.
    }
  }
  { easy. }
}
{
  ddestruct H. cbn in *.
  psimpl. ddestruct H1.
  split.
  {
    constructor.
    {
      constructor.
      { easy. }
      {
        intros n0. specf H5 n0.
        setoid_rewrite <- H5.
        apply wait_inv0.
      }
      {
        intros n0. specf H5 n0.
        setoid_rewrite <- H5.
        apply done_inv0.
      }
      {
        intros n0 m0. assert (H5':=H5).
        specf H5 n0. specf H5' m0.
        setoid_rewrite <- H5.
        setoid_rewrite <- H5'.
        apply wait_uniq0.
      }
    }
    {
      intros n0. specf H5 n0.
      setoid_rewrite <- H5.
      apply ready_lazy0.
    }
  }
  { easy. }
}
{
  ddestruct H. cbn in *. psimpl.
  ddestruct H1. cbn in *. ddestruct H5.
  {
    split.
    {
      constructor.
      {
        constructor.
        { easy. }
        {
          intros.
          dec_eq_nats n0 n.
          {
            rewrite <- x in H5 at 1.
            now simp_sets.
          }
          {
            eapply wait_inv0 with
              (n:=n0).
            { now rewrite <- H4 at 1. }
            { now rewrite <- H4 at 1. }
          }
        }
        {
          intros.
          assert (n0 <> n).
          {
            contr. subst.
            rewrite <- x in H9 at 1.
            simp_sets.
          }
          eapply done_inv0 with
            (i:=i1) (n:=n0).
          { easy. }
          { now rewrite <- H4. }
          { now rewrite <- H4. }
        }
        {
          intros.
          dec_eq_nats n0 n.
          {
            rewrite <- x in H8 at 1.
            simp_sets. rewrite H4; auto.
            rewrite H4 in H10; auto.
            eapply i_uniq. easy.
            exact H10.
          }
          {
            dec_eq_nats m n.
            {
              rewrite <- x in H10 at 1.
              simp_sets. exfalso.
              eapply i_uniq.
              { symmetry. exact H11. }
              { rewrite <- H4 at 1; auto. exact H8. }
              { now rewrite <- H4 at 1. }
            }
            {
              rewrite H4; auto.
              eapply wait_uniq0 with
                (n:=n0)
                (i:=i1) (v:=v1)
                (w:=w).
              { easy. }
              { now rewrite <- H4 at 1. }
              { now rewrite <- H4 at 1. }
              { now rewrite <- H4 at 1. }
            }
          }
        }
      }
      {
        intros.
        assert (n0 <> n).
        {
          contr. subst.
          rewrite <- x in H5 at 1.
          now simp_sets.
        }
        rewrite H4 at 1; auto.
        eapply ready_lazy0 with
          (v:=v1).
        { now rewrite <- H4 at 1. }
      }
    }
    { constructor; easy. }
  }
  {
    split.
    {
      constructor.
      {
        constructor.
        { easy. }
        {
          intros.
          dec_eq_nats n0 n.
          {
            rewrite <- x in H8 at 1.
            simp_sets; try easy.
            eapply wait_inv0 with
              (n:=n).
            {
              rewrite <- x2 at 1.
              apply contains_triv.
            }
            { now rewrite <- x2 at 1. }
          }
          {
            eapply wait_inv0 with
              (n:=n0).
            { now rewrite <- H4 at 1. }
            { now rewrite <- H4 at 1. }
          }
        }
        {
          intros.
          assert (n0 <> n).
          {
            contr. subst.
            rewrite <- x in H10 at 1.
            simp_sets.
          }
          eapply done_inv0 with
            (i:=i2) (n:=n0).
          { contr. now subst. }
          { now rewrite <- H4. }
          { now rewrite <- H4. }
        }
        {
          intros.
          
        }
      }
      {
        intros.
        dec_eq_nats n0 n.
        {
          contr. subst.
          rewrite <- x in H8 at 1.
          simp_sets; try easy.
          eapply ready_lazy0 with
            (n:=n) (v:=x0).
          {
            rewrite <- x2 at 1.
            apply contains_triv.
          }
          { now rewrite <- x2 at 1. }
        }
        {
          rewrite H4 at 1; auto.
          eapply ready_lazy0 with
            (v:=v1).
          { now rewrite <- H4 at 1. }
        }
      }
    }
    { constructor; easy. }
  }
}
{
  ddestruct H1. cbn in *. psimpl.
  ddestruct H2. cbn in *. ddestruct H6.
  2:{
    rewrite <- x2 in H.
    ddestruct H. simp_sets.
  }
  rewrite H in x0.
  ddestruct x0. simp_sets.
  rename i0 into k, v0 into u.
  split.
  {
    constructor.
    {
      constructor.
      {
        destruct_big_steps.
        rewrite state_idle0 in H9.
        ddestruct H9. 2: simp_sets.
        rewrite <- x in H16.
        ddestruct H16. simp_sets.
        rewrite <- x in H23.
        ddestruct H23. 2: simp_sets.
        rewrite <- x in H30.
        ddestruct H30. simp_sets.
        easy.
      }
      {
        intros.
        assert (n0 <> n).
        {
          contr. subst.
          rewrite <- x0 in H10 at 1.
          simp_sets.
          admit.
        }
        admit.
      }
      {
        admit.
      }
      {
        admit.
      }
    }
    {
      admit.
    }
  }
  {
    admit.
  }
}
{
  ddestruct H1. cbn in *. psimpl.
  ddestruct H2. cbn in *. ddestruct H6.
  {
    rewrite H in x0.
    ddestruct x0. simp_sets.
  }
  rewrite H in x2.
  ddestruct x2. simp_sets.
  rename i0 into k, v0 into u.
  split.
  {
    constructor.
    {
      constructor.
      { easy. }
      {
        admit.
      }
      {
        admit.
      }
      {
        admit.
      }
    }
    {
      admit.
    }
  }
  {
    admit.
  }
}
{
  ddestruct H. cbn in *. psimpl.
  ddestruct H1. cbn in *. ddestruct H5.
  destruct_big_steps.
  rewrite state_idle0 in H5.
  ddestruct H5. 2: simp_sets.
  rewrite <- x in H14.
  ddestruct H14.
  split.
  {
    constructor.
    {
      constructor.
      { easy. }
      {
        admit.
      }
      {
        admit.
      }
      {
        admit.
      }
    }
    {
      admit.
    }
  }
  {
    admit.
  }
}
Admitted.

Lemma ready_done_stable {T A} (i : Name T) (v : A) (w : option A) :
  forall s x t y,
  (Ready i s x /\ Done i (Exch v) w x) ->
  Rely i s x t y ->
  Ready i t y /\ Done i (Exch v) w y.
Admitted.

Lemma complete_stable {T A} (k : nat) (i : Name T) (v : A) :
  forall s x t y,
  Complete k i s x \/ (Ready i s x /\ exists w, Done i (Exch v) w x) ->
  Rely i s x t y ->
  Complete k i t y \/ (Ready i t y /\ exists w, Done i (Exch v) w y).
Admitted.

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
  intros. psimpl. unfold TInvoke in H1. psimpl.
  specialize (H0 (invPoss i x1 (Exch v))).
  eassert _.
  {
    eapply H0. set_ext y.
    unfold invPoss.
    split; intros; psimpl.
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
    exists x1. split. easy.
    cbn. rewrite eqb_id.
    repeat split;
      (easy || apply differ_pointwise_trivial).
  }
  clear H0. psimpl.
  exists x0. split. easy.
  eapply ready_wait_stable.
  2: exact H4. split.
  {
    destruct H2, ready_inv0.
    constructor.
    {
      constructor.
      { easy. }
      {
        intros.
        assert (Waiting i0 (Exch v0) x1).
        {
          eapply wait_inv0 with (n:=n).
          now rewrite H3 at 1.
          now rewrite H3 at 1.
        }
        destruct H5.
        assert (i0 <> i).
        {
          contr. subst.
          unfold TIdle in H. psimpl.
          specialize (H5 x1 eq_refl). psimpl.
          now rewrite H5 in call_waiting.
        }
        constructor; cbn;
        now rewrite eqb_nid.
      }
      {
        intros.
        assert (Done j (Exch w) (Some v0) x1).
        {
          eapply done_inv0 with
            (i:=i0) (n:=n).
          { easy. }
          { now rewrite H3 at 1. }
          { now rewrite H3 at 1. }
        }
        destruct H6.
        assert (i <> j).
        {
          contr. subst.
          unfold TIdle in H. psimpl.
          specialize (H6 x1 eq_refl). psimpl.
          now rewrite H6 in call_done.
        }
        constructor; cbn;
        now rewrite eqb_nid.
      }
      { now setoid_rewrite <- H3. }
    }
    { now setoid_rewrite <- H3. }
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
    (S:=fun _ _ _ => LiftSPrec (fun s x =>
      Ready i s x /\
      Waiting i (Exch v) x))).
  {
    unfold Stable, stableRelt, sub, subRelt.
    unfold LiftSRelt, LiftSPrec. intros. psimpl.
    specialize (H0 x1 eq_refl). psimpl.
    exists x0. split. easy.
    eapply ready_wait_stable.
    2: exact H0. easy.
  }
  {
    unfold Stable, stablePost, stableRelt, sub, subRelt.
    unfold LiftSRelt, LiftSPrec. intros. psimpl.
    specialize (H0 x1 eq_refl). psimpl.
    exists x0. split. easy.
    eapply ready_wait_stable.
    2: exact H0. easy.
  }
  {
    begin_commit.
    rename x1 into p.
    exists (eq p).
    split.
    { repeat econstructor. }
    split.
    {
      intros. subst.
      repeat econstructor.
    }
    split.
    {
      exists p. split. easy.
      split.
      {
        constructor.
        {
          constructor.
          { apply H3. }
          {
            intros n. specf H7 n.
            setoid_rewrite <- H7.
            apply H3.
          }
          {
            intros n. specf H7 n.
            setoid_rewrite <- H7.
            apply H3.
          }
          {
            intros n m.
            assert (H7' := H7).
            specf H7 n. specf H7' m.
            setoid_rewrite <- H7.
            setoid_rewrite <- H7'.
            apply H3.
          }
        }
        {
          intros n. specf H7 n.
          setoid_rewrite <- H7.
          apply H3.
        }
      }
      { easy. }
    }
    {
      intros. eq_inj H8.
      exists x. split. easy.
      eapply EARandCall with
        (n:=T).
      constructor.
      {
        constructor; cbn. easy.
        intros. now rewrite H0.
      }
      { easy. }
    }
  }
  {
    begin_commit.
    rename x3 into p.
    exists (eq p).
    split.
    { repeat econstructor. }
    split.
    {
      intros. subst.
      repeat econstructor.
    }
    split.
    {
      exists p. split. easy.
      split.
      {
        constructor.
        {
          constructor.
          { apply H4. }
          {
            intros n. specf H9 n.
            setoid_rewrite <- H9.
            apply H4.
          }
          {
            intros n. specf H9 n.
            setoid_rewrite <- H9.
            apply H4.
          }
          {
            intros n m.
            assert (H9' := H9).
            specf H9 n. specf H9' m.
            setoid_rewrite <- H9.
            setoid_rewrite <- H9'.
            apply H4.
          }
        }
        {
          intros n. specf H9 n.
          setoid_rewrite <- H9.
          apply H4.
        }
      }
      { easy. }
    }
    {
      intros. eq_inj H10.
      exists x2. split. easy.
      eapply EARandRet with
        (n:=T) (k:=v0).
      constructor.
      {
        constructor; cbn. easy.
        intros. now rewrite H0.
      }
      { easy. }
    }
  }
}
intros.
rename v0 into k.
repeat rewrite <- reltCompAssoc at 1.
apply lemForget.
eapply lemBind.
{
  eapply (lemCall
    (Q:=fun _ _ => LiftSPrec (fun s x =>
      Complete k i s x \/
      (Ready i s x /\
       exists w, Done i (Exch v) w x)))
    (S:=fun w _ _ => LiftSPrec (fun s x =>
      Ready i s x /\
      Done i (Exch v) w x))).
  {
    unfold Stable, stableRelt, sub, subRelt.
    unfold LiftSRelt, LiftSPrec. intros. psimpl.
    specialize (H0 x1 eq_refl). psimpl.
    exists x0. split. easy.
    eapply complete_stable.
    2: exact H0. easy.
  }
  {
    unfold Stable, stablePost, stableRelt, sub, subRelt.
    unfold LiftSRelt, LiftSPrec. intros. psimpl.
    specialize (H0 x1 eq_refl). psimpl.
    exists x0. split. easy.
    eapply ready_done_stable.
    2: exact H0. easy.
  }
  {
    begin_commit.
    ddestruct H.
    cbn in *. ddestruct H9.
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
        left.
        constructor.
        {
          constructor.
          { apply H4. }
          {
            intros.
            dec_eq_nats k n.
            {
              rewrite <- x in H9 at 1.
              now simp_sets.
            }
            {
              apply H4 with (n:=n).
              { now rewrite <- H8. }
              { now rewrite <- H8. }
            }
          }
          {
            intros.
            assert (k <> n).
            {
              contr. subst.
              rewrite <- x in H13 at 1.
              now apply contains_contr in H13.
            }
            eapply H4 with (n:=n).
            { exact H9. }
            { now rewrite <- H8 at 1. }
            { now rewrite <- H8 at 1. }
          }
          {
            intros. destruct H4, ready_inv0.
            assert (k <> m).
            {
              contr. subst.
              rewrite <- x in H14 at 1.
              simp_sets.
              eapply ready_lazy0 with
                (n:=n) (v:=v0).
              rewrite <- H8 at 1.
              easy. easy. now rewrite <- H8.
            }
            dec_eq_nats k n.
            {
              rewrite <- x in H12 at 1.
              simp_sets.
              rewrite H8 at 1; auto.
              eapply ready_lazy0 with
                (v:=w).
              { now rewrite <- H8 at 1. }
            }
            {
              rewrite H8 at 1.
              eapply wait_uniq0 with
                (n:=n)
                (i:=i0) (v:=v0)
                (w:=w).
              { easy. }
              { now rewrite <- H8 at 1. }
              { now rewrite <- H8 at 1. }
              { now rewrite <- H8 at 1. }
              { easy. }
            }
          }
        }
        {
          exists v.
          rewrite <- x at 1.
          apply contains_triv.
        }
        { now rewrite <- x at 1. }
        {
          intros.
          destruct H4, ready_inv0.
          rewrite H8 at 1; auto.
          eapply ready_lazy0 with
            (v:=v0).
          { now rewrite <- H8 at 1. }
        }
      }
      {
        intros. eq_inj H9.
        exists x8. split. easy.
        eapply EAOffer with
          (n:=k) (v:=v).
        { easy. }
        {
          intros.
          destruct H4.
          eapply ready_lazy0.
          exact H12.
        }
        {
          constructor.
          {
            constructor; cbn. easy.
            intros. now rewrite H0.
          }
          {
            cbn. repeat (easy || constructor).
            econstructor.
            { easy. }
            { symmetry. exact x4. }
            { symmetry. exact x. }
            { easy. }
            { constructor. }
          }
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
        left.
        constructor.
        {
          constructor.
          { apply H4. }
          {
            intros.
            dec_eq_nats k n.
            {
              rewrite <- x in H12 at 1.
              simp_sets.
              { easy. }
              {
                eapply H4 with (n:=n).
                {
                  rewrite <- x8 at 1.
                  apply contains_triv.
                }
                { now rewrite <- x8 at 1. }
              }
            }
            {
              apply H4 with (n:=n).
              { now rewrite <- H8. }
              { now rewrite <- H8. }
            }
          }
          {
            intros.
            assert (k <> n).
            {
              contr. subst.
              rewrite <- x in H14 at 1.
              now apply contains_contr in H14.
            }
            eapply H4 with (n:=n).
            { exact H12. }
            { now rewrite <- H8 at 1. }
            { now rewrite <- H8 at 1. }
          }
          {
            intros. destruct H4, ready_inv0.
            dec_eq_nats k n.
            {
              rewrite <- x in H13 at 1.
              simp_sets.
              {
                rewrite H8 at 1; auto.
                eapply ready_lazy0 with
                  (v:=w).
                { now rewrite <- H8 at 1. }
              }
              {
                rewrite H8 at 1; auto.
                eapply wait_uniq0 with
                  (n:=n)
                  (i:=i0) (v:=x4)
                  (w:=w).
                { easy. }
                {
                  rewrite <- x8 at 1.
                  apply contains_triv.
                }
                { now rewrite <- x8 at 1. }
                { now rewrite <- H8 at 1. }
              }
            }
            {
              dec_eq_nats k m.
              {
                rewrite <- x in H15 at 1.
                simp_sets.
                {
                  exfalso.
                  eapply ready_lazy0 with
                    (n:=n) (v:=v0).
                  { now rewrite <- H8 at 1. }
                  { now rewrite <- H8 at 1. }
                }
                {
                  exfalso.
                  eapply wait_uniq0 with
                    (n:=n) (m:=m)
                    (i:=i0) (v:=v0)
                    (w:=x4).
                  { easy. }
                  { now rewrite <- H8. }
                  { now rewrite <- H8. }
                  {
                    rewrite <- x8 at 1.
                    apply contains_triv.
                  }
                  { now rewrite <- x8 at 1. }
                }
              }
              {
                rewrite H8 at 1; auto.
                eapply wait_uniq0 with
                  (n:=n)
                  (i:=i1) (v:=v0)
                  (w:=w).
                { easy. }
                { now rewrite <- H8 at 1. }
                { now rewrite <- H8 at 1. }
                { now rewrite <- H8 at 1. }
              }
            }
          }
        }
        {
          exists v.
          rewrite <- x at 1.
          apply contains_triv.
        }
        { now rewrite <- x at 1. }
        {
          intros. destruct H4.
          rewrite H8 at 1; auto.
          eapply ready_lazy0 with
            (v:=v0).
          { now rewrite <- H8 at 1. }
        }
      }
      {
        intros. eq_inj H12.
        exists x9. split. easy.
        eapply EAOffer with
          (n:=k) (v:=v).
        { easy. }
        {
          intros. destruct H4, ready_inv0.
          eapply ready_lazy0. exact H13.
        }
        {
          constructor.
          {
            constructor; cbn. easy.
            intros. now rewrite H0.
          }
          {
            cbn.
            repeat (easy || constructor).
            econstructor.
            { easy. }
            { symmetry. exact x8. }
            { symmetry. exact x. }
            { easy. }
            { now constructor. }
          }
        }
      }
    }
  }
  intros.
  {
    begin_commit.
    rename x3 into p.
    destruct H4.
    {
      ddestruct H. cbn in *.
      ddestruct H10.
      {
        rename y into w.
        pose (p' :=
          comRetPoss j
            (comRetPoss i
              (comInvPoss j
                (comInvPoss i
                  p
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
            p
            ([] ++
            [(i, CallEv (Exch v))] ++
            [(j, CallEv (Exch w))] ++
            [(i, RetEv (Exch v) (Some w))] ++
            [(j, RetEv (Exch w) (Some v))])
            p'
        ).
        {
          assert (Waiting i (Exch v) p).
          {
            eapply H4 with (n:=k).
            {
              rewrite <- x2 at 1.
              apply contains_triv.
            }
            { now rewrite <- x2 at 1. }
          }
          assert (Waiting j (Exch w) p).
          {
            eapply H4 with (n:=k).
            {
              rewrite <- x2, insert_perm at 1.
              apply contains_triv.
            }
            { now rewrite <- x2 at 1. }
          }
          assert (PState p = ExchDef {} {}).
          {
            apply H4.
          }
          destruct H13, H14.
          repeat rewrite app_assoc.
          apply retStep. apply retStep.
          apply callStep. apply callStep.
          constructor.
          {
            rewrite H15.
            repeat (easy || constructor).
          }
          {
            cbn. rewrite eqb_nid, insert_perm; auto.
            repeat (easy || constructor).
          }
          {
            cbn. rewrite eqb_id, eqb_nid; auto.
            repeat (easy || constructor).
          }
          {
            cbn. rewrite eqb_id, eqb_nid; auto.
            repeat (easy || constructor).
          }
        }
        exists (eq p').
        split.
        { repeat econstructor. }
        split.
        {
          intros. subst.
          exists p. split. easy.
          eapply erase_vis.
          exact H13.
        }
        split.
        {
          exists p'. split. easy.
          split.
          {
            constructor.
            {
              constructor.
              { now subst p'. }
              {
                intros.
                assert (k <> n).
                {
                  contr. subst.
                  rewrite <- x in H15 at 1.
                  simp_sets.
                }
                assert (i <> i0).
                {
                  contr. subst.
                  eapply H4.(comp_inv).(wait_uniq) with
                    (n:=k) (m:=n).
                  { easy. }
                  {
                    rewrite <- x2 at 1.
                    apply contains_triv.
                  }
                  { now rewrite <- x2 at 1. }
                  {
                    rewrite <- H5 at 1.
                    exact H14. easy.
                  }
                  { now rewrite <- H5 at 1. }
                }
                assert (j <> i0).
                {
                  contr. subst.
                  eapply H4.(comp_inv).(wait_uniq) with
                    (n:=k) (m:=n).
                  { easy. }
                  {
                    rewrite <- x2, insert_perm at 1.
                    apply contains_triv.
                  }
                  { now rewrite <- x2 at 1. }
                  {
                    rewrite <- H5 at 1.
                    exact H14. easy.
                  }
                  { now rewrite <- H5 at 1. }
                }
                assert (Waiting i0 (Exch v0) p).
                {
                  eapply H4 with (n:=n).
                  { now rewrite <- H5 at 1. }
                  { now rewrite <- H5 at 1. }
                }
                destruct H19.
                constructor; cbn;
                now rewrite ?eqb_id, ?eqb_nid.
              }
              {
                intros.
                dec_eq_nats k n.
                {
                  rewrite <- x in H15 at 1.
                  rewrite <- x in H16 at 1.
                  simp_sets.
                  constructor; cbn;
                  now rewrite eqb_id.
                }
                {
                  assert (i <> j0).
                  {
                    contr. subst.
                    rewrite H5 in H15 at 1; auto.
                    rewrite H5 in H16 at 1; auto.
                    assert (Done j0 (Exch w0) (Some v0) p).
                    {
                      eapply H4 with (n:=n).
                      { exact H14. }
                      { easy. }
                      { easy. }
                    }
                    assert (Waiting j0 (Exch v) p).
                    {
                      eapply H4 with (n:=k).
                      {
                        rewrite <- x2 at 1.
                        apply contains_triv.
                      }
                      { now rewrite <- x2 at 1. }
                    }
                    destruct H18, H19.
                    rewrite call_done in call_waiting.
                    easy.
                  }
                  assert (j <> j0).
                  {
                    contr. subst.
                    rewrite H5 in H15 at 1; auto.
                    rewrite H5 in H16 at 1; auto.
                    assert (Done j0 (Exch w0) (Some v0) p).
                    {
                      eapply H4 with (n:=n).
                      { exact H14. }
                      { easy. }
                      { easy. }
                    }
                    assert (Waiting j0 (Exch w) p).
                    {
                      eapply H4 with (n:=k).
                      {
                        rewrite <- x2, insert_perm at 1.
                        apply contains_triv.
                      }
                      { now rewrite <- x2 at 1. }
                    }
                    destruct H19, H20.
                    rewrite call_done in call_waiting.
                    easy.
                  }
                  assert (Done j0 (Exch w0) (Some v0) p).
                  {
                    eapply H4 with (n:=n).
                    { exact H14. }
                    { now rewrite <- H5 at 1. }
                    { now rewrite <- H5 at 1. }
                  }
                  destruct H20.
                  constructor; cbn;
                  now rewrite ?eqb_id, ?eqb_nid.
                }
              }
              {
                intros.
                assert (k <> n).
                {
                  contr. subst.
                  rewrite <- x in H16 at 1.
                  simp_sets.
                }
                assert (k <> m).
                {
                  contr. subst.
                  rewrite <- x in H17 at 1.
                  simp_sets.
                  eapply H4.(comp_inv).(wait_uniq) with
                    (n:=n) (m:=m)
                    (i:=i) (v:=v0) (w:=v).
                  { easy. }
                  { now rewrite <- H5 at 1. }
                  { now rewrite <- H5 at 1. }
                  {
                    rewrite <- x2 at 1.
                    apply contains_triv.
                  }
                  { now rewrite <- x2 at 1. }
                }
                rewrite H5 at 1; auto.
                eapply H4 with (n:=n).
                { easy. }
                {
                  rewrite <- H5 at 1; auto.
                  exact H15.
                }
                { now rewrite <- H5 at 1. }
                {
                  rewrite <- H5 at 1; auto.
                  exact H17.
                }
              }
            }
            {
              intros.
              dec_eq_nats k n.
              {
                rewrite <- x at 1.
                apply disj_cons.
              }
              {
                rewrite H5 at 1.
                eapply H4 with
                  (n:=k)
                  (i:=i) (v:=v)
                  (w:=v0).
                { easy. }
                {
                  rewrite <- x2 at 1.
                  apply contains_triv.
                }
                { now rewrite <- x2 at 1. }
                { now rewrite <- H5 at 1. }
                { easy. }
              }
            }
          }
          {
            constructor; cbn;
            now rewrite ?eqb_id, ?eqb_nid.
          }
        }
        {
          intros. eq_inj H14.
          exists p'. split. easy.
          eapply EAAccept with
            (n:=k) (v:=v)
            (j:=j) (w:=w).
          { easy. }
          {
            constructor.
            {
              constructor; cbn. easy.
              intros. now rewrite H0.
            }
            {
              cbn.
              repeat (easy || constructor).
              econstructor.
              { easy. }
              { symmetry. exact x2. }
              { symmetry. exact x. }
              { easy. }
              { now constructor. }
            }
          }
          { easy. }
        }
      }
      {
        exists (eq p).
        split.
        { repeat econstructor. }
        split.
        {
          intros. subst.
          repeat econstructor.
        }
        split.
        {
          exists p. split. easy.
          split.
          {
            constructor.
            {
              constructor.
              { apply H4. }
              {
                intros.
                assert (k <> n).
                {
                  contr. subst.
                  rewrite <- x in H13 at 1.
                  now apply contains_contr in H13.
                }
                eapply H4 with
                  (n:=n).
                { now rewrite <- H5 at 1. }
                { now rewrite <- H5 at 1. }
              }
              {
                intros.
                assert (k <> n).
                {
                  contr. subst.
                  rewrite <- x in H14 at 1.
                  simp_sets.
                }
                eapply H4 with
                  (i:=i1)
                  (n:=n).
                { easy. }
                { now rewrite <- H5 at 1. }
                { now rewrite <- H5 at 1. }
              }
              {
                intros.
                assert (k <> m).
                {
                  contr. subst.
                  rewrite <- x in H16 at 1.
                  simp_sets.
                }
                assert (k <> n).
                {
                  contr. subst.
                  rewrite <- x in H14 at 1.
                  simp_sets.
                }
                rewrite H5 at 1; auto.
                eapply H4 with
                  (n:=n)
                  (i:=i1) (v:=v0)
                  (w:=w).
                { easy. }
                { now rewrite <- H5 at 1. }
                { now rewrite <- H5 at 1. }
                { now rewrite <- H5 at 1. }
              }
            }
            {
              intros.
              assert (k <> n).
              {
                contr. subst.
                rewrite <- x in H13 at 1.
                simp_sets.
              }
              destruct H4.
              rewrite H5 at 1; auto.
              eapply comp_lazy0 with
                (v:=v0).
              { easy. }
              { now rewrite <- H5 at 1. }
            }
          }
          {
            eapply H4 with
              (n:=k) (i:=i0).
            { easy. }
            {
              rewrite <- x7 at 1.
              apply contains_triv.
            }
            {
              rewrite <- x7 at 1.
              apply contains_triv.
            }
          }
        }
        {
          intros. eq_inj H13.
          exists x10. split. easy.
          eapply EAFinish with
            (n:=k)
            (j:=i0) (w:=x2)
            (v:=v).
          { easy. }
          {
            constructor.
            {
              constructor; cbn. easy.
              intros. now rewrite H0.
            }
            {
              cbn.
              repeat (easy || constructor).
              econstructor.
              { easy. }
              { symmetry. exact x7. }
              { symmetry. exact x. }
              { easy. }
              { now constructor. }
            }
          }
        }
      }
      {
        pose (p' :=
          comRetPoss i
            (comInvPoss i
              p
              (Exch v)
              (ExchDef {i => v} {}))
            (Exch v)
            (ExchDef {} {})
            None
        ).
        assert (
          VisPossSteps
            p
            ([] ++
            [(i, CallEv (Exch v))] ++
            [(i, RetEv (Exch v) None)])
            p'
        ).
        {
          assert (Waiting i (Exch v) p).
          {
            eapply H4 with
              (n:=k).
            {
              rewrite <- x2 at 1.
              apply contains_triv.
            }
            { now rewrite <- x2 at 1. }
          }
          destruct H10. rewrite app_assoc.
          apply retStep. apply callStep.
          constructor.
          {
            destruct H4, comp_inv0.
            rewrite state_idle0.
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
          intros. subst.
          exists p. split. easy.
          eapply erase_vis.
          exact H10.
        }
        split.
        {
          exists p'. split. easy.
          split.
          {
            constructor.
            {
              constructor.
              { easy. }
              {
                intros. destruct H4, comp_inv0.
                assert (k <> n).
                {
                  contr. subst.
                  rewrite <- x in H13 at 1.
                  simp_sets.
                }
                assert (i0 <> i).
                {
                  contr. subst.
                  eapply comp_lazy0 with
                    (m:=n)
                    (v:=v0).
                  { easy. }
                  { now rewrite <- H5 at 1. }
                  { now rewrite <- H5 at 1. }
                }
                assert (Waiting i0 (Exch v0) p).
                {
                  eapply wait_inv0 with
                    (n:=n).
                  { now rewrite <- H5 at 1. }
                  { now rewrite <- H5 at 1. }
                }
                destruct H16.
                constructor; cbn;
                now rewrite eqb_nid.
              }
              {
                intros. destruct H4, comp_inv0.
                assert (k <> n).
                {
                  contr. subst.
                  rewrite <- x in H14 at 1.
                  simp_sets.
                }
                assert (Done j (Exch w) (Some v0) p).
                {
                  eapply done_inv0 with
                    (i:=i0)
                    (n:=n).
                  { easy. }
                  { now rewrite <- H5 at 1. }
                  { now rewrite <- H5 at 1. }
                }
                assert (i <> j).
                {
                  contr. subst.
                  assert (Waiting j (Exch v) p).
                  {
                    eapply wait_inv0 with
                      (n:=k).
                    {
                      rewrite <- x2 at 1.
                      apply contains_triv.
                    }
                    { now rewrite <- x2 at 1. }
                  }
                  destruct H16, H17.
                  rewrite call_done in call_waiting.
                  easy.
                }
                destruct H16.
                constructor; cbn;
                now rewrite eqb_nid.
              }
              {
                intros.
                assert (k <> n).
                {
                  contr. subst.
                  rewrite <- x in H14 at 1.
                  simp_sets.
                }
                assert (k <> m).
                {
                  contr. subst.
                  rewrite <- x in H16 at 1.
                  simp_sets.
                }
                rewrite H5 at 1; auto.
                eapply H4 with
                  (n:=n)
                  (i:=i0) (v:=v0)
                  (w:=w).
                { easy. }
                { now rewrite <- H5 at 1. }
                { now rewrite <- H5 at 1. }
                { now rewrite <- H5 at 1. }
              }
            }
            {
              intros.
              assert (k <> n).
              {
                contr. subst.
                rewrite <- x in H13 at 1.
                simp_sets.
              }
              rewrite H5 at 1; auto.
              eapply H4.(comp_lazy) with
                (v:=v0).
              { easy. }
              { now rewrite <- H5 at 1. }
            }
          }
          {
            constructor; cbn;
            now rewrite eqb_id.
          }
        }
        {
          intros. eq_inj H13.
          exists p'. split. easy.
          eapply EARevoke with
            (n:=k) (v:=v).
          {
            constructor.
            {
              constructor; cbn. easy.
              intros. now rewrite H0.
            }
            {
              cbn.
              repeat (easy || constructor).
              econstructor.
              { easy. }
              { symmetry. exact x2. }
              { symmetry. exact x. }
              { easy. }
              { now constructor. }
            }
          }
          { easy. }
        }
      }
    }
    {
      psimpl.
      destruct H4, ready_inv0.
      ddestruct H. cbn in *.
      ddestruct H5.
      {
        rename y into w.
        assert (Waiting i (Exch v) p).
        {
          eapply wait_inv0 with
            (n:=k).
          {
            rewrite <- x3 at 1.
            apply contains_triv.
          }
          { now rewrite <- x3 at 1. }
        }
        destruct H11, H13.
        now rewrite call_done in call_waiting.
      }
      {
        exists (eq p).
        split.
        { repeat econstructor. }
        split.
        {
          intros. subst.
          repeat econstructor.
        }
        split.
        {
          exists p. split. easy.
          split.
          {
            constructor.
            {
              constructor.
              { easy. }
              {
                intros.
                assert (k <> n).
                {
                  contr. subst.
                  rewrite <- x in H13 at 1.
                  simp_sets.
                }
                eapply wait_inv0 with
                  (n:=n).
                { now rewrite <- H4 at 1. }
                { now rewrite <- H4 at 1. }
              }
              {
                intros.
                assert (k <> n).
                {
                  contr. subst.
                  rewrite <- x in H14 at 1.
                  simp_sets.
                }
                eapply done_inv0 with
                  (i:=i1) (n:=n).
                { easy. }
                { now rewrite <- H4 at 1. }
                { now rewrite <- H4 at 1. }
              }
              {
                intros.
                assert (k <> n).
                {
                  contr. subst.
                  rewrite <- x in H14 at 1.
                  simp_sets.
                }
                assert (k <> m).
                {
                  contr. subst.
                  rewrite <- x in H16 at 1.
                  simp_sets.
                }
                rewrite H4 at 1; auto.
                eapply wait_uniq0 with
                  (n:=n)
                  (i:=i1) (v:=v0)
                  (w:=w).
                { easy. }
                { now rewrite <- H4 at 1. }
                { now rewrite <- H4 at 1. }
                { now rewrite <- H4 at 1. }
              }
            }
            {
              intros.
              assert (k <> n).
              {
                contr. subst.
                rewrite <- x in H13 at 1.
                simp_sets.
              }
              rewrite H4 at 1; auto.
              eapply ready_lazy0 with
                (v:=v0).
              { now rewrite <- H4 at 1. }
            }
          }
          {
            eapply done_inv0 with
              (i:=i0)
              (n:=k).
            { easy. }
            {
              rewrite <- x10 at 1.
              apply contains_triv.
            }
            {
              rewrite <- x10 at 1.
              apply contains_triv.
            }
          }
        }
        {
          intros. eq_inj H13.
          exists x11. split. easy.
          eapply EAFinish with
            (n:=k) (v:=v)
            (j:=i0) (w:=x3).
          { easy. }
          {
            constructor.
            {
              constructor; cbn. easy.
              intros. now rewrite H0.
            }
            {
              cbn.
              repeat (easy || constructor).
              econstructor.
              { easy. }
              { symmetry. exact x10. }
              { symmetry. exact x. }
              { easy. }
              { now constructor. }
            }
          }
        }
      }
      {
        exfalso.
        assert (Waiting i (Exch v) p).
        {
          eapply wait_inv0 with
            (n:=k).
          {
            rewrite <- x3 at 1.
            apply contains_triv.
          }
          { now rewrite <- x3 at 1. }
        }
        destruct H11, H5.
        rewrite call_done in call_waiting.
        easy.
      }
    }
  }
}
{
  intros. constructor.
  unfold sub, subRelt.
  intros. psimpl. easy.
}
Qed.