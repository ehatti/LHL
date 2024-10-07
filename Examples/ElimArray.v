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
  Lists.List.
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

Record Inv {T A}
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
:= {
  state_idle :
    PState x = ExchDef {} {};
  offered1_wait :
    forall i v n,
      exchSt s n = ExchDef {i => v} {} ->
      Waiting i (Exch v) x;
  offered2_wait :
    forall i j v w n,
      exchSt s n = ExchDef {i => v, j => w} {} ->
      Waiting i (Exch v) x /\
      Waiting j (Exch w) x;
  accepted_done :
    forall i j v w n,
      exchSt s n = ExchDef {j => w} {i => v} ->
      Done i (Exch v) (Some w) x /\
      Done j (Exch w) (Some v) x;
  (* covering :
    forall i,
      (exists n,
        (exists v os cs,
          exchSt s n = ExchDef os cs /\
          (contains (i, v) os \/ contains (i, v) cs)) /\
        forall m v os cs,
          exchSt s m = ExchDef os cs ->
          n <> m ->
          ~contains (i, v) os /\ ~contains (i, v) cs) \/
      (forall n v os cs,
        exchSt s n = ExchDef os cs ->
        ~contains (i, v) os /\ ~contains (i, v) cs) *)
}.

Notation IStep s i e t :=
  (InterStep (elimArray _ _) s (i, UEvent (Some e)) t).

Variant EATran {T A} : Relt T A :=
| EARandCall s x t i n :
    IStep s i (CallEv (inl (Random n))) t ->
    EATran s x t x
| EARandRet s x t i n k :
    IStep s i (RetEv (inl (Random n)) k) t ->
    EATran s x t x
| EAOffer s x t i v n :
    IStep s i (CallEv (inr (At n (Exch v)))) t ->
    EATran s x t x
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
    EATran s x t y
| EAFinish (s : InterState (F A) (VE T A)) x t i j v w n :
    exchSt s n = ExchDef {j => w} {i => v} ->
    IStep s i (RetEv (inr (At n (Exch v))) (Some w)) t ->
    EATran s x t x
| EARevoke s x t y i v n :
    IStep s i (RetEv (inr (At n (Exch v))) None) t ->
    VisPossSteps
      x
      [(i, CallEv (Exch v));
       (i, RetEv (Exch v) None)]
      y ->
    EATran s x t y.

Definition Guar {T A} : Relt T A :=
  EATran.

Definition Rely {T A} : Relt T A :=
  SRTC EATran.

Ltac begin_commit :=
  unfold Commit, LiftSPrec; intros.

Lemma eq_inj {A} {x y : A} :
  eq x = eq y -> x = y.
intros. now rewrite H.
Qed.

Ltac eq_inj H :=
  apply eq_inj in H; subst.

Lemma pres_Inv {T A} :
  forall s t x,
  Inv (T:=T) (A:=A) s x ->
  RState (snd s) = RState (snd t) ->
  Inv t x.
intros. destruct H.
constructor.
{
  easy.
}
{
  intros. eapply offered1_wait0.
  rewrite H0. exact H.
}
{
  intros. eapply offered2_wait0.
  rewrite H0. exact H.
}
{
  intros. eapply accepted_done0.
  rewrite H0. exact H.
}
(* {
  intros. specialize (covering0 i).
  destruct covering0; psimpl; [left|right].
  {
    exists x0.
    split.
    {
      exists x1, x2, x3.
      rewrite <- H0. easy.
    }
    {
      intros. eapply H1.
      rewrite H0. exact H3.
      easy.
    }
  }
  {
    intros. eapply H.
    rewrite H0. exact H1.
  }
} *)
Qed.

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


Lemma exch_correct {T A} {i : Name T} {v : A} :
  VerifyProg i (LiftSRelt Rely) (LiftSRelt Guar)
    (prComp (LiftSPrec Inv) (TInvoke (elimArray T A) i _ (Exch v)) ->>
     LiftSRelt Rely)
    (exch v)
    (fun r _ _ => LiftSPrec (fun s x =>
      Inv s x /\
      Done i (Exch v) r x)).
eapply weakenPrec with
  (P:=fun _ _ => LiftSPrec (fun s x =>
    Inv s x /\
    Waiting i (Exch v) x)).
2:{
  admit.
}
unfold exch.
eapply lemBind.
{
  eapply (lemCall
    (Q:=fun _ _ => LiftSPrec (fun s x =>
      Inv s x /\
    Waiting i (Exch v) x))
    (S:=fun r _ _ => LiftSPrec (fun s x =>
      Inv s x /\
      Waiting i (Exch v) x /\
      r < T))).
  {
    admit.
  }
  {
    admit.
  }
  {
    begin_commit. do 2 psimpl.
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
        eapply pres_Inv.
        exact H3. easy.
      }
      { easy. }
    }
    {
      exists x1. split. easy.
      eq_inj H8. eapply EARandCall
        with (i:=i) (n:=T).
      constructor.
      {
        constructor; cbn. easy.
        intros. now rewrite H0.
      }
      { easy. }
    }
  }
  {
    intros.
    begin_commit. do 5 destruct H.
    clear - H2 H1 H0 H3. do 2 psimpl.
    exists (eq x).
    split.
    { repeat econstructor. }
    split.
    {
      intros. subst.
      repeat econstructor.
    }
    split.
    {
      exists x. split. easy.
      split.
      {
        eapply pres_Inv.
        exact H3. easy.
      }
      { now ddestruct H. }
    }
    {
      exists x. split. easy.
      eq_inj H8. apply EARandRet
        with (i:=i) (n:=T) (k:=v0).
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
eapply lemBind.
{
  eapply (lemCall
    (Q:=fun _ _ => LiftSPrec (fun s x =>
      Waiting i (Exch v) x /\
      Inv s x))
    (S:=fun r _ _ => LiftSPrec (fun s x =>
      Inv s x /\
      Done i (Exch v) r x))).
  {
    admit.
  }
  {
    admit.
  }
  {
    repeat rewrite <- reltCompAssoc.
    begin_commit. do 5 destruct H.
    clear H. do 2 psimpl.
    exists (eq x3).
    split.
    { repeat econstructor. }
    split.
    {
      intros. subst.
      repeat econstructor.
    }
    destruct H3. ddestruct H.
    cbn in *. ddestruct H2.
    {
      split.
      {
        exists x3. split. easy.
        split.
        { easy. }
        {
          constructor.
          {
            easy.
          }
          {
            intros. specf x n.
            dec_eq_nats v0 n.
            {
              rewrite eqb_id in x.
              rewrite <- x in H2 at 1.
              ddestruct H2. simp_sets.
              easy.
            }
            {
              specf x2 n. rewrite eqb_nid in *.
              all: try easy. eapply offered1_wait0.
              rewrite <- x2, x. easy.
            }
          }
          {
            intros. specf x n.
            dec_eq_nats v0 n.
            {
              rewrite eqb_id in x.
              rewrite <- x in H2 at 1.
              ddestruct H2. simp_sets.
            }
            {
              specf x2 n. rewrite eqb_nid in *.
              all: try easy. eapply offered2_wait0.
              rewrite <- x2, x. easy.
            }
          }
          {
            intros. specf x n.
            dec_eq_nats v0 n.
            {
              rewrite eqb_id in x.
              rewrite <- x in H2 at 1.
              ddestruct H2. simp_sets.
            }
            {
              specf x2 n. rewrite eqb_nid in *.
              all: try easy. eapply accepted_done0.
              rewrite <- x2, x. easy.
            }
          }
        }
      }
      {
        exists x3. split. easy.
        eq_inj H2. eapply EAOffer
          with (i:=i) (n:=v0) (v:=v).
        constructor.
        {
          constructor; cbn. easy.
          intros. now rewrite H0.
        }
        {
          cbn. rewrite <- x2, <- x at 1.
          repeat (easy || constructor).
        }
      }
    }
    {
      split.
      {
        exists x3. split. easy.
        split.
        { easy. }
        {
          constructor.
          { easy. }
          {
            intros. specf x1 n.
            dec_eq_nats v0 n.
            {
              rewrite eqb_id in x1.
              rewrite <- x1 in H9 at 1.
              ddestruct H9. simp_sets.
            }
            {
              specf x2 n. rewrite eqb_nid in *.
              all: try easy. eapply offered1_wait0.
              rewrite <- x2, x1. easy.
            }
          }
          {
            intros. specf x1 n.
            dec_eq_nats v0 n.
            {
              specf x2 n.
              rewrite eqb_id in x1, x2.
              rewrite <- x1 in H9 at 1.
              ddestruct H9. simp_sets.
              symmetry in x2.
              apply offered1_wait0 in x2.
              easy.
            }
            {
              specf x2 n. rewrite eqb_nid in *.
              all: try easy. eapply offered2_wait0.
              rewrite <- x2, x1. easy.
            }
          }
          {
            intros. specf x1 n.
            dec_eq_nats v0 n.
            {
              rewrite eqb_id in x1.
              rewrite <- x1 in H9 at 1.
              ddestruct H9. simp_sets.
            }
            {
              specf x2 n. rewrite eqb_nid in *.
              all: try easy. eapply accepted_done0.
              rewrite <- x2, x1. easy.
            }
          }
        }
      }
      {
        exists x3. split. easy.
        eq_inj H9. eapply EAOffer
          with (i:=i) (n:=v0) (v:=v).
        constructor.
        {
          constructor; cbn. easy.
          intros. now rewrite H0.
        }
        {
          cbn. rewrite <- x2, <- x1 at 1.
          repeat (easy || constructor).
        }
      }
    }
  }
  {
    intros.
    repeat rewrite <- reltCompAssoc.
    begin_commit. do 5 destruct H.
    clear H. do 2 psimpl.
    destruct H3, H4.
    ddestruct H. cbn in *.
    ddestruct H2.
    {
      rename y into w.
      set (x3' :=
        comRetPoss j
          (comRetPoss i
            (comInvPoss j
              (comInvPoss i
                x3
                (Exch v)
                (ExchDef {i => v} {}))
              (Exch w)
              (ExchDef {j => w, i => v} {}))
            (Exch v)
            (ExchDef {i => v} {j => w})
            (Some w))
          (Exch w)
          (ExchDef {} {})
          (Some v)
      ).
      assert (
        VisPossSteps
          x3
          ([] ++
           [(i, CallEv (Exch v))] ++
           [(j, CallEv (Exch w))] ++
           [(i, RetEv (Exch v) (Some w))] ++
           [(j, RetEv (Exch w) (Some v))])
          x3'
      ).
      {
        repeat rewrite app_assoc.
        specf x2 v0.
        rewrite eqb_id in x2. symmetry in x2.
        apply offered2_wait0 in x2. destruct x2.
        apply retStep. apply retStep.
        apply callStep. apply callStep.
        constructor.
        {
          rewrite state_idle0. destruct H4.
          repeat (easy || constructor).
        }
        {
          cbn. rewrite eqb_nid. destruct H8.
          repeat (easy || constructor). easy.
        }
        {
          cbn. rewrite eqb_id, eqb_nid.
          destruct H4. rewrite insert_perm.
          repeat (easy || constructor). easy.
        }
        {
          cbn. rewrite eqb_id, eqb_nid. destruct H8.
          repeat (easy || constructor). easy.
        }
      }
      exists (eq x3').
      split.
      { repeat econstructor. }
      split.
      {
        intros. subst.
        exists x3. split. easy.
        eapply erase_vis.
        exact H4.
      }
      split.
      {
        exists x3'. split. easy.
        split.
        {
          subst x3'.
          constructor.
          { easy. }
          {
            intros.
            assert (v0 <> n).
            {
              unfold not. intros. subst.
              specf x n. rewrite eqb_id in x.
              rewrite <- x in H8 at 1.
              ddestruct H8. simp_sets.
            }
            assert (differ_pointwise (RState (snd s)) (RState (snd t)) v0).
            {
              unfold differ_pointwise. intros.
              specf x2 j0. specf x j0.
              rewrite <- x2, <- x at 1.
              now rewrite eqb_nid.
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
          subst x3'.
          constructor; cbn;
          try (rewrite eqb_id);
          try (rewrite eqb_nid; try easy);
          easy.
        }
      }
      {
        exists x3'. split. easy.
        eq_inj H8. eapply EAAccept with
          (n:=v0) (i:=i) (j:=j) (v:=v) (w:=w).
        { specf x2 v0. now rewrite eqb_id in x2. }
        {
          constructor.
          {
            constructor; cbn. easy.
            intros. now rewrite H0.
          }
          {
            cbn. rewrite <- x2, <- x at 1.
            repeat (easy || constructor).
          }
        }
        { easy. }
      }
    }
    {
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
        split.
        {
          constructor.
          {
            easy.
          }
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
          specf x2 v0. rewrite eqb_id in x2.
          symmetry in x2. now apply accepted_done0 in x2.
        }
      }
      {
        exists x3. split. easy.
        eq_inj H4. eapply EAFinish with
          (n:=v0) (i:=i) (j:=i0) (v:=v) (w:=x).
        {
          specf x2 v0. now rewrite eqb_id in x2.
        }
        {
          constructor.
          {
            constructor; cbn. easy.
            intros. now rewrite H0.
          }
          {
            cbn. rewrite <- x2, <- x1 at 1.
            repeat (easy || constructor).
          }
        }
      }
    }
    {
      set (x3' :=
        comRetPoss i
          (comInvPoss i
            x3
            (Exch v)
            (ExchDef {i => v} {}))
          (Exch v)
          (ExchDef {} {})
          None
      ).
      assert (
        VisPossSteps
          x3
          ([] ++
           [(i, CallEv (Exch v))] ++
           [(i, RetEv (Exch v) None)])
          x3'
      ).
      {
        specf x2 v0. rewrite eqb_id in x2.
        symmetry in x2. apply offered1_wait0 in x2.
        rewrite app_assoc.
        apply retStep. apply callStep.
        constructor.
        {
          destruct x2. rewrite state_idle0.
          repeat (easy || constructor).
        }
        {
          cbn. rewrite eqb_id. destruct x2.
          repeat (easy || constructor).
        }
      }
      exists (eq x3').
      split.
      { repeat econstructor. }
      split.
      {
        intros. subst.
        exists x3. split. easy.
        eapply erase_vis.
        exact H2.
      }
      split.
      {
        exists x3'. split. easy.
        split.
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
          subst x3'.
          constructor; cbn;
          now rewrite eqb_id.
        }
      }
      {
        exists x3'. split. easy.
        eq_inj H4. eapply EARevoke
          with (i:=i) (v:=v) (n:=v0).
        {
          constructor.
          {
            constructor; cbn. easy.
            intros. now rewrite H0.
          }
          {
            cbn. rewrite <- x2, <- x at 1.
            repeat (easy || constructor).
          }
        }
        { easy. }
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