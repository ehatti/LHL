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
  Logic.FunctionalExtensionality.
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
      (Done j (Exch w) (Some v) x \/
       PIdle j x);
  ths_faithful :
    forall n m i j v w,
      (contains (i, v) (pendSet s n) /\
       contains (j, w) (pendSet s m)) ->
      i <> j \/
      (i = j /\
       (doneSet s n <> {} \/
        doneSet s m <> {}))
  (* ths_faithful :
    ~(exists n m i v w,
      n <> m /\
      contains (i, v) (pendSet s n) /\
      contains (i, w) (pendSet s m)) *)
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

Ltac contr := unfold not at 1; intros.

Lemma specf {A B} {f g : A -> B} :
  f = g ->
  forall x,
  f x = g x.
intros. now rewrite H.
Qed.

Ltac specf H v := apply specf with (x:=v) in H.

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
{
  intros.
  assert ((i, v) ∈ pendSet s n /\ (j, w) ∈ pendSet s m).
  { now rewrite H0. }
  apply ths_faithful0 in H1.
  now rewrite H0 in H1.
}
Qed.

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
        {
          rename v0 into k.
          symmetry in x. rename x into H13.
          symmetry in x2. rename x2 into H14.
          assert (
            exchSt s k = ExchDef {} {} /\
            exchSt t k = ExchDef {i => v} {} /\
            differ_pointwise (RState (snd s)) (RState (snd t)) k
          ).
          {
            rewrite H13, H14 at 1.
            specf H13 k. specf H14 k.
            rewrite H13, H14 at 1.
            rewrite eqb_id.
            repeat (split || easy).
            unfold differ_pointwise.
            intros. now rewrite eqb_nid.
          }
          clear H13 H14. psimpl.
          intros. psimpl.
          dec_eq_nats n k.
          {
            rewrite H9 in H at 1.
            apply contains_invert in H.
            destruct H. ddestruct H.
            2: now apply contains_contr in H.
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
        {
          admit.
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
    destruct H3.
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
          rewrite state_idle0. destruct H7.
          repeat (easy || constructor).
        }
        {
          cbn. rewrite eqb_nid. destruct H8.
          repeat (easy || constructor). easy.
        }
        {
          cbn. rewrite eqb_id, eqb_nid.
          destruct H7. rewrite insert_perm.
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
        exact H7.
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
            assert (i0 <> j).
            {
              contr. subst.
              assert (
                j <> j \/ j = j /\ (doneSet s n <> {} \/ doneSet s v0 <> {})
              ).
              {
                apply ths_faithful0 with
                  (v:=v1) (w:=w).
                split.
                {
                  specf x2 n. specf x n.
                  rewrite eqb_nid in *.
                  all: try easy.
                  rewrite <- x2, x, H8 at 1.
                  apply contains_triv.
                }
                {
                  specf x2 v0. rewrite eqb_id in x2.
                  rewrite <- x2, insert_perm at 1.
                  apply contains_triv.
                }
              }
              destruct H10. easy.
              psimpl. clear H10.
              destruct H11.
              {
                specf x2 n. specf x n.
                rewrite eqb_nid in *. all: try easy.
                now rewrite <- x2, x, H8 in H10 at 1.
              }
              {
                specf x2 v0. rewrite eqb_id in x2.
                now rewrite <- x2 in H10.
              }
            }
            assert (i0 <> i).
            {
              contr. subst.
              assert (
                i <> i \/ i = i /\ (doneSet s n <> {} \/ doneSet s v0 <> {})
              ).
              {
                apply ths_faithful0 with
                  (v:=v1) (w:=v).
                split.
                {
                  specf x2 n. specf x n.
                  rewrite eqb_nid in *.
                  all: try easy.
                  rewrite <- x2, x, H8 at 1.
                  apply contains_triv.
                }
                {
                  specf x2 v0. rewrite eqb_id in x2.
                  rewrite <- x2 at 1. apply contains_triv.
                }
              }
              destruct H11. easy.
              psimpl. clear H11.
              destruct H12.
              {
                specf x2 n. specf x n.
                rewrite eqb_nid in *. all: try easy.
                now rewrite <- x2, x, H8 in H10 at 1.
              }
              {
                specf x2 v0. rewrite eqb_id in x2.
                now rewrite <- x2 in H10.
              }
            }
            specf x2 n. specf x n.
            rewrite eqb_nid in *; try easy.
            rewrite <- x, x2 in H8 at 1.
            apply offered1_wait0 in H8.
            destruct H8.
            constructor; cbn;
            now repeat rewrite eqb_nid.
          }
          {
            admit.
          }
          {
            admit.
          }
          {
            contr. destruct H8 as [n [m [l [v' [w']]]]].
            psimpl.
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
        eq_inj H7. eapply EAFinish with
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
        eq_inj H7. eapply EARevoke
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