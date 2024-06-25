From Coq Require Import 
    Init.Nat
    Arith
    FunctionalExtensionality
    PropExtensionality
    Program.Equality
    Lists.List.

From LHL.Util Require Import
  Util
  TransUtil
  Tactics.

From LHL.Core Require Import
    Program
    Specs
    Traces
    Eutt.

(* Basic Trace Properties *)

Lemma nil_IsTraceOfSpec {E} :  
    forall (spec : Spec E),
    IsTraceOfSpec nil spec.
Proof.
    intros. exists spec.(Init). apply TransUtil.StepsNone.
Qed.

Lemma IsTraceOf_iso {E} t spec :
  IsTraceOfSpec (E:=E) t spec ->
  IsTraceOfSpecBwd (to_bwd t) spec.
intros.
destruct H.
exists x.
apply Steps_iso.
easy.
Qed.

Lemma BwdIsTraceOf_iso {E} t spec :
  IsTraceOfSpecBwd (E:=E) (to_bwd t) spec ->
  IsTraceOfSpec t spec.
intros.
destruct H.
exists x.
apply BwdSteps_iso.
easy.
Qed.

(* State Properties *)

(* Step Properties *)

(* overObj and InterStep Properties *)

Lemma decompUnderSteps {E F : ESig} {spec : Spec E} :
  InterUSteps F spec =
  fun s p t =>
    Steps (Step spec) (snd s) (projSilent p) (snd t) /\
    Steps (PointStep UnderThreadStep) (fst s) p (fst t).
extensionality s.
extensionality p.
extensionality t.
apply propositional_extensionality.
split.
{
  intros.
  generalize dependent s.
  induction p; intros.
  dependent destruction H.
  repeat constructor.
  dependent destruction H.
  apply IHp in H0. clear IHp.
  unfold InterUStep in H.
  destruct_all.
  destruct a, o; simpl in *.
  split.
  econstructor.
  exact H2.
  easy.
  econstructor.
  exact H.
  easy.
  split.
  rewrite H2.
  easy.
  econstructor.
  exact H.
  easy.
}
{
  firstorder.
  generalize dependent s.
  induction p.
  intros.
  destruct s, t; simpl in *.
  dependent destruction H.
  dependent destruction H0.
  constructor.
  intros.
  destruct a, o.
  simpl in *.
  dependent destruction H.
  dependent destruction H1.
  eapply StepsMore with (st'':=(st''0, _)).
  2: apply IHp.
  unfold InterUStep.
  split.
  simpl.
  exact H1.
  simpl.
  exact H.
  easy.
  easy.
  simpl in *.
  dependent destruction H0.
  eapply StepsMore with (st'':=(_, _)).
  unfold InterUStep.
  simpl.
  split.
  exact H0.
  easy.
  apply IHp.
  easy.
  easy.
}
Qed.

Fixpoint decompOverObjLift {E F} (p : Trace (ThreadName * option (Event E))) : Trace (ThreadLEvent E F) :=
  match p with
  | nil => nil
  | cons (i, e) p => cons (i, UEvent e) (decompOverObjLift p)
  end.

Lemma projUnderThr_app {E F} {p q : Trace (ThreadLEvent E F)} :
  projUnderThr (p ++ q)%list = (projUnderThr p ++ projUnderThr q)%list.
induction p.
easy.
destruct a, l.
destruct ev.
simpl.
f_equal.
easy.
simpl.
easy.
simpl.
easy.
Qed.

Lemma projOver_app {E F} {p q : Trace (ThreadLEvent E F)} :
  projOver (p ++ q)%list = (projOver p ++ projOver q)%list.
induction p.
easy.
destruct a, l.
simpl.
easy.
simpl.
f_equal.
easy.
Qed.

Lemma projSilent_help {E F} {p : Trace (ThreadName * option (Event E))} :
  projUnderThr (F:=F) (decompOverObjLift p) = projSilent p.
induction p.
easy.
destruct a, o.
simpl.
f_equal.
easy.
simpl.
easy.
Qed.

Inductive IsUnderTrace {E F} : Trace (ThreadLEvent E F) -> Prop :=
| NilUnder :
    IsUnderTrace nil
| ConsUnder i e p :
    IsUnderTrace p ->
    IsUnderTrace (cons (i, UEvent e) p).

Lemma projOverUnder {E F} {p : Trace (ThreadLEvent E F)} :
  IsUnderTrace p ->
  projOver p = nil.
intros.
induction H; easy.
Qed.

Definition IsOverObjTrace {E F} (p : Trace (ThreadLEvent E F)) :=
  p = nil \/ exists i ev p', p = (i, OEvent ev) :: p'.

Lemma projPoint_app {I A} (xs ys : list (I * A)) (eqb : I -> I -> bool) :
  forall i,
  projPoint i eqb (xs ++ ys) = projPoint i eqb xs ++ projPoint i eqb ys.
intros.
induction xs.
easy.
destruct a.
simpl in *.
destruct (eqb i i0).
simpl.
f_equal.
easy.
easy.
Qed.

Inductive overObj_view {E F} : Trace (ThreadLEvent E F) -> Prop :=
| OverObjNil : overObj_view nil
| OverObjCons i e p q :
    IsUnderTrace p ->
    overObj_view q ->
    overObj_view ((i, OEvent e) :: p ++ q).

Lemma get_overObj_view {E F} :
  forall p,
  @IsOverObjTrace E F p ->
  overObj_view p.
intros.
destruct H.
subst.
constructor.
destruct_all.
subst.
induction x1.
apply OverObjCons with (p:=nil); constructor.
dependent destruction IHx1.
destruct a, l.
change ((x, OEvent x0) :: (n, UEvent ev) :: p ++ q)
with ((x, OEvent x0) :: ((n, UEvent ev) :: p) ++ q).
repeat constructor; easy.
apply OverObjCons with (p:=nil); repeat constructor; easy.
Qed.

Lemma decompOverObj {E F} {lay : Layer E F} :
  Steps (Step (overObj lay)) =
  fun s p t =>
    exists (q : Trace (ThreadLEvent E F)),
      p = projOver q /\
      Steps (Step lay.(USpec)) (snd s) (projUnderThr q) (snd t) /\
      Steps (ThreadsStep lay.(LImpl)) (fst s) q (fst t) /\
      IsOverObjTrace q.
extensionality s.
extensionality p.
extensionality t.
apply propositional_extensionality.
split; intros.
{
  induction H.
  {
    exists nil.
    repeat constructor.
  }
  {
    simpl in H.
    destruct_all.
    subst.
    exists ((fst ev, OEvent (snd ev)) :: map (fun e => (fst e, UEvent (snd e))) x1 ++ x).
    repeat split.
    {
      destruct ev.
      simpl.
      f_equal.
      clear H5.
      induction x1; easy.
    }
    {
      simpl.
      rewrite @projUnderThr_app.
      rewrite <- Steps_app.
      exists (snd st'').
      split.
      {
        clear H4 H3 H2 H0 x H.
        generalize dependent (snd st).
        generalize dependent x0.
        induction x1; intros.
        {
          dependent destruction H5.
          simpl.
          constructor.
        }
        {
          dependent destruction H5.
          unfold InterUStep in H.
          destruct_all.
          destruct a, o; simpl in *.
          econstructor.
          exact H0.
          destruct st''0.
          simpl.
          eapply IHx1.
          exact H5.
          subst. simpl.
          destruct st''0.
          simpl.
          eapply IHx1.
          exact H5.
        }
      }
      {
        easy.
      }
    }
    {
      apply StepsMore with (st'':=x0).
      destruct H.
      econstructor; easy.
      rewrite <- Steps_app.
      exists (fst st'').
      split.
      2: easy.
      clear H4 H3 H2 H0 x H.
      generalize dependent x0.
      generalize dependent (snd st).
      induction x1; intros.
      {
        dependent destruction H5.
        constructor.
      }
      {
        simpl in *.
        dependent destruction H5.
        unfold InterUStep in H.
        destruct_all. simpl in *.
        dependent destruction H.
        destruct a, o; simpl in *.
        econstructor.
        econstructor.
        exact H.
        easy.
        destruct st''0.
        simpl.
        eapply IHx1.
        exact H5.
        subst.
        econstructor.
        econstructor.
        simpl.
        exact H.
        easy.
        destruct st''0.
        simpl.
        eapply IHx1.
        exact H5.
      }
    }
    right.
    repeat econstructor.
  }
}
{
  destruct_all.
  subst.
  apply get_overObj_view in H2.
  generalize dependent s.
  induction H2; intros.
  {
    destruct s, t.
    simpl in *.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  }
  {
    simpl in *.
    dependent destruction H1.
    rewrite <- Steps_app in H3.
    rewrite projUnderThr_app in H0.
    rewrite <- Steps_app in H0.
    destruct_all.
    eapply StepsMore with (st'':=(_, _)).
    2:{
      rewrite projOver_app.
      rewrite projOverUnder.
      simpl.
      apply IHoverObj_view.
      simpl.
      exact H5.
      simpl.
      exact H4.
      easy.
    }
    {
      exists st''.
      split.
      dependent destruction H1.
      simpl in *.
      easy.
      exists (projUnder p).
      clear H4 H1 H5 IHoverObj_view.
      generalize dependent s.
      generalize dependent st''.
      induction H; intros.
      {
        simpl in *.
        dependent destruction H3.
        dependent destruction H0.
        constructor.
      }
      {
        destruct e0.
        {
          simpl in *.
          dependent destruction H3.
          dependent destruction H1.
          dependent destruction H0.
          simpl in *.
          eapply StepsMore with (st'':=(_, _)).
          econstructor.
          econstructor.
          simpl.
          exact H0.
          exact H1.
          simpl.
          exact H4.
          change st''1 with (snd (fst s, st''1)).
          apply IHIsUnderTrace.
          easy.
          easy.
        }
        {
          simpl in *.
          dependent destruction H3.
          dependent destruction H0.
          simpl in *.
          eapply StepsMore with (st'':=(_, _)).
          split.
          econstructor.
          exact H0.
          easy.
          easy.
          destruct s.
          change s with (snd (t0, s)).
          apply IHIsUnderTrace.
          easy.
          easy.
        }
      }
    }
  }
}
Qed.

Lemma exProjOver E {F} :
  forall (p : Trace (ThreadEvent F)),
  exists (q : Trace (ThreadLEvent E F)),
  p = projOver q.
intros.
induction p.
exists nil.
easy.
destruct_all.
subst.
destruct a.
eexists (cons (t, OEvent e) x).
simpl.
easy.
Qed.

Lemma projInterSteps {E F} {lay : Layer E F} :
  Steps (Step (overObj lay)) =
  fun s p t =>
    exists q,
      p = projOver q /\
      InterSteps lay.(LImpl) s q t /\
      IsOverObjTrace q.
extensionality s.
extensionality p.
extensionality t.
apply propositional_extensionality.
split; intros.
{
  induction H.
  {
    exists nil.
    repeat constructor.
  }
  {
    simpl in H.
    destruct_all.
    subst.
    eexists ((fst ev, OEvent (snd ev)) :: map (fun e => (fst e, UEvent (snd e))) x1 ++ x).
    repeat split.
    {
      clear.
      destruct ev.
      simpl.
      induction x1; easy.
    }
    {
      eapply StepsMore with (st'':=(_, _)).
      unfold InterStep.
      destruct H.
      simpl in *.
      simpl.
      split.
      2: easy.
      unfold ThreadsStep.
      econstructor.
      simpl.
      exact o.
      easy.
      rewrite <- Steps_app.
      exists st''.
      split.
      {
        clear H3 H2 H0 x.
        induction H4.
        constructor.
        simpl in *.
        econstructor.
        unfold InterUStep in H0.
        unfold InterStep.
        unfold ThreadsStep.
        destruct_all.
        split.
        dependent destruction p.
        econstructor.
        unfold ThreadStep.
        simpl in *.
        exact u.
        easy.
        destruct ev0, o; simpl in *; easy.
        easy.
      }
      {
        easy.
      }
    }
    unfold IsOverObjTrace.
    right.
    repeat econstructor.
  }
}
{
  destruct_all.
  subst.
  apply get_overObj_view in H1.
  generalize dependent s.
  induction H1; intros.
  {
    dependent destruction H0.
    constructor.
  }
  {
    dependent destruction H0.
    rewrite <- Steps_app in H2.
    destruct_all.
    simpl.
    apply StepsMore with (st'':=x).
    exists (fst st'').
    split.
    simpl.
    unfold InterStep in H0.
    destruct_all.
    unfold ThreadsStep in H0.
    dependent destruction H0.
    simpl in *.
    econstructor.
    exact H0.
    easy.
    exists (projUnder p).
    {
      clear IHoverObj_view H3.
      destruct H0.
      unfold StateStep in H3.
      simpl in *.
      rewrite H3. clear H3 H0 s.
      assert ((fst st'', snd st'') = st'') by (destruct st''; easy).
      rewrite H0. clear H0 H1.
      generalize dependent st''.
      induction p; intros.
      {
        dependent destruction H2.
        constructor.
      }
      {
        dependent destruction H.
        simpl.
        dependent destruction H2.
        destruct H0.
        dependent destruction H0.
        simpl in *.
        econstructor.
        unfold InterUStep.
        split.
        econstructor.
        exact H0.
        easy.
        destruct e0; easy.
        apply IHp.
        easy.
        easy.
      }
    }
    rewrite projOver_app.
    rewrite projOverUnder.
    simpl.
    apply IHoverObj_view.
    easy.
    easy.
  }
}
Qed.

Lemma decompSplitSteps {A B E} (stepL : A -> E -> A -> Prop) (stepR : B -> E -> B -> Prop) :
  Steps
    (fun s e t =>
      stepL (fst s) e (fst t) /\
      stepR (snd s) e (snd t)) =
  fun s p t =>
    Steps stepL (fst s) p (fst t) /\
    Steps stepR (snd s) p (snd t).
extensionality s.
extensionality p.
extensionality t.
apply propositional_extensionality.
split.
intros.
generalize dependent s.
induction p.
intros.
dependent destruction H.
repeat constructor.
intros.
dependent destruction H.
apply IHp in H0.
destruct_all.
split.
econstructor.
exact H.
easy.
econstructor.
exact H2.
easy.
intros.
generalize dependent s.
induction p.
intros.
destruct_all.
destruct s, t.
simpl in *.
dependent destruction H.
dependent destruction H0.
econstructor.
intros.
destruct_all.
dependent destruction H.
dependent destruction H1.
eapply StepsMore with (st'':=(st'', st''0)).
easy.
apply IHp.
easy.
Qed.

Lemma other_inter {E F} {spec : Spec E} {impl : Impl E F} :
  forall p t i s,
  OtherSteps (spec:=spec) i impl s p t ->
  InterSteps impl s p t.
intros p t i.
induction p; cbn; intros.
dependent destruction H. constructor.
dependent destruction H. destruct_all.
apply IHp in H0.
econstructor. exact H1. easy.
Qed.

(* Eutt *)

Inductive euttTS_ {E F : ESig} :
    ThreadState E F -> ThreadState E F -> Prop :=
| euttTS_Idle : euttTS_ Idle Idle
| euttTS_Cont A m (p p' : Prog E A) : 
    eutt p p' -> 
    euttTS_ (Cont m p) (Cont m p')
| euttTS_UCall A B om um (k k' : A -> Prog E B) : 
    (forall (x : A), eutt (k x) (k' x)) ->
    euttTS_ (UCall om um k) (UCall om um k').

Definition euttTS {E F : ESig} :
    ThreadsSt E F -> ThreadsSt E F -> Prop :=
    fun ths ths' => forall (i : ThreadName), euttTS_ (ths i) (ths' i).

Definition euttIS {A E F} :
    ThreadsSt E F * A -> ThreadsSt E F * A -> Prop :=
        fun ost ost' => euttTS (fst ost) (fst ost') /\ (snd ost = snd ost').
        
(* Lemma eutt_InterStep {E F} (RR : IRel E E) (spec : Spec E) (impl : Impl E F) (impl' : Impl E F): 
    euttImpl RR impl impl' ->
    forall i ist0 ev ist1 ist0',
        euttIS (A := spec.(State)) RR ist0 ist0' ->
        InterStep (impl := impl) i ist0 ev ist1 ->
        exists ist1' ev',
            (ev' = ev  /\ InterStep (impl := impl') i ist0' ev' ist1' /\ euttIS RR ist1 ist1')
        \/  (ev' = (i, Silent) /\ InterStep (impl := impl') i ist0' ev' ist1' /\ euttIS RR ist0 ist1').
Proof.
    intros. remember H1. destruct H1.
    - (* OCall *) 
      unfold euttIS, euttTS in H0. destruct H0.
      pose (EUTTSI := (H0 i)).
      inversion EUTTSI. 
      pose (thst1' := (updt_thst (fst ist0') i (Cont m (impl' R m)))).
      pose (ist1' := (thst1', st)).
      exists ist1'. exists (i, OCallEv m).
      left; repeat split.
      + (* InterStep *)
        symmetry in H4.
        assert (thst1' i = Cont m (impl' R m)) by eapply updt_istate_i_eq_st.
        assert (differ_pointwise (fst ist0') thst1' i) by eapply updt_istate_pointwise.
        assert (ist0' = (fst ist0', st)) by (destruct ist0'; simpl in H1; rewrite H1; simpl; reflexivity).
        rewrite H6. pose (step' := IOCall (st := st) H4 H2 H5). apply step'.
      + (* Still eutt *)
        unfold euttTS. intro j. simpl.
        pose (Nat.eq_dec j i).
        destruct s.
        (* i = j *)
        assert (thst1' i = Cont m (impl' R m)) by eapply updt_istate_i_eq_st.
        subst. rewrite e0. rewrite H2.
        constructor. unfold euttImpl in H. apply H.
        (* i <> j *)
        pose (H0 j). simpl in e1. 
        assert (differ_pointwise (fst ist0') thst1' i) by eapply updt_istate_pointwise.
        rewrite (H2 j n). rewrite (d j n). assumption.   
Admitted.

Lemma euttTS_isPathOf {E F} (spec : Spec E) : 
    forall (impl : Impl E F) (impl' : Impl E F),
    forall t thst0 thst1 thst0', 
        euttIS ieq thst0 thst0' ->
        IsPathOf thst0 t thst1 (Steps (overObj (spec :> impl)).(Step)) ->
        exists thst1',  
            IsPathOf thst0' t thst1' (Steps (overObj (spec :> impl')).(Step)).
Admitted. *)