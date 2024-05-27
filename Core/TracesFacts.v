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
  InterUSteps (F:=F) (spec:=spec) =
  fun s p t =>
    Steps (Step spec) (snd s) (projSilent p) (snd t) /\
    Steps (PointStep UnderThreadStep) (fst s) p (fst t).
extensionality s.
extensionality p.
extensionality t.
apply propositional_extensionality.
Admitted.

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

Inductive IsOverObjTrace {E F} : Trace (ThreadLEvent E F) -> Prop :=
| NilOverObj : IsOverObjTrace nil
| ConsOverObj i e p q :
    IsUnderTrace p ->
    IsOverObjTrace q ->
    IsOverObjTrace (p ++ cons (i, OEvent e) q)%list.

Lemma isOverObjTrace {E F} :
  forall p, @IsOverObjTrace E F p.
Admitted.

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
firstorder.
{
  generalize dependent s.
  induction p.
  exists nil.
  split.
  easy.
  dependent destruction H.
  constructor.
  intros.
  constructor.
  split.
  constructor.
  constructor.
  intros.
  dependent destruction H.
  apply IHp in H0. clear IHp.
  simpl in H.
  destruct_all.
  rewrite decompUnderSteps in H.
  subst. simpl in *.
  destruct_all.
  eexists (decompOverObjLift x1 ++ cons (fst a, OEvent (snd a)) x)%list.
  split.
  clear.
  induction x1.
  destruct a.
  easy.
  rewrite IHx1.
  destruct a0.
  simpl.
  easy.
  split.
  rewrite projUnderThr_app.
  rewrite <- Steps_app.
  eexists.
  split.
  2: exact H1.
  rewrite H5 in *.
  rewrite projSilent_help.
  easy.
  split.
  rewrite <- Steps_app.
  exists (fst x0).
  split.
  clear H3 H5 H2 H1 x H4 H3 H st'' t a.
  induction H0.
  constructor.
  destruct ev.
  simpl.
  econstructor.
  destruct H.
  simpl in *.
  econstructor.
  simpl.
  exact u.
  easy.
  easy.
  simpl.
  econstructor.
  destruct H4.
  econstructor.
  simpl.
  exact o.
  intros.
  apply e.
  easy.
  easy.
  clear H2 H1 H5 H4 H0 H x0 st'' s t.
  assert (IsUnderTrace (F:=F) (decompOverObjLift x1)).
  clear.
  induction x1.
  constructor.
  destruct a.
  simpl.
  econstructor.
  easy.
  econstructor.
  easy.
  easy.
}
{
  subst.
  generalize dependent s.
  induction H2.
  destruct s, t.
  simpl in *.
  intros.
  dependent destruction H0.
  dependent destruction H1.
  constructor.
  intros.
  rewrite <- Steps_app in H1.
  rewrite projUnderThr_app in H0.
  rewrite <- Steps_app in H0.
  destruct_all.
  rewrite projOver_app.
  rewrite projOverUnder.
  simpl.
  dependent destruction H3.
  eapply StepsMore with (st'':=(st'', x0)).
  exists (x, x0).
  exists (projUnder p).
  split.
  {
    rewrite decompUnderSteps.
    split.
    simpl.
    assert (projSilent (projUnder p) = projUnderThr p).
    clear.
    induction p.
    constructor.
    destruct a, l.
    destruct ev.
    simpl.
    f_equal.
    easy.
    easy.
    easy.
    rewrite H6.
    easy.
    clear IHIsOverObjTrace H3 H2 H0 H4.
    simpl in *.
    generalize dependent s.
    induction H.
    simpl in *.
    intros.
    dependent destruction H1.
    constructor.
    simpl.
    intros.
    dependent destruction H1.
    econstructor.
    dependent destruction H0.
    simpl in *.
    split.
    simpl.
    exact t0.
    easy.
    specialize (IHIsUnderTrace (st''0, x0)).
    apply IHIsUnderTrace.
    easy.
  }
  split.
  unfold InterOStep.
  simpl.
  unfold ThreadsStep in *.
  dependent destruction H3.
  simpl in *.
  econstructor.
  easy.
  easy.
  easy.
  apply IHIsOverObjTrace.
  easy.
  easy.
  easy.
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
      InterSteps lay.(LImpl) s q t.
extensionality s.
extensionality p.
extensionality t.
apply propositional_extensionality.
firstorder.
{
  generalize dependent s.
  induction p.
  exists nil.
  dependent destruction H.
  repeat constructor.
  intros.
  dependent destruction H.
  apply IHp in H0. clear IHp.
  simpl in *.
  destruct_all.
  subst.
  destruct a.
  eexists (map (fun e => (fst e, UEvent (snd e))) x1 ++ (t0, OEvent e) :: x).
  split.
  clear.
  induction x1.
  easy.
  simpl.
  rewrite IHx1.
  easy.
  unfold InterSteps.
  rewrite <- Steps_app.
  exists x0.
  split.
  clear H1 x H2.
  generalize dependent s.
  induction x1.
  intros.
  dependent destruction H.
  constructor.
  intros.
  dependent destruction H.
  apply IHx1 in H0. clear IHx1.
  simpl.
  econstructor.
  2: exact H0.
  clear H0.
  unfold InterUStep, InterStep in *.
  destruct_all.
  split.
  dependent destruction H.
  all: simpl in *.
  econstructor.
  simpl.
  easy.
  easy.
  easy.
  econstructor.
  unfold InterStep, InterOStep in *.
  simpl in *.
  split.
  2: exact H3.
  dependent destruction H2.
  econstructor.
  easy.
  easy.
  easy.
}
{
  subst.
  assert (IsOverObjTrace x) by apply isOverObjTrace.
  generalize dependent s.
  induction H.
  intros.
  dependent destruction H0.
  constructor.
  intros.
  unfold InterSteps in H1.
  rewrite <- Steps_app in H1.
  destruct_all.
  dependent destruction H2.
  apply IHIsOverObjTrace in H3.
  clear IHIsOverObjTrace.
  rewrite projOver_app.
  rewrite projOverUnder.
  2: easy.
  simpl.
  eapply StepsMore with (st'':=st'').
  eexists x, (projUnder p).
  split.
  clear H3 H2.
  generalize dependent s.
  induction H.
  intros.
  dependent destruction H1.
  constructor.
  intros.
  dependent destruction H1.
  apply IHIsUnderTrace in H2.
  clear IHIsUnderTrace.
  apply StepsMore with (st'':=st''0).
  clear H2.
  {
    unfold InterStep, InterUStep in *.
    destruct_all.
    simpl in *.
    split.
    2: easy.
    dependent destruction H1.
    simpl in *.
    econstructor.
    easy.
    easy.
  }
  exact H2.
  clear H3 H1.
  unfold InterStep, InterOStep in *.
  simpl in *.
  destruct_all.
  split.
  {
    dependent destruction H1.
    simpl in *.
    econstructor.
    easy.
    easy.
  }
  easy.
  easy.
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


(* Eutt *)

Inductive euttTS_ {E F : ESig} :
    ThreadState E F -> ThreadState E F -> Prop :=
| euttTS_Idle : euttTS_ Idle Idle
| euttTS_Cont A m (p p' : Prog E A) : 
    eutt p p' -> 
    euttTS_ (Cont m p) (Cont m p')
| euttTS_UCall A B m (k k' : A -> Prog E B) : 
    (forall (x : A), eutt (k x) (k' x)) ->
    euttTS_ (UCall m k) (UCall m k').

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