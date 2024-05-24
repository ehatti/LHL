From LHL.Util Require Import
  Util
  TransUtil
  Tactics.

From LHL.Core Require Import
  Program
  ProgramFacts
  Specs
  Traces
  TracesFacts
  Eutt.

From Coq Require Import
  Program.Equality
  Relations.Relation_Operators
  Logic.PropExtensionality
  Logic.FunctionalExtensionality
  Logic.ClassicalChoice
  Init.Nat
  Arith.EqNat
  Arith.PeanoNat.

From Paco Require Import
  paco.

Lemma threadDecEq : @IsEqDec ThreadName eqb.
Admitted.

(* Basic Refinement Properties *)

Lemma layerRefines_trans {E1 E2 E3 F} :
  forall (lay1 : Layer E1 F) (lay2 : Layer E2 F) (lay3 : Layer E3 F),
    layerRefines lay1 lay2 -> layerRefines lay2 lay3 ->
    layerRefines lay1 lay3.
Proof.
  intros. unfold layerRefines, specRefines in *.
  eapply TransUtil.Incl_trans.
  apply H. apply H0.
Qed.

(* Eutt implies refinement *)

Lemma help_eq :
  forall n,
  Nat.eqb n n = true.
intros.
induction n.
easy.
simpl.
easy.
Qed.


Lemma floatEx {A} {B C : A -> Prop} :
  (forall x, B x -> C x) ->
  (exists x, B x) -> (exists x, C x).
intros.
destruct_all.
exists x.
apply H.
easy.
Qed.

Inductive euttTrace {E F} : Trace (LEvent E F) -> Trace (LEvent E F) -> Prop :=
| EuttTraceNil :
    euttTrace nil nil
| EuttTraceLSilent p q :
    euttTrace p q ->
    euttTrace (cons (UEvent None) p) q
| EuttTraceRSilent p q :
    euttTrace p q ->
    euttTrace p (cons (UEvent None) q)
| EuttTraceUnder p q e :
    euttTrace p q ->
    euttTrace (cons (UEvent (Some e)) p) (cons (UEvent (Some e)) q)
| EuttTraceOver p q e :
    euttTrace p q ->
    euttTrace (cons (OEvent e) p) (cons (OEvent e) q).

Lemma euttTrace_app {E F} :
  forall p1 p2 q1 q2 : Trace (LEvent E F),
  euttTrace p1 q1 ->
  euttTrace p2 q2 ->
  euttTrace (app p1 p2) (app q1 q2).
Admitted.

Inductive euttThreadTrace {E F} : Trace (ThreadLEvent E F) -> Trace (ThreadLEvent E F) -> Prop :=
| EuttTraceThreadNil :
    euttThreadTrace nil nil
| EuttTraceThreadLSilent i p q :
    euttThreadTrace p q ->
    euttThreadTrace (cons (i, UEvent None) p) q
| EuttTraceThreadRSilent i p q :
    euttThreadTrace p q ->
    euttThreadTrace p (cons (i, UEvent None) q)
| EuttTraceThreadUnder i p q e :
    euttThreadTrace p q ->
    euttThreadTrace (cons (i, UEvent (Some e)) p) (cons (i, UEvent (Some e)) q)
| EuttTraceThreadOver i p q e :
    euttThreadTrace p q ->
    euttThreadTrace (cons (i, OEvent e) p) (cons (i, OEvent e) q).

(* Lemma compEuttTrace *)

Lemma help12 {E F} :
  forall (p : Trace (ThreadLEvent E F)),
  forall (qc : nat -> Trace (LEvent E F)),
  (forall i, euttTrace (projPoint i eqb p) (qc i)) ->
  exists q,
    euttThreadTrace p q /\
    forall i, projPoint i eqb q = qc i.
Admitted.

Lemma euttOver {E F} :
  forall (p q : Trace (ThreadLEvent E F)),
  euttThreadTrace p q ->
  projOver p = projOver q.
intros.
induction H.
easy.
easy.
easy.
easy.
simpl.
f_equal.
easy.
Qed.

Fixpoint nones {E F} n : Trace (LEvent E F) :=
  match n with
  | 0 => nil
  | S n => cons (UEvent None) (nones n)
  end.

Lemma euttTrace_nones {E F} :
  forall n m,
  @euttTrace E F (nones n) (nones m).
intros.
induction n.
induction m.
constructor.
constructor.
easy.
constructor.
easy.
Qed.

Inductive help_view {E F} : Trace (LEvent E F) -> Prop :=
| HelpViewNil :
    help_view nil
| HelpViewEvt n e p :
    help_view p ->
    e <> UEvent None ->
    help_view (app (nones n) (cons e p)).

Lemma get_view {E F} :
  forall p,
  @help_view E F p.
Admitted.

Lemma euttTS_refl {E F} :
  forall s, @euttTS_ E F s s.
intros.
destruct s.
constructor.
constructor.
apply Reflexive_eutt_ieq.
constructor.
intros.
apply Reflexive_eutt_ieq.
Qed.

Lemma state_finite {E F} {impl impl' : Impl E F} :
  forall s s' t n,
    ~(exists A (m : F A) p, t = Cont m (NoOp p)) ->
    euttTS_ s s' ->
    Steps (ThreadStep impl) s (nones n) t ->
    exists n', Steps (ThreadStep impl') s' (nones n') t.
Admitted.

Theorem eutt_layerRefines {E F} : 
  forall (spec : Spec E) (impl impl' : Impl E F), 
  euttImpl impl impl' -> 
  layerRefines (spec :> impl) (spec :> impl').
unfold euttImpl, layerRefines, specRefines, Incl, IsTraceOfSpec, Steps.
intros.
destruct_all.
destruct x.
repeat rewrite projInterSteps in *.
destruct_all.
subst.
simpl .
unfold InterSteps, InterStep in *.
simpl in *.
unfold InterState in *.
repeat rewrite decompSplitSteps in *.
simpl in *.
destruct_all.
cut (
  forall i, exists q : Trace (LEvent E F),
    euttTrace (projPoint i eqb x) q /\
    exists stf,
      Steps (ThreadStep impl') (allIdle i) q stf
).
intros.
{
  apply choice in H2.
  destruct_all.
  assert (forall i, euttTrace (projPoint i eqb x) (x0 i)).
  intros.
  specialize (H2 i).
  easy.
  assert (
    forall i, exists stf,
      Steps (ThreadStep impl') (allIdle i) (x0 i) stf
  ).
  intros.
  specialize (H2 i).
  easy.
  clear H2.
  apply choice in H4.
  destruct_all.
  apply help12 in H3.
  destruct_all.
  assert (
    forall i,
      Steps (ThreadStep impl') (allIdle i) (projPoint i eqb x2) (x1 i)
  ).
  intros.
  specialize (H4 i).
  specialize (H2 i).
  rewrite <- H4 in H2.
  easy.
  clear H2.
  rewrite <- (decompPointSteps eqb (ThreadStep impl')) in H5.
  2: exact threadDecEq.
  eexists (x1, s), x2.
  repeat split.
  apply euttOver.
  easy.
  easy.
  {
    simpl in *.
    clear H5 x1 H4 x0 H0.
    generalize dependent (Init spec).
    induction H3.
    easy.
    intros.
    dependent destruction H1.
    unfold StateStep in H0.
    simpl in *.
    subst.
    apply IHeuttThreadTrace.
    easy.
    intros.
    econstructor.
    unfold StateStep.
    easy.
    apply IHeuttThreadTrace.
    easy.
    intros.
    dependent destruction H1.
    econstructor.
    exact H0.
    apply IHeuttThreadTrace.
    easy.
    intros.
    dependent destruction H1.
    unfold StateStep in H0.
    simpl in *.
    subst.
    econstructor.
    unfold StateStep.
    easy.
    apply IHeuttThreadTrace.
    easy.
  }
}
clear H1.
rewrite (decompPointSteps eqb (ThreadStep impl)) in H0.
2: exact threadDecEq.
intros.
specialize (H0 i).
revert H0.
cut (
  forall p s s',
    euttTS_ s s' ->
    Steps (ThreadStep impl) s p (t i) ->
    exists q,
      euttTrace p q /\
      exists stf,
        Steps (ThreadStep impl') s' q stf
).
{
  intros.
  apply H0 with (s:=Idle).
  constructor.
  easy.
}
generalize dependent (t i).
clear s x t i.
intros t p.
assert (help_view p) by apply get_view.
induction H0.
repeat econstructor.
intros.
rewrite <- Steps_app in H3.
destruct_all.
dependent destruction H4.
move H3 after st''.
assert (
  exists st''',
    euttTS_ st'' st''' /\
    ThreadStep impl' x e st'''
).
{
  clear H5 H3 IHhelp_view.
  destruct e, ev.
  2: congruence.
  exists st''.
  split.
  apply euttTS_refl.
  easy.
  unfold ThreadStep in *.
  dependent destruction H4.
  exists (Cont m (impl' _ m)).
  split.
  constructor.
  apply H.
  constructor.
  easy.
  easy.
  exists st''.
  split.
  apply euttTS_refl.
  unfold ThreadStep in *.
  dependent destruction H4.
  constructor.
  easy.
  easy.
}
destruct_all.
apply IHhelp_view with (s':=x0) in H5.
destruct_all.
assert (
  exists n',
    Steps (ThreadStep impl') s' (nones n') x
).
{
  eapply state_finite.
  unfold ThreadStep in H4.
  unfold not.
  intros.
  destruct e.
  dependent destruction H4.
  destruct_all.
  subst.
  discriminate.
  destruct_all.
  subst.
  discriminate.
  congruence.
  destruct_all.
  subst.
  dependent destruction H4.
  exact H2.
  exact H3.
}
destruct_all.
eexists (nones x3 ++ e :: x1)%list.
split.
apply euttTrace_app.
apply euttTrace_nones.
destruct e, ev.
constructor.
easy.
congruence.
constructor.
easy.
constructor.
easy.
exists x2.
rewrite <- Steps_app.
exists x.
split.
easy.
econstructor.
exact H7.
easy.
easy.
Qed.

(* Crucial Refinement Properties *)

Lemma help {E F} :
  forall (p : Trace (ThreadLEvent E F)),
  projSilent (projUnder p) = projUnderThr p.
intros.
induction p.
easy.
destruct a, l, ev.
simpl.
rewrite IHp.
all: easy.
Qed.

Lemma projUnderSteps {E F} {lay : Layer E F} :
  forall s p t,
  BwdSteps (Step (overObj lay)) s p t ->
  exists q,
  BwdSteps (Step lay.(USpec)) (snd s) q (snd t).
intros.
generalize dependent t.
induction p.
intros.
dependent destruction H.
exists Start.
constructor.
intros.
dependent destruction H.
apply IHp in H.
simpl in H0.
destruct_all.
eexists.
eapply BwdSteps_app.
exact H.
rewrite decompUnderSteps in H0.
destruct_all.
rewrite <- H2.
apply Steps_iso in H0.
exact H0.
Qed.

Theorem mkLayer_monotonic {E F} :
  forall (spec spec' : Spec E) (impl : Impl E F),
  specRefines spec' spec -> 
  layerRefines (spec' :> impl) (spec :> impl).
unfold layerRefines, specRefines, Incl, IsTraceOfSpec.
intros.
destruct_all.
repeat rewrite decompOverObj in *.
destruct_all.
subst.
simpl in *.
eassert (exists st, Steps _ _ _ st).
exists (snd x).
exact H1.
apply H in H0.
destruct_all.
eexists (fst x, x1).
exists x0.
split.
easy.
simpl.
split.
easy.
easy.
Qed.

Lemma help3 {A} {xs : list A} {x : A} :
  to_bwd (app xs (cons x nil)) = Snoc (to_bwd xs) x.
induction xs.
easy.
simpl.
rewrite IHxs.
clear IHxs.
destruct xs; easy.
Qed.

Fixpoint projOver_bwd {E F} (p : bwd_list (ThreadLEvent E F)) : bwd_list (ThreadEvent F) :=
  match p with
  | Start => Start
  | Snoc p (i, OEvent e) => Snoc (projOver_bwd p) (i, e)
  | Snoc p _ => projOver_bwd p
  end.

Lemma full_trace {E F G} :
  forall (p : Trace (ThreadLEvent E F)) (q : Trace (ThreadLEvent F G)),
  projOver p = projUnderThr q ->
  exists (r : Trace (ThreadLEvent E G)),
    projUnder r = projUnder p /\
    projOver r = projOver q.
Admitted.

Lemma swapEx {A B} {P : A -> B -> Prop} :
  (exists x y, P x y) ->
  (exists y x, P x y).
firstorder.
Qed.

Lemma takeThr {E F G} :
  forall (p : Trace (ThreadLEvent E F)) (q : Trace (ThreadLEvent E G)),
    projUnder p = projUnder q ->
    projUnderThr p = projUnderThr q.
Admitted.

Fixpoint projUnderSeq {E F} (p : Trace (LEvent E F)) : Trace (option (Event E)) :=
  match p with
  | nil => nil
  | cons (UEvent e) p => cons e (projUnderSeq p)
  | cons _ p => projUnderSeq p
  end.

Open Scope list.

Inductive assoc_view {E F G} : Trace (LEvent E F) -> Trace (LEvent F G) -> Trace (LEvent E G) -> Prop :=
| AVNil :
    assoc_view nil nil nil
| AVGEv e tL tH tF :
    assoc_view tL tH tF ->
    assoc_view tL (OEvent e :: tH) (OEvent e :: tF)
| AVFEv e tL tH tF :
    assoc_view tL tH tF ->
    assoc_view (OEvent e :: tL) (UEvent (Some e) :: tH) tF
| AVFSl tL tH tF :
    assoc_view tL tH tF ->
    assoc_view tL (UEvent None :: tH) tF
| AVEEv e tL tH tF :
    assoc_view tL tH tF ->
    assoc_view (UEvent e :: tL) tH (UEvent e :: tF).

Theorem layerRefines_VComp_assoc {E F G} : 
  forall  (spec : Spec E) (impl : Impl E F) (impl' : Impl F G),
    layerRefines ((overObj (spec :> impl)) :> impl') ((spec :> impl) :|> impl').
unfold layerRefines, specRefines, Incl, IsTraceOfSpec.
intros.
destruct_all.
repeat rewrite decompOverObj in *.
destruct_all.
subst.
simpl (USpec (overObj (spec :> impl) :> impl')) in H0.
rewrite decompOverObj in H0.
destruct_all.
simpl in *.
symmetry in H.
assert (H' := H).
apply full_trace in H.
destruct_all.
apply swapEx.
exists x2.
move H' after H5.
repeat (unfold InterState in *; simpl in *).
cut (
  exists st : ThreadsSt E G,
    Steps (ThreadsStep (impl |> impl')) allIdle x2 st
).
{
  intros.
  destruct_all.
  exists (x3, snd (snd x)).
  repeat split; try easy.
  simpl.
  apply takeThr in H.
  rewrite H.
  easy.
  apply isOverObjTrace.
}
unfold ThreadsSt.
unfold ThreadsStep in *.
cut (
  exists st, forall i,
    (fun i sti =>
      Steps (ThreadStep (impl |> impl')) (allIdle i) (projPoint i eqb x2) sti)
    i (st i)
).
{
  intros.
  destruct_all.
  exists x3.
  rewrite (decompPointSteps eqb (ThreadStep (impl |> impl'))).
  easy.
  exact threadDecEq.
}
rewrite (decompPointSteps eqb (ThreadStep impl)) in H3.
2: exact threadDecEq.
rewrite (decompPointSteps eqb (ThreadStep impl')) in H1.
2: exact threadDecEq.
apply choice.
intros.
specialize (H3 x3).
specialize (H1 x3).
move H4 before H2.
rename x1 into tL.
rename x0 into tH.
rename x2 into tF.
clear H4 H2 H0.
assert (assoc_view (projPoint x3 eqb tL) (projPoint x3 eqb tH) (projPoint x3 eqb tF)).
admit.
revert H0 H1 H3.
cut (
  forall p q r,
  assoc_view p q r ->
  Steps (ThreadStep impl') (allIdle x3) q (fst x x3) ->
  Steps (ThreadStep impl) (allIdle x3) p (fst (snd x) x3) ->
  exists y,
    Steps (ThreadStep (impl |> impl')) (allIdle x3) r y
).
intros.
eapply H0.
exact H1.
easy.
easy.
intros.
destruct x, p0.
simpl in *.
clear H H' H5 tH tL tF s.
induction H0.
repeat econstructor.
apply IHassoc_view in H2. clear IHassoc_view.
destruct_all.
exists x.
dependent destruction H1.
econstructor.