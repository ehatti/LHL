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

Require Import FunInd.

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
intros.
induction H.
easy.
simpl.
constructor.
easy.
simpl.
constructor.
easy.
simpl.
constructor.
easy.
simpl.
constructor.
easy.
Qed.

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

Lemma euttTraceThread_app {E F} :
  forall p1 p2 q1 q2 : Trace (ThreadLEvent E F),
  euttThreadTrace p1 q1 ->
  euttThreadTrace p2 q2 ->
  euttThreadTrace (app p1 p2) (app q1 q2).
intros.
induction H.
easy.
simpl.
constructor.
easy.
simpl.
constructor.
easy.
simpl.
constructor.
easy.
simpl.
constructor.
easy.
Qed.

(* Fixpoint interleave {E F} *)

Fixpoint projLSilent {E F} (p : Trace (LEvent E F)) : Trace (Event E + Event F) :=
  match p with
  | nil => nil
  | cons (UEvent (Some e)) p => cons (inl e) (projLSilent p)
  | cons (OEvent e) p => cons (inr e) (projLSilent p)
  | cons _ p => projLSilent p
  end.

Fixpoint projLESilent {E F} (p : Trace (ThreadLEvent E F)) : Trace (ThreadName * (Event E + Event F)) :=
  match p with
  | nil => nil
  | cons (i, UEvent (Some e)) p => cons (i, inl e) (projLESilent p)
  | cons (i, OEvent e) p => cons (i, inr e) (projLESilent p)
  | cons _ p => projLESilent p
  end.

Lemma help21 {A} {x : A} {xs : list A} :
  ~(xs = cons x xs).
unfold not.
intros.
induction xs.
discriminate.
apply IHxs.
dependent destruction H.
easy.
Qed.

Fixpoint nones {E F} n : Trace (LEvent E F) :=
  match n with
  | 0 => nil
  | S n => cons (UEvent None) (nones n)
  end.

Inductive help_view {E F} : Trace (LEvent E F) -> Prop :=
| HelpViewNil :
    help_view nil
| HelpViewNones n :
  help_view (nones n)
| HelpViewEvt n e p :
    help_view p ->
    e <> UEvent None ->
    help_view (app (nones n) (cons e p)).

Lemma get_view {E F} :
  forall p,
  (* p <> cons (UEvent None) nil -> *)
  @help_view E F p.
intros.
induction p.
constructor.
dependent destruction IHp.
destruct a.
destruct ev.
apply HelpViewEvt with (n:=0).
constructor.
easy.
apply HelpViewNones with (n:=1).
apply HelpViewEvt with (n:=0).
constructor.
easy.
destruct a.
destruct ev.
apply HelpViewEvt with (n:=0).
constructor.
easy.
apply HelpViewNones with (n:= S n).
apply HelpViewEvt with (n:=0).
constructor.
easy.
destruct a.
destruct ev.
apply HelpViewEvt with (n:=0).
constructor.
easy.
easy.
easy.
change (UEvent None :: nones n ++ e :: p)%list
with (nones (S n) ++ e :: p)%list.
constructor.
easy.
easy.
apply HelpViewEvt with (n:=0).
constructor.
easy.
easy.
easy.
Qed.

Fixpoint get_nones {E F} i (p : Trace (LEvent E F)) : Trace (ThreadLEvent E F) * Trace (LEvent E F) :=
  match p with
  | nil => (nil, nil)
  | cons (UEvent None) p =>
    let (ns, es) := get_nones i p in
    (cons (i, UEvent None) ns, es)
  | cons _ q => (nil, q)
  end.

Lemma get_nones_beh {E F} :
  forall i n e p,
  e <> UEvent None ->
  @get_nones E F i (app (nones n) (cons e p)) = (List.map (fun e => (i, e)) (nones n), p).
intros.
induction n.
simpl.
destruct e.
destruct ev.
easy.
congruence.
easy.
simpl in *.
rewrite IHn.
easy.
Qed.

Fixpoint interleave {E F}
  (qc : nat -> Trace (LEvent E F))
  (p : Trace (ThreadLEvent E F))
  : Trace (ThreadLEvent E F) :=
  match p with
  | nil => nil
  | cons (i, UEvent None) p => interleave qc p
  | cons (i, e) p =>
    let (ns, q) := get_nones i (qc i) in
    let qc' j := if i =? j then q else qc j in
    app ns (cons (i, e) (interleave qc' p))
  end.

Lemma help22 {E F} :
  forall p q,
  @euttTrace E F (cons (UEvent None) p) q ->
  euttTrace p q.
fix rec 3.
intros.
dependent destruction H.
exact H.
constructor.
apply rec.
exact H.
Qed.

Lemma help23 {E F} :
  forall p q,
  @euttTrace E F p (cons (UEvent None) q) ->
  euttTrace p q.
fix rec 3.
intros.
dependent destruction H.
constructor.
apply rec.
exact H.
apply H.
Qed.

Lemma help23_t {E F} :
  forall p q n,
  @euttTrace E F p (app (nones n) q) ->
  euttTrace p q.
intros.
induction n.
easy.
apply IHn.
simpl in H.
apply help23 in H.
easy.
Qed.

Lemma help31 : forall n : nat, n =? n = true.
intros.
induction n.
easy.
simpl.
f_equal.
easy.
Qed.

Lemma help32 : forall n m : nat, n <> m -> n =? m = false.
fix rec 1.
intros.
destruct n.
destruct m.
easy.
easy.
destruct m.
easy.
simpl in *.
apply rec.
congruence.
Qed.

Lemma euttTraceEvt {E F} :
  forall p q e,
  e <> UEvent None ->
  @euttTrace E F (cons e p) q ->
  exists n r,
    euttTrace p r /\
    q = app (nones n) (cons e r).
intros.
induction q.
destruct e.
destruct ev.
dependent destruction H0.
congruence.
dependent destruction H0.
destruct e.
destruct ev.
destruct a.
destruct ev.
dependent destruction H0.
exists 0, q.
easy.
apply help23 in H0.
apply IHq in H0. clear IHq.
destruct_all.
exists (S x), x0.
split.
easy.
simpl.
subst.
easy.
dependent destruction H0.
congruence.
destruct a.
destruct ev0.
dependent destruction H0.
apply help23 in H0.
apply IHq in H0. clear IHq.
destruct_all.
subst.
eexists (S x), x0.
easy.
dependent destruction H0.
exists 0, q.
easy.
Qed.

Open Scope list.

Axiom excluded_middle : forall P, P \/ ~P.

Lemma beq_comm : forall n m, n =? m = (m =? n).
fix rec 1.
intros.
destruct n.
destruct m.
reflexivity.
reflexivity.
destruct m.
reflexivity.
simpl.
apply rec.
Qed.

Lemma help12 {E F} :
  forall (p : Trace (ThreadLEvent E F)),
  forall (qc : nat -> Trace (LEvent E F)),
  (forall i, euttTrace (projPoint i eqb p) (qc i)) ->
  exists q,
    euttThreadTrace p q /\
    forall i, projPoint i eqb q = qc i.
intros.
exists (interleave qc p).
split.
{
  generalize dependent qc.
  induction p.
  constructor.
  destruct a, l.
  destruct ev.
  2:{
    simpl.
    constructor.
    apply IHp.
    intros.
    specialize (H i).
    simpl in H.
    destruct (i =? n).
    apply help22 in H.
    easy.
    easy.
  }
  {
    intros.
    simpl in *.
    assert (H' := H).
    specialize (H n).
    rewrite help31 in H.
    apply euttTraceEvt in H.
    destruct_all.
    rewrite H0.
    rewrite get_nones_beh.
    change ((n, UEvent (Some e)) :: p)
    with (nil ++ (n, UEvent (Some e)) :: p).
    apply euttTraceThread_app.
    clear.
    induction x.
    constructor.
    simpl.
    constructor.
    easy.
    constructor.
    apply IHp.
    intros.
    specialize (H' i).
    assert (n =? i = (i =? n)) by apply beq_comm.
    rewrite H1. clear H1.
    assert (i = n \/ i <> n) by apply excluded_middle.
    destruct H1.
    subst.
    repeat rewrite help31 in *.
    rewrite H0 in H'.
    apply help23_t in H'.
    dependent destruction H'.
    easy.
    rewrite help32. rewrite help32 in H'.
    easy.
    easy.
    easy.
    easy.
    easy.
  }
  {
    intros.
    simpl in *.
    assert (H' := H).
    specialize (H n).
    rewrite help31 in H.
    apply euttTraceEvt in H.
    destruct_all.
    rewrite H0.
    rewrite get_nones_beh.
    change ((n, OEvent ev) :: p)
    with (nil ++ (n, OEvent ev) :: p).
    apply euttTraceThread_app.
    clear.
    induction x.
    constructor.
    simpl.
    constructor.
    easy.
    constructor.
    apply IHp.
    intros.
    specialize (H' i).
    assert (n =? i = (i =? n)) by apply beq_comm.
    rewrite H1. clear H1.
    assert (i = n \/ i <> n) by apply excluded_middle.
    destruct H1.
    subst.
    repeat rewrite help31 in *.
    rewrite H0 in H'.
    apply help23_t in H'.
    dependent destruction H'.
    easy.
    rewrite help32. rewrite help32 in H'.
    easy.
    easy.
    easy.
    easy.
    easy.
  }
}
{
  intros.
  specialize (H i).
  induction p.
  simpl in *.
}


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

Fixpoint noops {E A} n (p : Prog E A) :=
  match n with
  | 0 => p
  | S n => NoOp (noops n p)
  end.

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
    (forall A (m : F A) c,
      s' = Cont m c ->
      exists n c', c = noops n c') ->
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
  easy.
  constructor.
  easy.
}
generalize dependent (t i).
clear s x t i.
intros t p.
assert (help_view p) by apply get_view.
induction H0.
repeat econstructor.
{
  intros.
  exists nil.
  split.
  clear.
  induction n.
  constructor.
  simpl.
  constructor.
  easy.
  exists s'.
  constructor.
}
intros.
rewrite <- Steps_app in H4.
destruct_all.
dependent destruction H5.
move H3 after st''.
assert (
  exists st''',
    euttTS_ st'' st''' /\
    ThreadStep impl' x e st'''
).
{
  clear H6 H4 IHhelp_view.
  destruct e, ev.
  2: congruence.
  exists st''.
  split.
  apply euttTS_refl.
  easy.
  unfold ThreadStep in *.
  dependent destruction H5.
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
  dependent destruction H5.
  constructor.
  easy.
  easy.
}
destruct_all.
apply IHhelp_view with (s':=x0) in H6.
destruct_all.
assert (
  exists n',
    Steps (ThreadStep impl') s' (nones n') x
).
{
  clear IHhelp_view.
  admit.
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
exact H8.
easy.
{
  intros.
  subst.
  exists 0, c.
  easy.
}
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
intros.
cut (forall E F (p : Trace (ThreadLEvent E F)), projSilent (projUnder p) = projUnderThr p).
{
  intros.
  repeat rewrite <- H0.
  rewrite H.
  easy.
}
intros.
induction p0.
easy.
destruct a, l.
destruct ev.
simpl.
f_equal.
easy.
easy.
easy.
Qed.

Fixpoint projUnderSeq {E F} (p : Trace (LEvent E F)) : Trace (option (Event E)) :=
  match p with
  | nil => nil
  | cons (UEvent e) p => cons e (projUnderSeq p)
  | cons _ p => projUnderSeq p
  end.


Open Scope list.

Inductive assoc_view {E F G} : list (LEvent E F) -> list (LEvent F G) -> list (LEvent E G) -> Prop :=
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

Axiom undef:forall{a},a.

Definition compTS {E F G} (impl : Impl E F) (impl' : Impl F G) (t : ThreadState F G) (s : ThreadState E F) : ThreadState E G.
Admitted.

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
revert H1 H3.
cut (
  forall p q r,
  Steps (ThreadStep impl') (allIdle x3) q (fst x x3) ->
  Steps (ThreadStep impl) (allIdle x3) p (fst (snd x) x3) ->
  exists y,
    Steps (ThreadStep (impl |> impl')) (allIdle x3) r y
).
{
  intros.
  eassert _ by (eapply (H0 _ _ (projPoint x3 eqb tF) H1 H3)).
  easy.
}
intros.
destruct x, p0.
simpl in *.
clear H H' H5 tH tL tF s.
exists (compTS impl impl' (t x3) (t0 x3)).
cut (
  Steps (ThreadStep (impl |> impl')) (allIdle x3) r (compTS impl impl' (t x3) (t0 x3))
).
{
  intros.
  destruct_all.
  easy.
}
assert (
  @allIdle E G x3 = compTS impl impl' (@allIdle F G x3) (@allIdle E F x3)
).
{
  admit.
}
rewrite H. clear H.
generalize dependent (@allIdle E F x3).
generalize dependent (@allIdle F G x3).
eassert (assoc_view p q r) by admit.
induction H; intros.
{
  dependent destruction H0.
  dependent destruction H1.
  constructor.
}
{
  dependent destruction H0.
  unfold ThreadStep in H0.
  dependent destruction H0.
  {
    subst.
    eapply StepsMore with (st'':= compTS impl impl' (Cont m (impl' _ m)) t2).
    econstructor.
    admit.
    admit.
    apply IHassoc_view; easy.
  }
  {
    subst.
    eapply StepsMore with (st'':= compTS impl impl' Idle t2).
    econstructor.
    admit.
    admit.
    apply IHassoc_view; easy.
  }
}
{
  dependent destruction H0.
  dependent destruction H2.
  unfold ThreadStep in H0, H2.
  destruct e.
  {
    dependent destruction H0.
    dependent destruction H2.
  }
}
{
  
  dependent destruction H0.
  unfold ThreadStep in H0.
  dependent destruction H0.
  subst.
  apply IHassoc_view.
}