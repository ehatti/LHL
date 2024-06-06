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
  Eutt
  Simulates
  SimulatesFacts
  EuttRefinesSetup.

From Coq Require Import
  Program.Equality
  Relations.Relation_Operators
  Logic.PropExtensionality
  Logic.FunctionalExtensionality
  Logic.ClassicalChoice
  Init.Nat
  Arith.EqNat
  Arith.PeanoNat
  Lists.List.

From Paco Require Import
  paco.

Lemma threadDecEq : @IsEqDec ThreadName eqb.
constructor.
intros.
firstorder.
generalize dependent i.
generalize dependent j.
fix rec 1.
destruct i, j.
easy.
simpl in *.
discriminate.
simpl in *.
discriminate.
simpl in *.
intros.
f_equal.
apply rec.
easy.
subst.
rewrite eqb_id.
easy.
intros.
firstorder.
generalize dependent i.
generalize dependent j.
fix rec 1.
intros.
destruct i, j.
simpl in *.
discriminate.
easy.
easy.
simpl in *.
apply rec in H. clear rec.
congruence.
rewrite eqb_nid.
easy.
easy.
Qed.

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

Require Import Coq.Program.Wf.
Require Import Lia.

Definition ends_in_oev {E F} (p : Trace (ThreadLEvent E F)) :=
  exists q i e, p = q ++ cons (i, OEvent e) nil.

Definition ends_in_oev_seq {E F} (p : Trace (LEvent E F)) :=
  exists q e, p = q ++ cons (OEvent e) nil.


Lemma ends_oev_cons {E F} :
  forall p e,
  @ends_in_oev E F p ->
  @ends_in_oev E F (e :: p).
unfold ends_in_oev.
intros.
destruct_all.
subst.
exists (e :: x), x0, x1.
easy.
Qed.

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
simpl.
unfold InterSteps, InterStep in *.
simpl in *.
unfold InterState in *.
repeat rewrite decompSplitSteps in *.
simpl in *.
destruct_all.
cut (
  forall i, exists q : Trace (LEvent E F),
    (In i (map fst x) -> euttTrace (projPoint i eqb x) q) /\
    (~In i (map fst x) -> q = nil) /\
    exists stf,
      Steps (ThreadStep impl') (allIdle i) q stf
).
intros.
{
  apply choice in H3.
  destruct_all.
  assert (
    forall i,
      In i (dedup (map fst x)) ->
      euttTrace (projPoint i eqb x) (x0 i)
  ).
  intros i.
  specialize (H3 i).
  rewrite <- dedup_correct.
  easy.
  assert (
    forall i, exists stf,
      Steps (ThreadStep impl') (allIdle i) (x0 i) stf
  ).
  intros.
  specialize (H3 i).
  easy.
  assert (H3' := H3).
  rename H2 into HObj.
  apply choice in H5.
  destruct_all.
  apply help13 in H4.
  2:{
    intros.
    specialize (H3' i).
    destruct_all.
    apply H7.
    rewrite dedup_correct.
    easy.
  }
  destruct_all.
  assert (
    forall i,
      Steps (ThreadStep impl') (allIdle i) (projPoint i eqb x2) (x1 i)
  ).
  intros.
  specialize (H5 i).
  specialize (H2 i).
  rewrite <- H5 in H2.
  easy.
  (* clear H2. *)
  rewrite <- (decompPointSteps eqb (ThreadStep impl')) in H6.
  2: exact threadDecEq.
  eexists (x1, s), x2.
  repeat split.
  apply euttOver.
  easy.
  easy.
  simpl in *.
  (* clear H7 H2 H3' x1 H6 H4 H3 H0. *)
  clear H6 H3' H2 x1 H5 H3 H0.
  generalize dependent (Init spec).
  clear HObj.
  induction H4.
  {
    easy.
  }
  {
    intros.
    dependent destruction H1.
    unfold StateStep in H0.
    simpl in *.
    subst.
    apply IHeuttThreadTrace.
    easy.
  }
  {
    intros.
    econstructor.
    easy.
    apply IHeuttThreadTrace.
    easy.
  }
  {
    intros.
    dependent destruction H1.
    econstructor.
    exact H0.
    apply IHeuttThreadTrace.
    easy.
  }
  {
    intros.
    dependent destruction H1.
    econstructor.
    exact H0.
    apply IHeuttThreadTrace.
    easy.
  }
  {
    destruct x2.
    left.
    easy.
    right.
    dependent destruction H6.
    dependent destruction H6.
    simpl in *.
    unfold ThreadStep in H6.
    destruct t0, l; simpl in *.
    dependent destruction H6.
    dependent destruction H6.
    repeat econstructor.
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
      (In i (map fst x) -> euttTrace p q) /\
      (~ In i (map fst x) -> q = nil) /\
      exists stf,
        Steps (ThreadStep impl') s' q stf
).
{
  intros.
  apply H0 with (s':=Idle) in H1. clear H0.
  easy.
  intros.
  constructor.
}
generalize dependent (t i).
clear s t.
intros t p.
assert (help_view p) by apply get_view.
induction H0.
{
  intros.
  exists nil.
  repeat econstructor.
}
{
  intros.
  exists nil.
  split.
  clear.
  induction n.
  constructor.
  simpl.
  constructor.
  apply IHn.
  easy.
  split.
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
  exists n' x0',
    match x0 with
    | Cont m (Bind um k) =>
        exists k',
          x0' = Cont m (Bind um k') /\
          forall x, eutt (k x) (k' x)
    | UCall m k =>
        exists k',
          x0' = UCall m k' /\
          forall x, eutt (k x) (k' x)
    | _ => x0' = x0
    end /\
    Steps (ThreadStep impl') s' (nones n') x0'
).
{
  clear IHhelp_view H6.
  destruct H3.
  {
    destruct n; simpl in *; dependent destruction H4.
    exists 0, Idle.
    repeat constructor.
    unfold ThreadStep in H3.
    dependent destruction H3.
  }
  2:{
    destruct n; simpl in *; dependent destruction H4.
    exists 0, (UCall m k').
    split.
    exists k'.
    easy.
    constructor.
    unfold ThreadStep in H3.
    dependent destruction H3.
  }
  {
    punfold H3.
    assert (eutt_finite m p0 p' x0).
    eapply derive_eutt_finite.
    exact H1.
    easy.
    exact H4.
    exact H5.
    clear H5 H4 H3.
    induction H6.
    {
      exists 0, (Cont m (Return x0)).
      repeat constructor.
    }
    {
      exists 0, (Cont m (Bind m0 k')).
      repeat constructor.
      exists k'.
      easy.
    }
    {
      apply IHeutt_finite.
    }
    {
      destruct_all.
      destruct s.
      {
        subst.
        exfalso.
        eapply contra_eutt_finite.
        2: exact H6.
        left.
        easy.
      }
      2:{
        destruct_all.
        subst.
        exfalso.
        eapply contra_eutt_finite.
        2: exact H6.
        right.
        repeat econstructor.
      }
      {
        destruct p1.
        destruct_all.
        subst.
        exists (S x0), (Cont m0 (Bind e0 x2)).
        split.
        exists x2.
        easy.
        simpl.
        econstructor.
        eapply USilentThreadStep.
        easy.
        easy.
        easy.
        subst.
        exists (S x0), (Cont m0 (Return a)).
        split.
        easy.
        simpl.
        econstructor.
        eapply USilentThreadStep.
        easy.
        easy.
        easy.
        subst.
        exists (S x0), (Cont m0 (NoOp p1)).
        split.
        easy.
        simpl.
        econstructor.
        eapply USilentThreadStep.
        easy.
        easy.
        easy.
      }
    }
  }
}
destruct_all.
assert (
  exists st''',
    euttTS_ st'' st''' /\
    ThreadStep impl' x2 e st'''
).
{
  (* clear H7 H5 x1 H3. *)
  unfold ThreadStep in H5.
  destruct x0.
  subst.
  destruct e.
  dependent destruction H5.
  dependent destruction H5.
  exists (Cont m (impl' _ m)).
  split.
  constructor.
  apply H.
  constructor; easy.
  destruct p0.
  destruct_all.
  subst.
  destruct e.
  dependent destruction H5.
  eexists (UCall _ x0).
  split.
  constructor.
  easy.
  unfold ThreadStep.
  eapply UCallThreadStep.
  easy.
  easy.
  dependent destruction H5.
  subst.
  destruct e.
  dependent destruction H5.
  dependent destruction H5.
  exists Idle.
  repeat constructor.
  subst.
  destruct e.
  dependent destruction H5.
  exists (Cont om p1).
  split.
  apply euttTS_refl.
  eapply USilentThreadStep.
  easy.
  easy.
  dependent destruction H5.
  subst.
  destruct e.
  dependent destruction H5.
  destruct_all.
  exists (Cont om (x0 v)).
  split.
  constructor.
  apply H7.
  subst.
  eapply URetThreadStep.
  easy.
  easy.
  dependent destruction H5.
}
destruct_all.
apply IHhelp_view in H9.
destruct_all.
eexists (
  if classicT (List.In i (map fst x)) then
    nones x1 ++ e :: x4
  else
    nil
)%list.
destruct (classicT (In i (map fst x))).
3: easy.
2:{
  repeat split.
  intros.
  contradiction.
  exists s'.
  constructor.
}
repeat split.
{
  intros.
  apply euttTrace_app.
  apply euttTrace_nones.
  destruct e.
  destruct ev.
  2:{
    repeat constructor.
    apply H9.
    easy.
  }
  {
    constructor.
    apply H9.
    easy.
  }
  {
    constructor.
    apply H9.
    easy.
  }
}
{
  intros.
  contradiction.
}
{
  exists x5.
  rewrite <- Steps_app.
  exists x2.
  split.
  2:{
    eapply StepsMore with (st'':=x3).
    easy.
    easy.
  }
  easy.
}
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

Fixpoint projUnderSeq {E F} (p : Trace (LEvent E F)) : Trace (option (Event E)) :=
  match p with
  | nil => nil
  | cons (UEvent e) p => cons e (projUnderSeq p)
  | cons _ p => projUnderSeq p
  end.

Fixpoint projUnderThrSeq {E F} (p : Trace (LEvent E F)) : Trace (Event E) :=
  match p with
  | nil => nil
  | cons (UEvent (Some e)) p => cons e (projUnderThrSeq p)
  | cons _ p => projUnderThrSeq p
  end.

Fixpoint projOverSeq {E F} (p : Trace (LEvent E F)) : Trace (Event F) :=
  match p with
  | nil => nil
  | cons (OEvent e) p => cons e (projOverSeq p)
  | cons _ p => projOverSeq p
  end.

Inductive assoc_view {E F G} : list (LEvent E F) -> list (LEvent F G) -> Prop :=
| AVNil :
    assoc_view nil nil
| AVGCall e tL tH :
    assoc_view tL tH ->
    assoc_view tL (OEvent e :: tH)
| AVFEv e tL tH :
    assoc_view tL tH ->
    assoc_view (OEvent e :: tL) (UEvent (Some e) :: tH)
| AVFSl tL tH :
    assoc_view tL tH ->
    assoc_view tL (UEvent None :: tH)
| AVEEvt e tL tH :
    assoc_view tL tH ->
    assoc_view (UEvent e :: tL) tH.

Definition substTS {E F G} (impl : Impl E F) (s : ThreadState F G) : ThreadState E G :=
  match s with
  | Idle => Idle
  | Cont m p => Cont m (substProg impl p)
  | UCall m k => UCall m (fun x => substProg impl (k x))
  end.

Ltac destruct_steps :=
repeat match goal with
| [ H : Steps ?step ?s (?e :: ?es) ?t |- _] => dependent destruction H
| [ H : Steps ?step ?s nil ?t |- _] => dependent destruction H
| [ H : ThreadStep ?impl ?s ?e ?t |- _] => unfold ThreadStep in H; dependent destruction H
end;
subst.

Lemma projOver_if {E F} :
  forall i j ev p,
  @projOverSeq E F (if i =? j then UEvent ev :: p else p) =
  @projOverSeq E F p.
intros.
destruct (i =? j).
simpl.
easy.
easy.
Qed.

Lemma projUnderThr_if_sil {E F} :
  forall i j p,
  @projUnderThrSeq E F (if i =? j then UEvent None :: p else p) =
  @projUnderThrSeq E F p.
intros.
destruct (i =? j).
simpl.
easy.
easy.
Qed.

Lemma projUnderThr_if_oev {E F} :
  forall i j p ev,
  @projUnderThrSeq E F (if i =? j then OEvent ev :: p else p) =
  @projUnderThrSeq E F p.
intros.
destruct (i =? j).
simpl.
easy.
easy.
Qed.

Program Fixpoint seq_proj_assoc {E F G} i (p : Trace (ThreadLEvent E F)) (q : Trace (ThreadLEvent F G)) {measure (length p + length q)} : 
  projOver p = projUnderThr q ->
  projOverSeq (projPoint i eqb p) = projUnderThrSeq (projPoint i eqb q) := _.
Next Obligation.
destruct p, q.
easy.

{
  destruct t, l.
  destruct ev; simpl in *.
  congruence.
  destruct (i =? n).
  apply (@seq_proj_assoc E F G) with (p:=nil).
  simpl.
  lia.
  easy.
  apply (@seq_proj_assoc E F G) with (p:=nil).
  simpl.
  lia.
  easy.
  simpl.
  destruct (i =? n).
  apply (@seq_proj_assoc E F G) with (p:=nil).
  simpl.
  lia.
  easy.
  apply (@seq_proj_assoc E F G) with (p:=nil).
  simpl.
  lia.
  easy.
}

{
  destruct t, l; simpl in *.
  destruct ev; simpl in *.
  destruct (i =? n).
  simpl.
  apply (@seq_proj_assoc E F G) with (q:=nil).
  simpl.
  lia.
  easy.
  apply (@seq_proj_assoc E F G) with (q:=nil).
  simpl.
  lia.
  easy.
  destruct (i =? n).
  simpl.
  apply (@seq_proj_assoc E F G) with (q:=nil).
  simpl.
  lia.
  easy.
  apply (@seq_proj_assoc E F G) with (q:=nil).
  simpl.
  lia.
  easy.
  congruence.
}
{
  destruct t, t0.
  destruct l, l0.
  {
    simpl (@projOverSeq E F _).
    rewrite (projOver_if (E:=E) (F:=F)).
    apply seq_proj_assoc.
    simpl.
    lia.
    easy.
  }
  {
    simpl (projUnderThrSeq _).
    rewrite (projUnderThr_if_oev (E:=F) (F:=G)).
    apply seq_proj_assoc.
    simpl.
    lia.
    easy.
  }
  destruct ev0.
  {
    simpl in *.
    dependent destruction H.
    assert (i = n0 \/ i <> n0) by apply excluded_middle.
    destruct H.
    subst.
    rewrite eqb_id.
    simpl.
    f_equal.
    apply seq_proj_assoc.
    simpl.
    lia.
    easy.
    rewrite eqb_nid.
    2: easy.
    apply seq_proj_assoc.
    simpl.
    lia.
    easy.
  }
  {
    simpl (projUnderThrSeq _).
    rewrite (projUnderThr_if_sil (E:=F) (F:=G)).
    apply seq_proj_assoc.
    simpl.
    lia.
    easy.
  }
  {
    simpl (projUnderThrSeq _).
    rewrite (projUnderThr_if_oev (E:=F) (F:=G)).
    apply seq_proj_assoc.
    simpl.
    lia.
    easy.
  }
}
Qed.


Program Fixpoint get_assoc_view {E F G} (p : Trace (LEvent E F)) (q : Trace (LEvent F G)) {measure (length p + length q)} : 
  projOverSeq p = projUnderThrSeq q ->
  assoc_view p q := _.
Next Obligation.
intros.
destruct p, q.
constructor.
{
  destruct l; simpl in *.
  destruct ev.
  congruence.
  constructor.
  apply get_assoc_view.
  simpl.
  lia.
  easy.
  constructor.
  apply get_assoc_view.
  simpl.
  lia.
  easy.
}
{
  destruct l; simpl in *.
  destruct ev.
  constructor.
  apply get_assoc_view.
  simpl.
  lia.
  easy.
  constructor.
  apply get_assoc_view.
  simpl.
  lia.
  easy.
  congruence.
}
{
  destruct l, l0.
  destruct ev, ev0.
  simpl in *.
  constructor.
  apply get_assoc_view.
  simpl.
  lia.
  easy.
  simpl in *.
  constructor.
  constructor.
  apply get_assoc_view.
  simpl.
  lia.
  easy.
  simpl in *.
  constructor.
  apply get_assoc_view.
  simpl.
  lia.
  easy.
  simpl in *.
  constructor.
  constructor.
  apply get_assoc_view.
  simpl.
  lia.
  easy.
  simpl in *.
  constructor.
  constructor.
  apply get_assoc_view.
  simpl.
  lia.
  easy.
  simpl in *.
  destruct ev0.
  dependent destruction H.
  constructor.
  apply get_assoc_view.
  simpl.
  lia.
  easy.
  constructor.
  apply get_assoc_view.
  simpl.
  lia.
  easy.
  simpl in *.
  constructor.
  apply get_assoc_view.
  simpl.
  lia.
  easy.
}
Qed.

Lemma derive_is_nil {E F} :
  forall p : Trace (LEvent E F),
  projUnderSeq p = nil ->
  projOverSeq p = nil ->
  p = nil.
intros.
destruct p.
easy.
destruct l.
simpl in *.
congruence.
simpl in *.
congruence.
Qed.

Lemma derive_is_nones {E F} :
  forall p : Trace (LEvent E F),
  projUnderThrSeq p = nil ->
  projOverSeq p = nil ->
  exists n,
    p = nones n.
intros.
induction p.
exists 0.
easy.
destruct a; simpl in *.
destruct ev; simpl in *.
congruence.
apply IHp in H.
destruct_all.
exists (S x).
subst.
easy.
apply IHp in H.
destruct_all.
subst.
easy.
easy.
congruence.
Qed.

Inductive Interleave {E F} : (nat -> Trace (LEvent E F)) -> Trace (ThreadLEvent E F) -> Prop :=
| InterleaveEnd qc :
    (forall i, qc i = nil) ->
    Interleave qc nil
| InterleaveCons i e q qc p :
    qc i = e :: q ->
    Interleave (fun j => if i =? j then q else qc j) p ->
    Interleave qc ((i, e) :: p).

Lemma constr_interleave {E F} :
  forall qc p,
  @Interleave E F qc p <->
  forall i,
    qc i = projPoint i eqb p.
split; intros.
{
  generalize dependent qc.
  induction p; intros; dependent destruction H.
  {
    rewrite H.
    easy.
  }
  {
    simpl.
    assert (i = i0 \/ i <> i0) by apply excluded_middle.
    destruct H1.
    subst.
    rewrite H.
    rewrite eqb_id.
    f_equal.
    apply IHp in H0.
    rewrite eqb_id in H0.
    easy.
    rewrite eqb_nid.
    2: easy.
    apply IHp in H0.
    rewrite eqb_nid in H0.
    2: easy.
    easy.
  }
}
{
  generalize dependent qc.
  induction p; intros.
  {
    constructor.
    easy.
  }
  {
    destruct a.
    simpl in *.
    assert (H' := H).
    econstructor.
    specialize (H n).
    rewrite eqb_id in H.
    exact H.
    apply IHp.
    intros.
    specialize (H' i).
    dec_eq_nats n i.
    rewrite eqb_id in *.
    easy.
    rewrite eqb_nid in *.
    easy.
    easy.
    easy.
  }
}
Qed.

(* the state *before* the event *)
Inductive assoc_states {E F G} {impl : Impl E F} {impl' : Impl F G} : ThreadState E F -> ThreadState F G -> ThreadState E G -> Prop :=
| ASGCall :
    assoc_states Idle Idle Idle
| ASFCall A B (gm : G A) (fm : F B) k :
    assoc_states Idle (Cont gm (Bind fm k)) (Cont gm (NoOp (bindSubstProg impl k (impl _ fm))))
| ASFNoOp A m p :
  assoc_states Idle (Cont m (NoOp p)) (Cont m (NoOp (A:=A) (substProg impl p)))
| ASECall A R gm fm em ek fk :
    assoc_states (Cont fm (Bind em ek)) (UCall gm fk) (Cont gm (Bind (A:=A) em (fun x => bindSubstProg (R:=R) impl fk (ek x))))
| ASENoOp R k om p um :
    assoc_states (Cont um (NoOp p)) (UCall om k) (Cont om (NoOp (bindSubstProg (R:=R) impl k p)))
| ASEBind A gm fm ek fk :
    assoc_states (UCall (A:=A) fm ek) (UCall (B:=A) gm fk) (UCall gm (fun x => bindSubstProg impl fk (ek x)))
| ASERet A gm fm v fk :
    assoc_states (Cont fm (Return v)) (UCall gm fk) (Cont (A:=A) gm (NoOp (substProg impl (fk v))))
| ASFRet A (gm : G A) v :
    assoc_states Idle (Cont gm (Return v)) (Cont gm (Return v))
.
Arguments assoc_states {E F G} impl impl'.

Ltac simpl_sp := try (rewrite frobProgId with (p:= substProg _ _)); try (rewrite frobProgId with (p:= bindSubstProg _ _ _)); simpl.

Inductive same_threads {I A B} : Trace (I * A) -> Trace (I * B) -> Prop :=
| STNil :
    same_threads nil nil
| STCons i e1 e2 p q :
    same_threads p q ->
    same_threads ((i, e1) :: p) ((i, e2) :: q).

Lemma same_threads_app {I A B} :
  forall p1 p2 q1 q2,
  same_threads p1 q1 ->
  same_threads p2 q2 ->
  @same_threads I A B (p1 ++ p2) (q1 ++ q2).
intros.
induction H.
easy.
simpl.
constructor.
easy.
Qed.

Lemma projOver_nil {E F} :
  forall p : Trace (ThreadLEvent E F),
  (forall i,
    projOverSeq (projPoint i eqb p) = nil) -> 
  projOver p = nil.
intros.
induction p.
{
  easy.
}
{
  destruct a, l.
  {
    simpl in *.
    apply IHp.
    intros.
    specialize (H i).
    destruct (i =? n).
    easy.
    easy.
  }
  {
    simpl in *.
    specialize (H n).
    rewrite eqb_id in H.
    simpl in *.
    congruence.
  }
}
Qed.

Lemma projUnderThr_nil {E F} :
  forall p : Trace (ThreadLEvent E F),
  (forall i,
    projUnderThrSeq (projPoint i eqb p) = nil) -> 
  projUnderThr p = nil.
intros.
induction p.
{
  easy.
}
{
  destruct a, l.
  destruct ev.
  2:{
    simpl in *.
    apply IHp.
    intros.
    specialize (H i).
    destruct (i =? n).
    easy.
    easy.
  }
  {
    simpl in *.
    specialize (H n).
    rewrite eqb_id in H.
    simpl in *.
    congruence.
  }
  {
    simpl in *.
    apply IHp.
    intros.
    specialize (H i).
    destruct (i =? n).
    easy.
    easy.
  }
}
Qed.

Program Fixpoint full_projOver_help {E F G} (p : Trace (ThreadLEvent E G)) (q : Trace (ThreadLEvent F G)) {measure (length p + length q)} :
  same_threads (projOver p) (projOver q) ->
  (forall i,
    projOverSeq (projPoint i eqb p) = projOverSeq (projPoint i eqb q)) ->
  projOver p = projOver q
  := _.
Next Obligation.
destruct p.
{
  clear full_projOver_help H.
  simpl.
  rewrite projOver_nil.
  easy.
  intros.
  specialize (H0 i).
  easy.
}
destruct q.
{
  simpl (projOver nil).
  rewrite projOver_nil.
  easy.
  easy.
}
{
  destruct t, t0.
  destruct l, l0; simpl in *.
  {
    apply full_projOver_help.
    simpl. lia.
    easy.
    intros.
    specialize (H0 i).
    destruct (i =? n), (i =? n0); easy.
  }
  {
    eapply full_projOver_help with (q:=(n0, OEvent ev0) :: q).
    simpl. lia.
    simpl.
    easy.
    intros.
    specialize (H0 i).
    assert (
      projOverSeq (projPoint i eqb p) = projOverSeq (if i =? n0 then OEvent ev0 :: projPoint i eqb q else projPoint i eqb q)
    ) by (destruct (i =? n); easy). clear H0.
    dec_eq_nats i n0.
    rewrite eqb_id in H1.
    simpl.
    rewrite eqb_id.
    easy.
    simpl.
    rewrite eqb_nid in *.
    easy.
    easy.
    easy.
  }
  {
    eapply full_projOver_help with (p:=(n, OEvent ev) :: p).
    simpl. lia.
    simpl.
    easy.
    intros.
    specialize (H0 i).
    assert (
      projOverSeq (if i =? n0 then UEvent ev0 :: projPoint i eqb q else projPoint i eqb q) = projOverSeq (projPoint i eqb q)
    ) by (destruct (i =? n0); easy).
    rewrite H1 in H0 at 1. clear H1.
    simpl.
    dec_eq_nats i n.
    rewrite eqb_id in *.
    easy.
    rewrite eqb_nid in *.
    easy.
    easy.
    easy.
  }
  {
    dependent destruction H.
    assert (H0' := H0).
    specialize (H0 n0).
    rewrite eqb_id in H0.
    simpl in *.
    dependent destruction H0.
    f_equal.
    apply full_projOver_help.
    simpl. lia.
    easy.
    intros.
    specialize (H0' i).
    destruct (i =? n0).
    simpl in *.
    congruence.
    easy.
  }
}
Qed.

Lemma projUnderThrSeq_same {E F} {b : bool} :
  forall (p : Trace (LEvent E F)) (e : LEvent E F),
  ~(exists e', e = UEvent (Some e')) ->
  projUnderThrSeq (if b then e :: p else p) =
  projUnderThrSeq p.
intros.
destruct e.
destruct ev.
destruct b.
exfalso.
apply H.
exists e.
easy.
easy.
destruct b; easy.
destruct b; easy.
Qed.

Lemma full_projOver {E F G} :
  forall (p : Trace (ThreadLEvent F G)) q,
  forall (qc : nat -> Trace (LEvent E G)),
  (forall i, projOverSeq (projPoint i eqb p) = projOverSeq (qc i)) ->
  Interleave qc q ->
  same_threads (projOver p) (projOver q) ->
  projOver p = projOver q.
intros.
eassert (H2 : forall i, _).
{
  erewrite <- constr_interleave.
  exact H0.
}
assert (forall i, projOverSeq (projPoint i eqb p) = projOverSeq (projPoint i eqb q)).
{
  intros.
  rewrite H.
  rewrite H2.
  easy.
}
apply full_projOver_help; easy.
Qed.

Program Fixpoint full_projUnderThr_help {E F G} (p : Trace (ThreadLEvent E F)) (q : Trace (ThreadLEvent E G)) {measure (length p + length q)} :
  same_threads (projUnderThr p) (projUnderThr q) ->
  (forall i,
    projUnderThrSeq (projPoint i eqb p) = projUnderThrSeq (projPoint i eqb q)) ->
  projUnderThr p = projUnderThr q
  := _.
Next Obligation.
destruct p.
{
  simpl in *.
  rewrite projUnderThr_nil.
  easy.
  intros.
  specialize (H0 i).
  easy.
}
destruct q.
{
  simpl (projUnderThr nil).
  rewrite projUnderThr_nil.
  easy.
  intros.
  specialize (H0 i).
  easy.
}
{
  destruct t, t0.
  destruct l, l0.
  {
    destruct ev, ev0.
    simpl in *.
    dependent destruction H.
    assert (H0' := H0).
    specialize (H0 n0).
    rewrite eqb_id in H0.
    simpl in *.
    dependent destruction H0.
    f_equal.
    apply full_projUnderThr_help.
    simpl. lia.
    easy.
    intros.
    specialize (H0' i).
    destruct (i =? n0).
    simpl in *.
    congruence.
    easy.
    simpl (projUnderThr ((n0, _) :: _)).
    apply full_projUnderThr_help.
    simpl. lia.
    easy.
    intros.
    specialize (H0 i).
    simpl in *.
    rewrite projUnderThrSeq_same with (e:= UEvent None) in H0 at 1.
    easy.
    unfold not.
    intros.
    destruct_all.
    congruence.
    simpl (projUnderThr ((n, _) :: _)).
    apply full_projUnderThr_help.
    simpl. lia.
    easy.
    intros.
    specialize (H0 i).
    simpl in *.
    destruct (i =? n); easy.
    simpl in *.
    apply full_projUnderThr_help.
    simpl. lia.
    easy.
    intros.
    specialize (H0 i).
    rewrite projUnderThrSeq_same in H0 at 1.
    rewrite projUnderThrSeq_same in H0 at 1.
    easy.
    unfold not.
    intros.
    destruct_all.
    congruence.
    unfold not.
    intros.
    destruct_all.
    congruence.
  }
  {
    simpl (projUnderThr ((n0, _) :: _)).
    apply full_projUnderThr_help.
    simpl. lia.
    easy.
    intros.
    specialize (H0 i).
    simpl in H0.
    destruct (i =? n0); easy.
  }
  {
    simpl (projUnderThr ((n, _) :: _)).
    apply full_projUnderThr_help.
    simpl. lia.
    easy.
    intros.
    specialize (H0 i).
    simpl in H0.
    destruct (i =? n); easy.
  }
  {
    simpl in *.
    apply full_projUnderThr_help.
    simpl. lia.
    easy.
    intros.
    specialize (H0 i).
    rewrite projUnderThrSeq_same in H0 at 1.
    rewrite projUnderThrSeq_same in H0 at 1.
    easy.
    unfold not.
    intros.
    destruct_all.
    congruence.
    unfold not.
    intros.
    destruct_all.
    congruence.
  }
}
Qed.

Lemma full_projUnderThr {E F G} :
  forall (p : Trace (ThreadLEvent E F)) q,
  forall (qc : nat -> Trace (LEvent E G)),
  (forall i, projUnderThrSeq (projPoint i eqb p) = projUnderThrSeq (qc i)) ->
  Interleave qc q ->
  same_threads (projUnderThr p) (projUnderThr q) ->
  projUnderThr p = projUnderThr q.
intros.
intros.
eassert (H2 : forall i, _).
{
  erewrite <- constr_interleave.
  exact H0.
}
assert (forall i, projUnderThrSeq (projPoint i eqb p) = projUnderThrSeq (projPoint i eqb q)).
{
  intros.
  rewrite H.
  rewrite H2.
  easy.
}
apply full_projUnderThr_help; easy.
Qed.

(* Inductive help66_interleave {E F G} : Trace (LEvent E F) -> Trace (LEvent F G) -> Trace (LEvent E G) -> Prop :=
| HNil :
    help66_interleave nil nil nil
| HSkipOverUnder e p q r :
    help66_interleave p q r ->
    help66_interleave p (UEvent e :: q) r
| HSkipUnderOver e p q r :
    help66_interleave p q r ->
    help66_interleave (OEvent e :: p) q r
| HSkipUnderSilent p q r :
    help66_interleave p q r ->
    help66_interleave (UEvent None :: p) q r
| HCons ue oe p q r :
. *)

Lemma help66 {E F G} (impl : Impl E F) (impl' : Impl F G) sL' sH' :
  forall (tL : list (LEvent E F)) (tH : list (LEvent F G)),
  assoc_view tL tH ->
  forall sL : ThreadState E F,
  forall sH : ThreadState F G,
  forall sF : ThreadState E G,
  assoc_states impl impl' sL sH sF ->
  Steps (ThreadStep impl) sL tL sL' ->
  Steps (ThreadStep impl') sH tH sH' ->
  exists sF' (q : Trace (LEvent E G)),
    projOverSeq tH = projOverSeq q /\
    projUnderThrSeq tL = projUnderThrSeq q /\
    Steps (ThreadStep (impl |> impl')) sF q sF'.
intros tL tH H.
induction H; intros; destruct_steps.
{
  exists sF, nil.
  repeat constructor.
}
{
  dependent destruction H0.
  eapply IHassoc_view in H4.
  3: exact H1.
  destruct_all.
  exists x, (OEvent (CallEv m) :: x0).
  repeat split; simpl; f_equal; try easy.
  econstructor.
  repeat constructor.
  exact H3.
  unfold implVComp.
  remember (impl' _ m).
  destruct p.
  simpl_sp.
  constructor.
  simpl_sp.
  constructor.
  simpl_sp.
  constructor.
}
{
  dependent destruction H0.
  eapply IHassoc_view in H4.
  3: exact H1.
  destruct_all.
  exists x, (OEvent (RetEv m v) :: x0).
  simpl.
  repeat split; simpl; f_equal; try easy.
  econstructor.
  econstructor; easy.
  exact H3.
  constructor.
}
{
  dependent destruction H0.
  eapply IHassoc_view in H4.
  3: exact H2.
  destruct_all.
  exists x, (UEvent None :: x0).
  repeat split; try easy.
  econstructor.
  econstructor; easy.
  exact H3.
  remember (impl _ um).
  destruct p.
  simpl_sp.
  constructor.
  simpl_sp.
  fold (substProg (E:=E) (F:=F)).
  constructor.
  simpl_sp.
  constructor.
}
{
  dependent destruction H0.
  eapply IHassoc_view in H4.
  3: exact H2.
  destruct_all.
  exists x, (UEvent None :: x0).
  repeat split; try easy.
  econstructor.
  econstructor; easy.
  exact H3.
  remember (k v).
  destruct p.
  simpl_sp.
  constructor.
  simpl_sp.
  constructor.
  simpl_sp.
  constructor.
}
{
  dependent destruction H0.
  eapply IHassoc_view in H4.
  3: exact H1.
  destruct_all.
  exists x, (UEvent None :: x0).
  repeat split; try easy.
  econstructor.
  econstructor; easy.
  exact H3.
  destruct p; simpl_sp; constructor.
}
{
  dependent destruction H0.
  eapply IHassoc_view in H4.
  3: exact H3.
  destruct_all.
  exists x, (UEvent (Some (CallEv um)) :: x0).
  repeat split; simpl; f_equal; try easy.
  econstructor.
  econstructor.
  easy.
  easy.
  exact H2.
  constructor.
}
{
  dependent destruction H0.
  eapply IHassoc_view in H4.
  3: exact H3.
  destruct_all.
  exists x, (UEvent (Some (RetEv um v)) :: x0).
  repeat split; simpl; f_equal; try easy.
  econstructor.
  econstructor.
  easy.
  easy.
  exact H2.
  simpl.
  remember (k v).
  destruct p; simpl_sp.
  2: fold (substProg (E:=E) (F:=F)).
  constructor.
  constructor.
  constructor.
}
{
  dependent destruction H0.
  eapply IHassoc_view in H4.
  3: exact H3.
  destruct_all.
  exists x, (UEvent None :: x0).
  repeat split; try easy.
  econstructor.
  econstructor.
  easy.
  easy.
  exact H2.
  destruct p; simpl_sp.
  2: fold (substProg (E:=E) (F:=F)).
  constructor.
  constructor.
  constructor.
}
Qed.

Lemma In_split {A} {x : A} {xs ys : list A} :
  In x (xs ++ ys) = (In x xs \/ In x ys).
apply propositional_extensionality.
split; intro.
{
  induction xs.
  right.
  easy.
  simpl in *.
  destruct H.
  subst.
  left. left.
  easy.
  apply IHxs in H.
  destruct H.
  left. right.
  easy.
  right.
  easy.
}
{
  induction xs.
  destruct H.
  contradiction.
  easy.
  simpl in *.
  destruct H.
  destruct H.
  subst.
  left.
  easy.
  right.
  apply IHxs.
  left.
  easy.
  right.
  apply IHxs.
  right.
  easy.
}
Qed.

Axiom dne : forall P, ~~P -> P.

Lemma if_prune {A B} {x y : B} {z : A -> B} :
  forall (b : A -> bool),
  (fun i : A => if b i then x else if b i then y else z i) =
  (fun i : A => if b i then x else z i).
intros.
extensionality j.
destruct (b j); easy.
Qed.

Lemma if_swap {A B} {x y : B} {z : A -> B} :
  forall (b1 b2 : A -> bool),
  (forall i, b1 i <> b2 i) ->
  (fun i : A => if b1 i then x else if b2 i then y else z i) =
  (fun i : A => if b2 i then y else if b1 i then x else z i).
intros.
extensionality i.
specialize (H i).
remember (b1 i).
remember (b2 i).
destruct (b1 i).
subst.
destruct (b2 i).
congruence.
easy.
subst.
easy.
Qed.

Lemma in_notin :
  forall i j xs,
  In i xs ->
  ~In (A:=nat) j xs ->
  i <> j.
intros.
induction xs.
contradiction.
simpl in *.
rewrite help41 in H0.
destruct_all.
destruct H.
subst.
easy.
apply IHxs; easy.
Qed.

Fixpoint thread_nones {E F} i n : Trace (ThreadLEvent E F) :=
  match n with
  | 0 => nil
  | S n => (i, UEvent None) :: thread_nones i n
  end.

Inductive silents {E G} : (nat -> Trace (LEvent E G)) -> Trace (ThreadLEvent E G) -> Prop :=
| SNil qc :
    (forall i, qc i = nil) ->
    silents qc nil
| SCons qc i s r :
    qc i = UEvent None :: s ->
    silents (fun j => if i =? j then s else qc j) r ->
    silents qc ((i, UEvent None) :: r).

Fixpoint atnones {E F} (qc : nat -> Trace (LEvent E F)) (is : list nat) :=
  match is with
  | nil => nil
  | i :: is =>
      @thread_nones E F i (length (qc i)) ++
      atnones (fun j => if i =? j then nil else qc j) is
  end.

Definition tail {A} (xs : list A) : list A :=
  match xs with
  | _ :: xs => xs
  | nil => nil
  end.

Lemma prune_if_projOver {E F G} :
  forall n q ev qc,
  (forall i, projOverSeq (if i =? n then UEvent ev :: projPoint i eqb q else projPoint i eqb q) = projOverSeq (qc i)) ->
  (forall i, projOverSeq (E:=E) (projPoint i eqb q) = projOverSeq (E:=F) (F:=G) (qc i)).
intros.
specialize (H i).
destruct (i =? n); easy.
Qed.

Lemma prune_if_projUnderThr {E F G} :
  forall n q ev qc,
  ~(exists e', ev = UEvent (Some e')) ->
  (forall i, projUnderThrSeq (if i =? n then ev :: projPoint i eqb q else projPoint i eqb q) = projUnderThrSeq (qc i)) ->
  (forall i, projUnderThrSeq (F:=F) (projPoint i eqb q) = projUnderThrSeq (E:=E) (F:=G) (qc i)).
intros.
specialize (H0 i).
dec_eq_nats i n.
rewrite eqb_id in H0.
simpl in *.
destruct ev.
destruct ev.
exfalso.
apply H.
exists e.
easy.
easy.
easy.
rewrite eqb_nid in H0.
easy.
easy.
Qed.


Lemma is_nones {E F} :
  forall p,
  nil = projUnderThrSeq p ->
  nil = projOverSeq (E:=E) (F:=F) p ->
  exists n, p = nones n.
intros.
induction p.
exists 0.
easy.
destruct a.
destruct ev.
simpl in *. congruence.
simpl in *.
apply IHp in H.
destruct_all.
exists (S x).
simpl.
subst.
easy.
easy.
simpl in *.
congruence.
Qed.

Lemma get_projUnderThr_nones {E F G} :
  forall ev q f,
  nil = projOverSeq f ->
  ev :: projUnderThrSeq (F:=F) q = projUnderThrSeq (F:=G) f ->
  exists n f', f = nones (E:=E) n ++ UEvent (Some ev) :: f'.
intros.
generalize dependent q.
induction f; simpl; intros.
congruence.
destruct a.
destruct ev0.
dependent destruction H0.
exists 0, f.
easy.
apply IHf in H0.
destruct_all.
subst.
exists (S x), x0.
easy.
easy.
simpl in *.
congruence.
Qed.

(* Lemma gen_get_projUnderThr_nones {E F G} :
  forall ev q f,
  ev :: projUnderThrSeq (F:=F) q = projUnderThrSeq (F:=G) f ->
  (exists n f',
    f = nones n ++ UEvent (E:=E) (Some ev) :: f'). *)

Lemma get_projOver_nones {E F G} :
  forall ev q f,
  nil = projUnderThrSeq f ->
  ev :: projOverSeq (E:=E) q = projOverSeq (E:=G) (F:=F) f ->
  exists n f', f = nones n ++ OEvent ev :: f'.
intros.
generalize dependent q.
induction f; simpl; intros.
congruence.
destruct a.
destruct ev0; simpl in *.
congruence.
apply IHf in H0.
destruct_all.
subst.
exists (S x), x0.
easy.
easy.
simpl in *.
dependent destruction H0.
exists 0, f.
easy.
Qed.

Lemma projOverSeq_app {E F} :
  forall p q,
  projOverSeq (p ++ q) =
  projOverSeq p ++ projOverSeq (F:=F) (E:=E) q.
intros.
induction p.
easy.
simpl.
destruct a.
easy.
simpl.
f_equal.
easy.
Qed.

Lemma projUnderThrSeq_app {E F} :
  forall p q,
  projUnderThrSeq (p ++ q) =
  projUnderThrSeq p ++ projUnderThrSeq (F:=F) (E:=E) q.
intros.
induction p.
easy.
simpl.
destruct a.
destruct ev.
simpl.
f_equal.
easy.
easy.
easy.
Qed.

Lemma projOverSeq_nones {E F} :
  forall n,
  projOverSeq (E:=E) (F:=F) (nones n) = nil.
intros.
induction n; easy.
Qed.

Lemma projUnderThrSeq_nones {E F} :
  forall n,
  projUnderThrSeq (E:=E) (F:=F) (nones n) = nil.
intros.
induction n; easy.
Qed.

Lemma tnones_notin {E F} :
  forall i l qc,
  ~In i l ->
  projPoint i eqb (atnones (E:=E) (F:=F) qc l) = nil.
intros.
generalize dependent qc.
induction l; simpl; intros.
easy.
dec_eq_nats a i.
simpl in H.
rewrite help41 in H. destruct H.
congruence.
rewrite @projPoint_app.
rewrite IHl.
rewrite app_nil_r.
induction (qc a).
easy.
simpl.
rewrite eqb_nid.
easy.
easy.
simpl in *.
rewrite help41 in H.
easy.
Qed.

Lemma proj_nones {E F} :
  forall n i,
  projPoint i eqb (thread_nones (E:=E) (F:=F) i n) = nones n.
intros.
induction n.
easy.
simpl.
rewrite eqb_id.
f_equal.
easy.
Qed.

Lemma proj_nones_not {E F} :
  forall n i j,
  i <> j ->
  projPoint i eqb (thread_nones (E:=E) (F:=F) j n) = nil.
intros.
induction n.
easy.
simpl.
rewrite eqb_nid.
f_equal.
easy.
easy.
Qed.

Lemma projUnderThr_nones {E F} :
  forall n n0,
  projUnderThr (E:=E) (F:=F) (thread_nones n n0) = nil.
intros.
induction n0; easy.
Qed.

Lemma nones_to_thread_nones {E G} :
  forall i x,
  map (fun e : LEvent E G => (i, e)) (nones x) = thread_nones i x.
induction x.
easy.
simpl.
f_equal.
easy.
Qed.

Inductive choose_trace {E F G} : (nat -> Trace (LEvent E G)) -> Trace (ThreadLEvent E F) -> Trace (ThreadLEvent F G) -> Trace (ThreadLEvent E G) -> Prop :=
| ChooseNil qc :
    (forall i, qc i = nil) ->
    choose_trace qc nil nil nil
| ChooseUnder qc i e s p q r :
    choose_trace (fun j => if i =? j then s else qc j) p q r ->
    qc i = UEvent (Some e) :: s ->
    choose_trace qc ((i, UEvent (Some e)) :: p) q ((i, UEvent (Some e)) :: r)
| ChooseOver qc i e s p q r :
    choose_trace (fun j => if i =? j then s else qc j) p q r ->
    qc i = OEvent e :: s ->
    choose_trace qc p ((i, OEvent e) :: q) ((i, OEvent e) :: r)
| ChooseSilent qc i s p q r :
    choose_trace (fun j => if i =? j then s else qc j) p q r ->
    qc i = UEvent None :: s ->
    choose_trace qc p q ((i, UEvent None) :: r)
| ChooseUnderSkipSilent qc i p q r :
    choose_trace qc p q r ->
    choose_trace qc ((i, UEvent None) :: p) q r
| ChooseUnderSkipOver qc i e p q r :
    choose_trace qc p q r ->
    choose_trace qc ((i, OEvent e) :: p) q r
| ChooseOverSkipUnder qc i e p q r :
    choose_trace qc p q r ->
    choose_trace qc p ((i, UEvent e) :: q) r.

Inductive finite_map {A} :=
| Emp
| Map (i : nat) (xs : list A) (m : finite_map).
Arguments finite_map : clear implicits.

Fixpoint update {A} (m : finite_map A) i (xs : list A) : finite_map A :=
  match m with
  | Emp => Map i xs Emp
  | Map j ys m' =>
      if i =? j then
        Map i xs m'
      else
        Map j ys (update m' i xs)
  end.

Fixpoint map_size {A} (m : finite_map A) : nat :=
  match m with
  | Emp => 0
  | Map _ xs m => length xs + map_size m
  end.

Fixpoint index {A} (m : finite_map A) i : list A :=
  match m with
  | Emp => nil
  | Map n xs m' =>
      if n =? i then
        xs
      else
        index m' i
  end.

Fixpoint dedup_map {A} (m : finite_map A) is : finite_map A :=
  match m with
  | Emp => Emp
  | Map i xs m' =>
      if classicT (In i is) then
        dedup_map m' is
      else
        Map i xs (dedup_map m' (i :: is))
  end.

(* Lemma map_functional {A} :
  forall m : finite_map A,
  index *)

Fixpoint indices {A} (m : finite_map A) : list nat :=
  match m with
  | Emp => nil
  | Map n _ m => n :: indices m
  end.

Fixpoint mk_fmap {A} (qc : nat -> list A) is : finite_map A :=
  match is with
  | nil => Emp
  | cons i is => Map i (qc i) (mk_fmap qc is)
  end.

Lemma fmap_correct {A} :
  forall qc is,
  (forall i, ~In i is -> qc i = nil) ->
  qc = @index A (mk_fmap qc is).
intros.
extensionality i.
specialize (H i).
induction is.
rewrite H.
easy.
easy.
simpl in *.
dec_eq_nats i a.
rewrite eqb_id.
easy.
rewrite eqb_nid.
apply IHis.
intros.
apply H.
rewrite help41.
easy.
easy.
Qed.

(* Lemma choose_nat : exists n : nat, True.
exists 0.
easy.
Qed. *)

(* Inductive nones_map_view {E F} : finite_map (LEvent E F) -> Prop :=
| NVEmp :
    nones_map_view Emp
| NVMap i n m :
    nones_map_view m ->
    nones_map_view (Map i (nones n) m). *)

(* Lemma get_nmv {E F} :
  forall qc,
  (forall i, exists n, index qc i = @nones E F n) ->
  nones_map_view qc.
intros.
induction qc.
constructor.
simpl in *. *)

Inductive under_trace {E F} : Trace (LEvent E F) -> Prop :=
| UTNil :
    under_trace nil
| UTCons p e :
    ~(exists e', e = OEvent e') ->
    under_trace p ->
    under_trace (e :: p).

Inductive over_silent_trace {E F} : Trace (LEvent E F) -> Prop :=
| OSNil :
    over_silent_trace nil
| OSCons p e :
    ~(exists e', e = UEvent (Some e')) ->
    over_silent_trace p ->
    over_silent_trace (e :: p).

Lemma get_projUnder_over {E F F'} :
  forall q f ev,
  ev :: projUnderThrSeq (F:=F) q = projUnderThrSeq (F:=F') f ->
  (exists n ev' u s,
    over_silent_trace (E:=E) u /\
    f = nones n ++ OEvent ev' :: u ++ UEvent (Some ev) :: s) \/
  (exists n s,
    f = nones n ++ UEvent (Some ev) :: s).
intros.
generalize dependent q.
induction f; simpl; intros.
discriminate.
destruct a.
destruct ev0.
Admitted.

Lemma get_projOver_under {E E' F} :
  forall q f ev,
  ev :: projOverSeq (E:=E) q = projOverSeq (E:=E') f ->
  (exists ev' n u s,
    under_trace u /\
    f = nones n ++ UEvent (F:=F) (Some ev') :: u ++ OEvent ev :: s) \/
  (exists n s,
    f = nones n ++ OEvent ev :: s).
intros.
generalize dependent q.
induction f; simpl; intros.
discriminate.
destruct a.
destruct ev0.
{
  apply IHf in H. clear IHf.
  destruct H; destruct_all; subst.
  left.
  exists e, 0, (nones x0 ++ UEvent (Some x) :: x1), x2.
  simpl.
  split.
  {
    induction x0.
    simpl.
    constructor.
    unfold not. intros. destruct_all. discriminate.
    easy.
    simpl.
    constructor.
    unfold not. intros. destruct_all. discriminate.
    easy.
  }
  {
    rewrite <- app_assoc.
    easy.
  }
  left.
  eexists e, 0, (nones x), x0.
  simpl.
  split.
  induction x.
  constructor.
  simpl.
  constructor.
  unfold not. intros. destruct_all. discriminate.
  easy.
  easy.
}
{
  apply IHf in H. clear IHf.
  destruct H; destruct_all; subst.
  left.
  eexists x, (S x0), x1, x2.
  easy.
  right.
  exists (S x), x0.
  easy.
}
{
  dependent destruction H.
  right.
  exists 0, f.
  easy.
}
Qed.

Program Fixpoint get_choose_trace {E F G} (p : Trace (ThreadLEvent E F)) (q : Trace (ThreadLEvent F G)) (qc : nat -> Trace (LEvent E G)) is {measure (length p + length q)} :
  (forall i,
    projUnderThrSeq (projPoint i eqb p) = projUnderThrSeq (qc i)) ->
  (forall i,
    projOverSeq (projPoint i eqb q) = projOverSeq (qc i)) ->
  (forall i,
    ~In i is -> qc i = nil) ->
  exists r,
    choose_trace qc p q r := _.
Next Obligation.
destruct p, q.
{
  clear get_choose_trace. simpl in *.
  assert (forall i, exists n, qc i = nones n).
  {
    intros.
    apply derive_is_nones.
    symmetry. apply H.
    symmetry. apply H0.
  }
  apply choice in H2.
  destruct_all.
  clear H H0.
  generalize dependent x.
  generalize dependent qc.
  induction is; intros.
  {
    exists nil.
    constructor.
    intros.
    apply H1.
    easy.
  }
  {
    assert (
      exists r,
        choose_trace (F:=F) (fun i => if a =? i then nil else qc i) nil nil r
    ).
    {
      apply IHis with (x:=fun i => if a =? i then 0 else x i).
      intros.
      dec_eq_nats a i.
      rewrite eqb_id.
      easy.
      rewrite eqb_nid.
      rewrite H1.
      easy.
      simpl.
      rewrite help41.
      easy.
      easy.
      intros.
      dec_eq_nats a x0.
      rewrite eqb_id.
      easy.
      rewrite eqb_nid.
      apply H2.
      easy.
    }
    destruct_all.
    exists (thread_nones a (x a) ++ x0).
    clear IHis.
    remember (x a).
    generalize dependent qc.
    generalize dependent x.
    induction n; intros.
    {
      simpl.
      assert (
        qc =
        (fun i : nat => if a =? i then nil else qc i)
      ).
      {
        extensionality i.
        dec_eq_nats a i.
        rewrite eqb_id.
        rewrite H2.
        rewrite <- Heqn.
        easy.
        rewrite eqb_nid.
        easy.
        easy.
      }
      rewrite H0.
      easy.
    }
    {
      simpl in *.
      econstructor.
      apply IHn with (x:=fun i => if i =? a then n else x i).
      rewrite eqb_id.
      easy.
      intros.
      rewrite help41 in H0.
      destruct_all.
      rewrite eqb_nid.
      apply H1.
      rewrite help41.
      easy.
      easy.
      intros.
      dec_eq_nats a x1.
      rewrite eqb_id.
      easy.
      repeat rewrite eqb_nid.
      apply H2.
      easy.
      easy.
      rewrite if_prune.
      easy.
      rewrite H2.
      rewrite <- Heqn.
      easy.
    }
  }
}
{
  destruct t, l; simpl in *.
  {
    eapply get_choose_trace with (p:=nil) in H.
    destruct_all.
    exists x.
    constructor.
    exact H.
    simpl. lia.
    eapply prune_if_projOver.
    exact H0.
    exact H1.
  }
  {
    assert (H0' := H0).
    specialize (H0 n).
    rewrite eqb_id in H0.
    simpl in H0.
    apply get_projOver_nones in H0.
    destruct_all.
    eassert (
      exists r,
        choose_trace (fun i => if n =? i then x0 else qc i) nil q r
    ).
    {
      eapply get_choose_trace.
      simpl. lia.
      intros.
      dec_eq_nats i n.
      rewrite eqb_id.
      specialize (H n).
      rewrite H0 in H.
      rewrite projUnderThrSeq_app, projUnderThrSeq_nones in H.
      easy.
      rewrite eqb_nid.
      apply H.
      easy.
      intros.
      specialize (H0' i).
      dec_eq_nats i n.
      rewrite eqb_id, H0 in *.
      rewrite projOverSeq_app, projOverSeq_nones in H0'.
      simpl in H0'.
      congruence.
      rewrite eqb_nid in *.
      easy.
      easy.
      easy.
      intros.
      apply H1 in H2.
      dec_eq_nats i n.
      rewrite H0 in H2.
      destruct x; simpl in H2; discriminate.
      rewrite eqb_nid.
      easy.
      easy.
    }
    destruct_all.
    exists (thread_nones n x ++ (n, OEvent ev) :: x1).
    clear get_choose_trace H H1 H0'.
    generalize dependent qc.
    induction x; intros.
    {
      simpl.
      econstructor.
      exact H2.
      easy.
    }
    {
      simpl.
      econstructor.
      apply IHx.
      rewrite eqb_id.
      easy.
      rewrite if_prune.
      easy.
      easy.
    }
    apply H.
  }
}
{
  destruct t, l; simpl in *.
  destruct ev.
  {
    assert (H' := H).
    specialize (H n).
    rewrite eqb_id in H.
    simpl in H.
    apply get_projUnderThr_nones in H.
    destruct_all.
    eassert (
      exists r,
        choose_trace (fun i => if n =? i then x0 else qc i) p nil r
    ).
    {
      eapply get_choose_trace.
      simpl. lia.
      intros.
      dec_eq_nats i n.
      rewrite eqb_id.
      specialize (H' n).
      rewrite eqb_id, H, projUnderThrSeq_app, projUnderThrSeq_nones in H'.
      simpl in *.
      congruence.
      specialize (H' i).
      rewrite eqb_nid in *.
      easy.
      easy.
      easy.
      intros.
      specialize (H0 i).
      dec_eq_nats n i.
      rewrite eqb_id.
      rewrite H, projOverSeq_app, projOverSeq_nones in H0.
      easy.
      rewrite eqb_nid.
      easy.
      easy.
      intros.
      apply H1 in H2.
      dec_eq_nats i n.
      rewrite H in H2.
      destruct x; simpl in H2; discriminate.
      rewrite eqb_nid.
      easy.
      easy.
    }
    destruct_all.
    exists (thread_nones n x ++ (n, UEvent (Some e)) :: x1).
    clear H' H0 H1 get_choose_trace.
    generalize dependent qc.
    induction x.
    {
      simpl.
      econstructor.
      exact H2.
      easy.
    }
    {
      simpl.
      intros.
      eapply ChooseSilent with (s:= nones x ++ UEvent (Some e) :: x0).
      apply IHx.
      rewrite eqb_id.
      easy.
      rewrite if_prune.
      easy.
      easy.
    }
    apply H0.
  }
  {
    eapply get_choose_trace in H1.
    destruct_all.
    exists x.
    econstructor.
    exact H1.
    simpl. lia.
    eapply prune_if_projUnderThr with (ev:= UEvent None).
    unfold not. intros. destruct_all. congruence.
    exact H.
    apply H0.
  }
  {
    eapply get_choose_trace in H1.
    destruct_all.
    exists x.
    econstructor.
    exact H1.
    simpl. lia.
    eapply prune_if_projUnderThr with (ev:= OEvent ev).
    unfold not. intros. destruct_all. congruence.
    exact H.
    apply H0.
  }
}
{
  destruct t, t0; simpl in *.
  destruct l, l0; simpl in *.
  2: destruct ev; simpl in *.
  destruct ev; simpl in *.
  {
    eapply get_choose_trace in H1.
    destruct_all.
    exists x.
    econstructor.
    exact H1.
    simpl. lia.
    intros.
    simpl.
    apply H.
    intros.
    specialize (H0 i).
    destruct (i =? n0); easy.
  }
  {
    eapply get_choose_trace in H1.
    destruct_all.
    exists x.
    econstructor.
    exact H1.
    simpl. lia.
    intros.
    specialize (H i).
    destruct (i =? n); easy.
    easy.
  }
  {
    assert (H' := H).
    assert (H0' := H0).
    specialize (H n). rewrite eqb_id in H. simpl in H.
    apply get_projUnder_over in H.
    destruct H; destruct_all.
    (* there is a blocking overlay event *)
    {
      specialize (H0 n). rewrite H2, projOverSeq_app, projOverSeq_nones in H0.
      simpl in *.
      dec_eq_nats n n0.
      {
        admit.
      }
      {
        rewrite eqb_nid in H0.
        admit.
        admit.
      }
    }
    (* there is no blocking overlay event*)
    {
      admit.
    }
  }
  {
    eapply get_choose_trace in H1.
    destruct_all.
    exists x.
    econstructor.
    exact H1.
    simpl. lia.
    intros.
    specialize (H i).
    destruct (i =? n); easy.
    easy.
  }
  {
    eapply get_choose_trace in H1.
    destruct_all.
    exists x.
    econstructor.
    exact H1.
    simpl. lia.
    intros.
    specialize (H i).
    destruct (i =? n); easy.
    easy.
  }
  {
    eapply get_choose_trace in H1.
    destruct_all.
    exists x.
    econstructor.
    exact H1.
    simpl. lia.
    intros.
    specialize (H i).
    destruct (i =? n); easy.
    intros.
    specialize (H0 i).
    simpl.
    dec_eq_nats i n0.
    rewrite eqb_id in *.
    easy.
    rewrite eqb_nid in *.
    easy.
    easy.
    easy.
  }
}
Admitted.

Lemma help57 {E F G} (p : Trace (ThreadLEvent E F)) (q : Trace (ThreadLEvent F G)) :
  forall qc : nat -> Trace (LEvent E G),
  (forall i,
    projUnderThrSeq (projPoint i eqb p) = projUnderThrSeq (qc i)) ->
  (forall i,
    projOverSeq (projPoint i eqb q) = projOverSeq (qc i)) ->
  (forall i,
    ~In i (map fst p ++ map fst q) -> qc i = nil) ->
  exists r,
    Interleave qc r /\
    same_threads (projUnderThr p) (projUnderThr r) /\
    same_threads (projOver q) (projOver r).
intros.
cut (
  exists r : Trace (ThreadLEvent E G),
    (forall i, projPoint i eqb r = qc i) /\
    same_threads (projUnderThr p) (projUnderThr r) /\
    same_threads (projOver q) (projOver r)
).
{
  intros.
  destruct_all.
  exists x.
  repeat split.
  rewrite constr_interleave.
  easy.
  easy.
  easy.
}
assert (
  exists r,
    choose_trace qc p q r
).
{
  eapply get_choose_trace.
  easy.
  easy.
  exact H1.
}
destruct_all.
exists x.
repeat split.
{
  clear H0 H1 H.
  induction H2.
  {
    symmetry.
    apply H.
  }
  {
    simpl.
    intros.
    dec_eq_nats i i0.
    rewrite eqb_id.
    rewrite H.
    f_equal.
    specialize (IHchoose_trace i0).
    rewrite eqb_id in IHchoose_trace.
    easy.
    specialize (IHchoose_trace i0).
    rewrite eqb_nid in *.
    easy.
    easy.
    easy.
  }
  {
    simpl.
    intros.
    specialize (IHchoose_trace i0).
    dec_eq_nats i i0.
    rewrite eqb_id in *.
    rewrite H.
    congruence.
    rewrite eqb_nid in *.
    easy.
    easy.
    easy.
  }
  {
    intros.
    specialize (IHchoose_trace i0).
    dec_eq_nats i i0.
    simpl.
    rewrite eqb_id in *.
    rewrite H.
    congruence.
    simpl.
    rewrite eqb_nid in *.
    easy.
    easy.
    easy.
  }
  {
    easy.
  }
  {
    easy.
  }
  {
    easy.
  }
}
{
  clear H1 H0.
  induction H2.
  {
    constructor.
  }
  {
    simpl in *.
    constructor.
    apply IHchoose_trace.
    intros.
    assert (H' := H).
    specialize (H i).
    rewrite eqb_id, H0 in H.
    simpl in *.
    dec_eq_nats i i0.
    rewrite eqb_id.
    congruence.
    rewrite eqb_nid.
    specialize (H' i0).
    rewrite eqb_nid in H'.
    easy.
    easy.
    easy.
  }
  {
    simpl in *.
    apply IHchoose_trace.
    intros.
    assert (H' := H).
    specialize (H i).
    rewrite H0 in H.
    simpl in *.
    dec_eq_nats i i0.
    rewrite eqb_id.
    easy.
    rewrite eqb_nid.
    apply H'.
    easy.
  }
  {
    simpl in *.
    apply IHchoose_trace.
    intros.
    assert (H' := H).
    specialize (H i).
    rewrite H0 in H.
    simpl in *.
    dec_eq_nats i i0.
    rewrite eqb_id.
    easy.
    rewrite eqb_nid.
    apply H'.
    easy.
  }
  {
    simpl in *.
    apply IHchoose_trace.
    intros.
    assert (H' := H).
    specialize (H i0).
    dec_eq_nats i0 i.
    rewrite eqb_id in *.
    easy.
    rewrite eqb_nid in *.
    easy.
    easy.
  }
  {
    simpl in *.
    apply IHchoose_trace.
    intros.
    assert (H' := H).
    specialize (H i0).
    dec_eq_nats i0 i.
    rewrite eqb_id in *.
    easy.
    rewrite eqb_nid in *.
    easy.
    easy.
  }
  {
    apply IHchoose_trace.
    easy.
  }
}
{
  clear H H1.
  induction H2.
  {
    constructor.
  }
  {
    simpl in *.
    apply IHchoose_trace.
    intros.
    assert (H0' := H0).
    specialize (H0 i).
    rewrite H in H0.
    simpl in *.
    dec_eq_nats i i0.
    rewrite eqb_id in *.
    easy.
    rewrite eqb_nid.
    apply H0'.
    easy.
  }
  {
    simpl in *.
    constructor.
    apply IHchoose_trace.
    intros.
    dec_eq_nats i i0.
    specialize (H0 i0).
    rewrite eqb_id, H in *.
    simpl in *.
    congruence.
    specialize (H0 i0).
    rewrite eqb_nid in *.
    easy.
    easy.
    easy.
  }
  {
    simpl in *.
    apply IHchoose_trace.
    intros.
    dec_eq_nats i i0.
    specialize (H0 i0).
    rewrite eqb_id, H in *.
    easy.
    rewrite eqb_nid.
    apply H0.
    easy.
  }
  {
    apply IHchoose_trace.
    easy.
  }
  {
    apply IHchoose_trace.
    easy.
  }
  {
    simpl in *.
    apply IHchoose_trace.
    intros.
    dec_eq_nats i i0.
    specialize (H0 i0).
    rewrite eqb_id in *.
    easy.
    specialize (H0 i0).
    rewrite eqb_nid in *.
    easy.
    easy.
  }
}
Qed.

Lemma steps_no_over {E F} impl :
  forall p : Trace (ThreadLEvent E F),
  projOver p = nil ->
  forall t,
  Steps (ThreadsStep impl) allIdle p t ->
  p = nil.
intros.
destruct p.
easy.
exfalso.
induction p.
destruct t0, l; simpl in *.
dependent destruction H0.
unfold ThreadsStep in H0.
dependent destruction H0.
simpl in *.
dependent destruction H0.
congruence.
destruct t0, l.
simpl in *.
dependent destruction H0.
unfold ThreadsStep in H0.
dependent destruction H0.
simpl in *.
dependent destruction H0.
simpl in *.
destruct a, l; simpl in *.
congruence.
congruence.
Qed.

Lemma map_split {A B} {f : A -> B} {xs ys} :
  map f (xs ++ ys) = map f xs ++ map f ys.
induction xs.
easy.
simpl.
f_equal.
easy.
Qed.

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
symmetry in H.
destruct x, s.
simpl in *.
simpl.
destruct_all.
cut (
  forall i, exists st, exists q,
    (~ In i (dedup (map fst x1 ++ map fst x0)) -> q = nil) /\
    projOverSeq (projPoint i eqb x0) = projOverSeq q /\
    projUnderThrSeq (projPoint i eqb x1) = projUnderThrSeq q /\
    Steps (ThreadStep (impl |> impl')) (substTS impl (allIdle i)) q st
).
{
  intros.
  repeat (apply choice in H5; destruct_all).
  exists (x, s).
  simpl in *.
  eassert (
    exists q,
      Interleave x2 q /\
      same_threads (projUnderThr x1) (projUnderThr q) /\
      same_threads (projOver x0) (projOver q)).
  {
    {
      destruct_all.
      subst.
      eapply help57.
      {
        intros.
        specialize (H5 i).
        easy.
      }
      {
        intros.
        specialize (H5 i).
        easy.
      }
      {
        intros.
        specialize (H5 i).
        destruct H5.
        apply H5.
        rewrite <- dedup_correct.
        easy.
      }
    }
  }
  destruct_all.
  exists x3.
  repeat split.
  {
    eapply full_projOver.
    intros.
    specialize (H5 i).
    destruct_all.
    exact H9.
    easy.
    easy.
  }
  {
    assert (projUnderThr x1 = projUnderThr x3).
    eapply full_projUnderThr.
    intros.
    specialize (H5 i).
    destruct_all.
    exact H10.
    easy.
    easy.
    rewrite <- H9.
    easy.
  }
  {
    unfold ThreadsStep.
    rewrite (decompPointSteps eqb (ThreadStep (impl |> impl'))).
    intros.
    specialize (H5 i).
    destruct_all.
    erewrite constr_interleave in H6.
    specialize (H6 i).
    rewrite <- H6.
    easy.
    exact threadDecEq.
  }
  dependent destruction H6.
  left.
  easy.
  right.
  specialize (H5 i).
  destruct_all.
  rewrite H6 in H12.
  dependent destruction H12.
  unfold ThreadStep in H6.
  destruct e.
  dependent destruction H6.
  dependent destruction H6.
  repeat econstructor.
}
intros.
assert (In i (dedup (map fst x1 ++ map fst x0)) \/ ~In i (dedup (map fst x1 ++ map fst x0))) by apply excluded_middle.
destruct H5.
2:{
  assert (projPoint i eqb x1 = nil).
  {
    rewrite <- dedup_correct in H5.
    rewrite In_split in H5.
    rewrite help41 in H5.
    destruct_all.
    rewrite proj_notin.
    easy.
    easy.
  }
  assert (projPoint i eqb x0 = nil).
  {
    rewrite <- dedup_correct in H5.
    rewrite In_split in H5.
    rewrite help41 in H5.
    destruct_all.
    rewrite proj_notin.
    easy.
    easy.
  }
  exists Idle, nil.
  rewrite H6.
  rewrite H7.
  repeat split.
  constructor.
}
rewrite (decompPointSteps eqb (ThreadStep impl)) in H3.
rewrite (decompPointSteps eqb (ThreadStep impl')) in H1.
specialize (H3 i).
specialize (H1 i).
2: exact threadDecEq.
2: exact threadDecEq.
apply (seq_proj_assoc i) in H.
(* generalize dependent (projPoint i eqb x1).
generalize dependent (projPoint i eqb x0). *)
intros.
(* rename l into tH.
rename l0 into tL. *)
apply get_assoc_view in H.
(* move tL after tH.
move H3 after H1. *)
cut (
exists (st : ThreadState E G) (q : list (LEvent E G)),
  projOverSeq (projPoint i eqb x0) = projOverSeq q /\
  projUnderThrSeq (projPoint i eqb x1) = projUnderThrSeq q /\
  Steps (ThreadStep (impl |> impl')) (substTS impl (allIdle i)) q st
).
{
  intros.
  destruct_all.
  exists x, x2.
  easy.
}
subst.
eapply help66 in H.
3: exact H3.
3: exact H1.
2: constructor.
subst.
simpl.
destruct_all.
exists x, x2.
easy.
Qed.