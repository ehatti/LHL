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
  EuttRefinesSetup.

From Coq Require Import
  Program.Equality
  Relations.Relation_Operators
  Logic.PropExtensionality
  Logic.FunctionalExtensionality
  Logic.ClassicalChoice
  Lists.List.

From Paco Require Import
  paco.

Lemma threadDecEq {T} : @IsEqDec (Name T) eqb.
unfold eqb.
constructor.
{
  split; intro.
  { destruct (classicT (i = j)); easy. }
  {
    subst.
    destruct (classicT (j = j)); easy.
  }
}
{
  split; intros;
  destruct (classicT (i = j)); easy.
}
Qed.

(* Basic Refinement Properties *)

Lemma specRefines_trans {T E} :
  forall (spec1 spec2 spec3 : Spec T E),
    specRefines spec1 spec2 -> specRefines spec2 spec3 -> 
    specRefines spec1 spec3.
Proof. 
  intros. unfold specRefines in *.  eapply TransUtil.Incl_trans.
  apply H. apply H0.
Qed.

Lemma layerRefines_trans {T E1 E2 E3 F} :
  forall (lay1 : Layer T E1 F) (lay2 : Layer T E2 F) (lay3 : Layer T E3 F),
    layerRefines lay1 lay2 -> layerRefines lay2 lay3 ->
    layerRefines lay1 lay3.
Proof.
  intros. unfold layerRefines, specRefines in *.
  eapply TransUtil.Incl_trans.
  apply H. apply H0.
Qed.

(* implEq implies refinement *)

Inductive implEq_rel {E F} : ThreadState E F -> ThreadState E F -> Prop :=
| IEIdle :
    implEq_rel Idle Idle
| IECont A (om : F A) p q :
    progEq p q ->
    implEq_rel (Cont om p) (Cont om q)
| IEUCall A (om : F A) B (um : E B) f g :
    (forall x, progEq (f x) (g x)) ->
    implEq_rel (UCall om um f) (UCall om um g).

Lemma swapEx {A B} {P : A -> B -> Prop} :
  (exists x y, P x y) ->
  (exists y x, P x y).
intros. destruct_all. repeat eexists. exact H.
Qed.

Theorem implEq_refines : 
  forall T E F spec impl impl',
  @implEq E F impl impl' ->
  specRefines (overObj (T:=T) (spec :> impl)) (overObj (spec :> impl')).
unfold specRefines, Incl, IsTraceOfSpec. intros. destruct_all.
repeat rewrite projInterSteps in *. apply swapEx.
destruct_all. subst. exists x0. repeat split; try easy.
clear H2. cbn in *.
cut (
  exists y,
    InterSteps impl' (allIdle, Init spec) x0 y
).
{
  intros. destruct_all. exists x1.
  repeat split; try easy.
  dependent destruction H0.
  left. easy.
  unfold InterStep, ThreadsStep in H0. destruct_all.
  dependent destruction H0. cbn in *.
  unfold ThreadStep in H0. destruct ev, l; cbn in *.
  dependent destruction H0.
  right. repeat econstructor.
}
assert (forall i, implEq_rel (@allIdle T E F i) (@allIdle T E F i)).
constructor.
revert H1 H0.
cut (
  forall t r s,
  (forall i : Name T, @implEq_rel E F (t i) (r i)) ->
  InterSteps impl (t, s) x0 x ->
  exists y : InterState F spec, InterSteps impl' (r, s) x0 y
).
{
  intros. eapply H0 in H2. destruct_all.
  exists x1. exact H2. easy.
}
cut (
  forall t r i e t',
  implEq_rel (t i) (r i) ->
  ThreadsStep impl t (i, e) t' ->
  exists r',
    implEq_rel (t' i) (r' i) /\
    ThreadsStep (T:=T) impl' r (i, e) r'
).
{
  intros.
  generalize dependent t. generalize dependent r.
  generalize dependent s.
  induction x0; cbn in *; intros.
  {
    repeat econstructor.
  }
  {
    dependent destruction H2. destruct st''.
    unfold InterStep in H2. destruct_all. destruct a. cbn in *.
    assert (differ_pointwise t0 t n).
    { unfold ThreadsStep in H2. dependent destruction H2. easy. }
    apply H0 with (r:=r) in H2. 2: easy.
    destruct_all.
    apply IHx0 with (r:=x) in H3.
    2:{
      intros. specialize (H1 i). dec_eq_nats i n.
      easy.
      rewrite <- H5.
      unfold ThreadsStep in H6. dependent destruction H6. cbn in *.
      rewrite <- H4; easy. easy.
    }
    destruct_all. exists x1.
    eapply StepsMore with (st'':=(x, s0)).
    2: easy.
    unfold InterStep. cbn. easy.
  }
}
unfold ThreadsStep. cbn. intros.
dependent destruction H1. unfold ThreadStep in H1.
cbn in *. destruct e; cbn in *.
dependent destruction H1.
{
  rewrite H1 in *. dependent destruction H0.
  rewrite <- x2. dependent destruction H0.
  exists (fun j => if i =? j then UCall om um f2 else r j).
  split.
  { rewrite eqb_id. econstructor. easy. }
  {
    econstructor. econstructor.
    cbn. symmetry. exact x.
    cbn. rewrite eqb_id. easy.
    cbn. intros. rewrite eqb_nid; easy.
  }
}
{
  rewrite H1 in *. dependent destruction H0.
  rewrite <- x2.
  exists (fun j => if i =? j then Cont om (g v) else r j).
  split.
  { rewrite eqb_id. econstructor. easy. }
  {
    econstructor. econstructor.
    cbn. symmetry. exact x.
    cbn. rewrite eqb_id. easy.
    cbn. intros. rewrite eqb_nid; easy.
  }
}
{
  rewrite H1 in *. dependent destruction H0.
  rewrite <- x2. dependent destruction H0.
  exists (fun j => if i =? j then Cont om p2 else r j).
  split.
  { rewrite eqb_id. econstructor. easy. }
  {
    econstructor. econstructor.
    cbn. symmetry. exact x.
    cbn. rewrite eqb_id. easy.
    cbn. intros. rewrite eqb_nid; easy.
  }
}
dependent destruction H1.
{
  exists (fun j => if i =? j then Cont m (impl' A m) else r j).
  split.
  { rewrite eqb_id. rewrite <- x. constructor. apply H. }
  {
    econstructor. econstructor.
    cbn. rewrite H1 in H0. dependent destruction H0. easy.
    cbn. rewrite eqb_id. easy.
    cbn. intros. rewrite eqb_nid; easy.
  }
}
{
  exists (fun j => if i =? j then Idle else r j).
  split.
  { rewrite eqb_id. rewrite <- x. constructor. }
  {
    econstructor. econstructor.
    cbn. rewrite H1 in H0. do 2 dependent destruction H0. easy.
    cbn. rewrite eqb_id. easy.
    cbn. intros. rewrite eqb_nid; easy.
  }
}
Qed.

(* Eutt implies refinement *)

Require Import Coq.Program.Wf.
Require Import Lia.

Definition ends_in_oev {T E F} (p : Trace (ThreadLEvent T E F)) :=
  exists q i e, p = q ++ cons (i, OEvent e) nil.

Definition ends_in_oev_seq {E F} (p : Trace (LEvent E F)) :=
  exists q e, p = q ++ cons (OEvent e) nil.


Lemma ends_oev_cons {T E F} :
  forall p e,
  @ends_in_oev T E F p ->
  @ends_in_oev T E F (e :: p).
unfold ends_in_oev.
intros.
destruct_all.
subst.
exists (e :: x), x0, x1.
easy.
Qed.

Theorem eutt_layerRefines {T E F} : 
  forall (spec : Spec T E) (impl impl' : Impl E F), 
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
clear H1. unfold ThreadsStep, ThreadLEvent, ThreadsSt in H0.
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
    | UCall om um k =>
        exists k',
          x0' = UCall om um k' /\
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
    exists 0, (UCall om um k').
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
        clear H6.
        generalize dependent p'.
        induction x0; simpl; intros.
        {
          dependent destruction H4.
        }
        {
          dependent destruction H4.
          unfold ThreadStep in H3. dependent destruction H3.
          eapply IHx0.
          exact H4.
        }
      }
      {
        destruct p1.
        destruct_all.
        subst.
        exists (S x0), (Cont m0 (Bind e0 x2)).
        split.
        exists x2. easy.
        simpl.
        econstructor.
        eapply USilentThreadStep.
        easy. easy. easy.
        subst.
        exists (S x0), (Cont m0 (Return a)).
        split.
        easy.
        simpl.
        econstructor.
        eapply USilentThreadStep.
        easy. easy. easy.
        subst.
        exists (S x0), (Cont m0 (NoOp p1)).
        split.
        easy.
        simpl.
        econstructor.
        eapply USilentThreadStep.
        easy. easy. easy.
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
  eexists (UCall _ _ x0).
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
  eexists (Cont _ (x0 v)).
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

Lemma help {T E F} :
  forall (p : Trace (ThreadLEvent T E F)),
  projSilent (projUnder p) = projUnderThr p.
intros.
induction p.
easy.
destruct a, l, ev.
simpl.
rewrite IHp.
all: easy.
Qed.

Theorem mkLayer_monotonic {T E F} :
  forall (spec spec' : Spec T E) (impl : Impl E F),
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
easy.
Qed.

Fixpoint projOverSeq {E F} (p : Trace (LEvent E F)) : Trace (Event F) :=
  match p with
  | nil => nil
  | cons (OEvent e) p => cons e (projOverSeq p)
  | cons _ p => projOverSeq p
  end.

Fixpoint projUnderThrSeq {E F} (p : Trace (LEvent E F)) : Trace (Event E) :=
  match p with
  | nil => nil
  | cons (UEvent (Some e)) p => cons e (projUnderThrSeq p)
  | cons _ p => projUnderThrSeq p
  end.

Lemma projUnderThrSeq_app {E F} :
  forall p q : Trace (LEvent E F),
  projUnderThrSeq (p ++ q) = projUnderThrSeq p ++ projUnderThrSeq q.
intros. induction p. easy.
cbn. destruct a, ev;
cbn; f_equal; easy.
Qed.

Import ListNotations.

Inductive Interleave {T E F} :
  (Name T -> Trace (LEvent E F)) ->
  Trace (ThreadLEvent T E F)
  -> Prop :=
| INil c :
    (forall i, c i = []) ->
    Interleave c []
| ICons c c' q p i e :
    c i = e :: q ->
    c' i = q ->
    differ_pointwise c c' i ->
    Interleave c' p ->
    Interleave c ((i, e) :: p).

Lemma Interleave_iso {T E F} :
  forall c : Name T -> Trace (LEvent E F),
  forall p : Trace (ThreadLEvent T E F),
  Interleave c p = (forall i, projPoint i eqb p = c i).
Proof.
  intros. apply propositional_extensionality.
  split; intros.
  {
    induction H.
    { now rewrite H. }
    {
      cbn in *.
      dec_eq_nats i0 i.
      { rewrite eqb_id, H. now f_equal. }
      { now rewrite eqb_nid, <- H1. }
    }
  }
  {
    generalize dependent c.
    induction p; cbn; intros.
    { intros. now constructor. }
    {
      destruct a; cbn in *.
      assert (H' := H).
      specialize (H n).
      rewrite eqb_id in H.
      eapply ICons with
        (c':=fun i =>
          if i =? n then
            projPoint n eqb p
          else
            c i).
      { symmetry. exact H. }
      { now rewrite eqb_id. }
      {
        unfold differ_pointwise.
        intros. now rewrite eqb_nid.
      }
      {
        apply IHp.
        intros.
        dec_eq_nats i n.
        {
          rewrite eqb_id. easy.
        }
        {
          specialize (H' i).
          now rewrite eqb_nid in *.
        }
      }
    }
  }
Qed.

Fixpoint projUnderSeq {E F} (p : Trace (LEvent E F)) : Trace (option (Event E)) :=
  match p with
  | [] => []
  | UEvent e :: p => e :: projUnderSeq p
  | _ :: p => projUnderSeq p
  end.

Lemma pullout_over {T E F} :
  forall i : Name T, forall e : Event F,
  forall q : Trace (ThreadLEvent T E F),
  forall p,
  projOver q = (i, e) :: p ->
  exists ql qr,
    q = ql ++ [(i, OEvent e)] ++ qr /\
    projOver ql = [] /\
    projOver qr = p.
Proof.
  intros i e q.
  induction q; cbn.
  { now intros. }
  {
    destruct a, l; cbn.
    {
      intros.
      apply IHq in H.
      destruct_all. subst.
      now exists ((n, UEvent ev) :: x), x0.
    }
    {
      intros.
      ddestruct H.
      now exists [], q.
    }
  }
Qed.

Axiom indef :
  forall {A} {P : A -> Prop}, (exists x, P x) -> {x | P x}.

Arguments exist {A P}.

From Equations Require Import Equations.

Equations sum_f {T} (i : Name T) (c : Name T -> nat)
  : nat by wf (proj1_sig i) lt :=
sum_f (exist 0 prf) c := c (exist 0 prf);
sum_f (exist (S i) prf) c := c (exist (S i) prf) + sum_f (exist i _) c.

Next Obligation. lia. Qed.

Lemma pullout_under_seq {E F} :
  forall e : option (Event E),
  forall q : Trace (LEvent E F),
  forall p,
  projUnderSeq q = e :: p ->
  exists ql qr,
    q = ql ++ [(UEvent e)] ++ qr /\
    projUnderSeq ql = [] /\
    projUnderSeq qr = p.
Proof.
  intros e q.
  induction q; cbn.
  { now intros. }
  {
    destruct a; cbn.
    {
      destruct ev; intros.
      {
        ddestruct H.
        now exists [], q.
      }
      {
        ddestruct H.
        now exists [], q.
      }
    }
    {
      intros.
      apply IHq in H.
      destruct_all. subst.
      now exists ((OEvent ev) :: x), x0.
    }
  }
Qed.

Import ListNotations.

Inductive assoc_traces {T E F G} : Trace (ThreadLEvent T F G) -> Trace (ThreadLEvent T E F) -> Prop :=
| ANil :
  assoc_traces [] []
| AGEvt i e q p :
  assoc_traces q p ->
  assoc_traces ((i, OEvent e) :: q) p
| AFEvt i e q p :
  assoc_traces q p ->
  assoc_traces ((i, UEvent (Some e)) :: q) ((i, OEvent e) :: p)
| AFSil i q p :
  assoc_traces q p ->
  assoc_traces ((i, UEvent None) :: q) p
| AEEvt i e q p :
  assoc_traces q p ->
  assoc_traces q ((i, UEvent e) :: p)
| AESil i q p :
  assoc_traces q p ->
  assoc_traces q ((i, UEvent None) :: p).

Equations get_assoc_traces {T E F G} (p : Trace (ThreadLEvent T E F)) (q : Trace (ThreadLEvent T F G)) : 
  projOver p = projUnderThr q ->
  assoc_traces q p
  by wf (length p + length q) lt :=
get_assoc_traces p q H := _.
Next Obligation.
intros.
destruct p, q.
constructor.
{
  destruct t.
  destruct l; simpl in *.
  destruct ev.
  congruence.
  constructor.
  apply get_assoc_traces.
  simpl. easy.
  constructor.
  constructor.
  apply get_assoc_traces.
  simpl. easy.
  simpl. lia.
}
{
  destruct t.
  destruct l; simpl in *.
  destruct ev.
  constructor.
  apply get_assoc_traces.
  simpl. easy.
  constructor.
  constructor.
  apply get_assoc_traces.
  simpl. easy.
  simpl. lia.
  easy.
}
{
  destruct t0, t.
  destruct l, l0.
  destruct ev, ev0.
  simpl in *.
  constructor.
  apply get_assoc_traces.
  simpl. easy.
  simpl in *.
  constructor.
  constructor.
  apply get_assoc_traces.
  simpl. easy.
  simpl in *. lia.
  constructor.
  apply get_assoc_traces.
  simpl. easy.
  simpl in *. lia.
  constructor.
  constructor.
  apply get_assoc_traces.
  simpl. easy.
  simpl in *. lia.
  {
    destruct ev.
    {
      ddestruct H.
      constructor.
      apply get_assoc_traces.
      easy.
      simpl. lia.
    }
    {
      constructor.
      apply get_assoc_traces.
      easy.
      simpl. lia.
    }
  }
  {
    cbn in *.
    constructor.
    constructor.
    apply get_assoc_traces.
    easy.
    lia.
  }
  {
    cbn in *.
    constructor.
    apply get_assoc_traces.
    easy.
    simpl. lia.
  }
}
Qed.

Inductive assoc_states {E F G} {impl : Impl E F} {impl' : Impl F G} : ThreadState E F -> ThreadState F G -> ThreadState E G -> Prop :=
| ASGCall :
    assoc_states Idle Idle Idle
| ASFCall A B (gm : G A) (fm : F B) k :
    assoc_states Idle (Cont gm (Bind fm k)) (Cont gm (NoOp (bindSubstProg impl k (impl _ fm))))
| ASFNoOp A m p :
  assoc_states Idle (Cont m (NoOp p)) (Cont m (NoOp (A:=A) (substProg impl p)))
| ASECall A R B gm fm em ek fk :
    assoc_states (Cont fm (Bind em ek)) (UCall gm fm fk) (Cont gm (Bind (A:=A) (B:=B) em (fun x => bindSubstProg (R:=R) impl fk (ek x))))
| ASENoOp A R k om p um :
    assoc_states (Cont um (NoOp p)) (UCall om um k) (Cont om (NoOp (A:=A) (bindSubstProg (R:=R) impl k p)))
| ASEBind A B R gm fm em ek fk :
    assoc_states (UCall (A:=A) fm em ek) (UCall (B:=B) gm fm fk) (UCall gm em (fun x => bindSubstProg (R:=R) impl fk (ek x)))
| ASERet A B gm fm v fk :
    assoc_states (Cont fm (Return v)) (UCall (A:=B) gm fm fk) (Cont (A:=A) gm (NoOp (substProg impl (fk v))))
| ASFRet A (gm : G A) v :
    assoc_states Idle (Cont gm (Return v)) (Cont gm (Return v))
.
Arguments assoc_states {E F G} impl impl'.

Theorem layerRefines_VComp_assoc {T E F G} : 
  forall  (spec : Spec T E) (impl : Impl E F) (impl' : Impl F G),
    layerRefines ((overObj (spec :> impl)) :> impl') ((spec :> impl) :|> impl').
Proof.
  unfold layerRefines, specRefines, Incl, IsTraceOfSpec.
  intros. destruct_all.
  repeat rewrite decompOverObj in *.
  destruct_all. subst. simpl (USpec _) in H0.
  rewrite decompOverObj in H0. destruct_all.
  cbn in *.
  cut (
    exists tht q,
      projOver x0 = projOver q /\
      projUnderThr x1 = projUnderThr q /\
      Steps (ThreadsStep (impl |> impl')) allIdle q tht
  ).
  {
    intros. destruct_all.
    exists (x2, snd (snd x)), x3. cbn.
    split. easy.
    split. now rewrite <- H6.
    split. easy.
    {
      clear H4.
      unfold IsOverObjTrace in *.
      unfold ThreadsStep, ThreadStep in H7.
      destruct H2; destruct_all;
      subst; cbn in *.
      {
        ddestruct H7.
        { now left. }
        {
          destruct ev. cbn in *.
          destruct l.
          {
            destruct ev.
            {
              cbn in *. ddestruct H2.
              cbn in *. ddestruct H2.
            }
            {
              cbn in *. ddestruct H2.
              cbn in *. ddestruct H2.
            }
          }
          { easy. }
        }
      }
      {
        right.
        ddestruct H7. ddestruct H2.
        destruct ev, l; cbn in *.
        { ddestruct H2. }
        { repeat econstructor. }
      }
    }
  }
  clear - H H1 H3.
  destruct x, s. cbn in *.
  rename x0 into q, x1 into p.
  rename t0 into pt, t into qt.
  clear - H H3 H1.
  assert (
    forall i : Name T,
      assoc_states impl impl' (allIdle i) (allIdle i) (allIdle i)).
  { intros. constructor. }
  assert (
    assoc_traces q p
  ).
  {
    now apply get_assoc_traces.
  }
  generalize dependent (@allIdle T F G).
  generalize dependent (@allIdle T E F).
  generalize dependent (@allIdle T E G).
  unfold ThreadsStep.
  clear H. induction H2;
  cbn; intros; assert (H0' := H0);
  try specialize (H0' i).
  {
    ddestruct H1. ddestruct H3.
    exists t, []. repeat constructor.
  }
  {
    ddestruct H1. ddestruct H.
    unfold ThreadStep in H. cbn in *.
    ddestruct H.
    {
      rewrite H in H0'.
      ddestruct H0'.
      eapply IHassoc_traces
        with (t:=fun j =>
          if i =? j then
            Cont m (substProg impl (impl' A m))
          else
            t j)
        in H3.
      2:{ exact H1. }
      2:{
        intros.
        specialize (H4 i0).
        dec_eq_nats i0 i.
        {
          rewrite <- x1, eqb_id, <- x0.
          rewrite frobProgId with (p:= substProg _ _).
          remember (impl' A m). destruct p0; cbn; try constructor.
        }
        { now rewrite eqb_nid, <- H0. }
      }
      destruct_all.
      exists x2, ((i, OEvent (CallEv m)) :: x3).
      split.
      { now rewrite H3. }
      split.
      { easy. }
      {
        econstructor.
        2: exact H6.
        constructor; cbn.
        {
          rewrite <- x, eqb_id.
          now constructor.
        }
        { intros. now rewrite eqb_nid. }
      }
    }
    {
      rewrite H in H0'.
      ddestruct H0'.
      eapply IHassoc_traces
        with (t:=fun j =>
          if i =? j then
            Idle
          else
            t j)
        in H3.
      2:{ exact H1. }
      2:{
        intros.
        dec_eq_nats i0 i.
        {
          rewrite eqb_id, <- x1, <- x0.
          constructor.
        }
        {
          specialize (H4 i0).
          now rewrite eqb_nid, <- H0.
        }
      }
      destruct_all.
      exists x2, ((i, OEvent (RetEv m v)) :: x3).
      split.
      { now rewrite H3. }
      split.
      { easy. }
      {
        econstructor.
        2: exact H6.
        econstructor; cbn.
        {
          rewrite <- x, eqb_id.
          now constructor.
        }
        { intros. now rewrite eqb_nid. }
      }
    }
  }
  {
    ddestruct H3. ddestruct H.
    ddestruct H1. ddestruct H1.
    cbn in *. ddestruct H; ddestruct H1;
    rewrite H1, H in H0'; ddestruct H0'.
    {
      eapply IHassoc_traces
        with (t:=fun j =>
          if i =? j then
            Cont om (bindSubstProg impl k (impl _ m))
          else
            t j)
        in H3.
      2:{ exact H5. }
      2:{
        intros.
        dec_eq_nats i0 i.
        {
          rewrite <- x0, <- x1, <- x, eqb_id.
          rewrite frobProgId with (p:= bindSubstProg _ _ _).
          destruct (impl A m); cbn; constructor.
        }
        {
          specialize (H6 i0).
          now rewrite <- H4, <- H0, eqb_nid.
        }
      }
      destruct_all.
      exists x2, ((i, UEvent None) :: x3).
      split. easy.
      split. easy.
      econstructor.
      2: exact H8.
      constructor; cbn.
      {
        rewrite eqb_id, <- x.
        now econstructor.
      }
      { intros. now rewrite eqb_nid. }
    }
    {
      eapply IHassoc_traces
        with (t:=fun j =>
          if i =? j then
            Cont om (substProg impl (k v))
          else
            t j)
        in H3.
      2:{ exact H5. }
      2:{
        intros.
        dec_eq_nats i0 i.
        {
          rewrite <- x0, <- x1, <- x.
          rewrite frobProgId with (p:= substProg _ _).
          rewrite eqb_id. destruct (k v); constructor.
        }
        {
          rewrite <- H0, <- H4, eqb_nid.
          apply H6. easy. easy. easy.
        }
      }
      destruct_all.
      exists x2, ((i, UEvent None) :: x3).
      split. easy.
      split. easy.
      econstructor.
      2: exact H8.
      constructor; cbn.
      {
        rewrite eqb_id, <- x.
        now econstructor.
      }
      { intros. now rewrite eqb_nid. }
    }
  }
  {
    ddestruct H1. ddestruct H.
    cbn in *. ddestruct H.
    rewrite H in H0'. ddestruct H0'.
    eapply IHassoc_traces
      with (t:=fun j =>
        if i =? j then
          Cont om (substProg impl p0)
        else
          t j)
      in H3.
    2:{ exact H1. }
    2:{
      intros.
      dec_eq_nats i0 i.
      {
        rewrite <- x1, <- x0, <- x, eqb_id.
        rewrite frobProgId with (p:= substProg _ _).
        destruct p0; constructor.
      }
      { now rewrite eqb_nid, <- H0. }
    }
    destruct_all.
    exists x2, ((i, UEvent None) :: x3).
    split. easy.
    split. easy.
    econstructor.
    2: exact H6.
    constructor; cbn.
    {
      rewrite eqb_id, <- x.
      now econstructor.
    }
    { intros. now rewrite eqb_nid. }
  }
  {
    ddestruct H3. ddestruct H.
    cbn in *. ddestruct H.
    {
      rewrite H in H0'. ddestruct H0'.
      eapply IHassoc_traces
        with (t:=fun j =>
          if i =? j then
            UCall gm um (fun x => bindSubstProg impl fk (k x))
          else
            t j)
        in H3.
      2: exact H1.
      2:{
        intros.
        dec_eq_nats i0 i.
        {
          rewrite <- x0, <- x1, <- x, eqb_id.
          constructor.
        }
        { now rewrite <- H0, eqb_nid. }
      }
      destruct_all.
      exists x2, ((i, UEvent (Some (CallEv um))) :: x3).
      split. easy.
      split. now rewrite H5.
      econstructor.
      2: exact H6.
      constructor; cbn.
      {
        rewrite eqb_id, <- x.
        now econstructor.
      }
      { intros. now rewrite eqb_nid. }
    }
    {
      rewrite H in H0'. ddestruct H0'.
      eapply IHassoc_traces
        with (t:=fun j =>
          if i =? j then
            Cont gm (bindSubstProg impl fk (k v))
          else
            t j)
        in H3.
      2: exact H1.
      2:{
        intros.
        dec_eq_nats i0 i.
        {
          rewrite eqb_id, <- x1, <- x0.
          rewrite frobProgId with (p:= bindSubstProg _ _ _).
          destruct (k v); constructor.
        }
        { now rewrite eqb_nid, <- H0. }
      }
      destruct_all.
      exists x2, ((i, UEvent (Some (RetEv um v))) :: x3).
      split. easy.
      split. now rewrite H5.
      econstructor.
      2: exact H6.
      constructor; cbn.
      {
        rewrite eqb_id, <- x.
        now econstructor.
      }
      { intros. now rewrite eqb_nid. }
    }
    {
      rewrite H in H0'. ddestruct H0'.
      eapply IHassoc_traces
        with (t:=fun j =>
          if i =? j then
            Cont om0 (bindSubstProg impl k p0)
          else
            t j)
        in H3.
      2: exact H1.
      2:{
        intros.
        dec_eq_nats i0 i.
        {
          rewrite eqb_id, <- x0, <- x1.
          rewrite frobProgId with (p:= bindSubstProg _ _ _).
          destruct p0; constructor.
        }
        { now rewrite eqb_nid, <- H0. }
      }
      destruct_all.
      exists x2, ((i, UEvent None) :: x3).
      split. easy.
      split. easy.
      econstructor.
      2: exact H6.
      constructor; cbn.
      {
        rewrite eqb_id, <- x.
        now econstructor.
      }
      { intros. now rewrite eqb_nid. }
    }
  }
  {
    ddestruct H3. ddestruct H.
    cbn in *. ddestruct H.
    rewrite H in H0'. ddestruct H0'.
    eapply IHassoc_traces
      with (t:=fun j =>
        if i =? j then
          Cont om0 (bindSubstProg impl k p0)
        else
          t j)
      in H3.
    2: exact H1.
    2:{
      intros.
      dec_eq_nats i0 i.
      {
        rewrite eqb_id, <- x0, <- x1.
        rewrite frobProgId with (p:= bindSubstProg _ _ _).
        destruct p0; constructor.
      }
      { now rewrite eqb_nid, <- H0. }
    }
    destruct_all.
    exists x2, ((i, UEvent None) :: x3).
    split. easy.
    split. easy.
    econstructor.
    2: exact H6.
    constructor; cbn.
    {
      rewrite eqb_id, <- x.
      now econstructor.
    }
    { intros. now rewrite eqb_nid. }
  }
Qed.