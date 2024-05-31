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
  SimulatesFacts.

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

Inductive set_list : list nat -> Type :=
| SLNil : set_list nil
| SLCons i is :
  ~In i is ->
  set_list is ->
  set_list (i :: is).

Axiom classicT : forall P : Prop, {P} + {~P}.

Fixpoint dedup (is : list nat) : list nat :=
  match is with
  | nil => nil
  | cons i is =>
      if classicT (List.In i is) then
        dedup is
      else
        cons i (dedup is)
  end.

Lemma dedup_correct :
  forall i is, List.In i is <-> List.In i (dedup is).
firstorder.
induction is.
contradiction.
simpl.
destruct (classicT (In a is)).
simpl in *.
destruct H.
subst.
apply IHis.
easy.
apply IHis.
easy.
simpl in *.
destruct H.
left.
easy.
right.
apply IHis.
easy.
induction is.
contradiction.
simpl in *.
destruct (classicT (In a is)).
right.
apply IHis.
easy.
simpl in *.
destruct H.
left.
easy.
right.
apply IHis.
easy.
Qed.

Lemma dedup_is_set : forall xs, set_list (dedup xs).
intros.
induction xs.
constructor.
simpl.
destruct (classicT (In a xs)).
easy.
constructor.
rewrite <- dedup_correct.
easy.
easy.
Qed.

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

Lemma get_nones_nil {E F} :
  forall i j p,
  i <> j ->
  projPoint i eqb (fst (@get_nones E F j p)) = nil.
intros.
induction p.
easy.
simpl.
destruct a.
destruct ev.
easy.
destruct (get_nones j p).
simpl.
rewrite eqb_nid.
easy.
easy.
easy.
Qed.

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

Lemma help41 (P Q : Prop) :
  ~(P \/ Q) <-> (~P /\ ~Q).
firstorder.
Qed.

Fixpoint tnones {E F} (qc : nat -> Trace (LEvent E F)) is :=
  match is with
  | nil => nil
  | cons i is => app (List.map (fun e => (i, e)) (qc i)) (tnones qc is)
  end.

Lemma tnones_notin {E F} :
  forall i (qc : nat -> Trace (LEvent E F)) is,
  ~In i is ->
  projPoint i eqb (tnones qc is) = nil.
intros.
induction is.
easy.
simpl in *.
rewrite help41 in H.
destruct_all.
rewrite <- app_nil_r.
rewrite projPoint_app.
f_equal.
clear IHis H0.
induction (qc a).
easy.
simpl.
rewrite eqb_nid.
easy.
easy.
apply IHis.
easy.
Qed.

Lemma help35 :
  forall i j : nat, forall xs,
  In i xs ->
  ~In j xs ->
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
apply IHxs.
easy.
easy.
Qed.

Lemma tnones_in {E F} :
  forall i (qc : nat -> Trace (LEvent E F)) is,
  In i is ->
  set_list is ->
  projPoint i eqb (tnones qc is) = qc i.
intros.
induction H0.
easy.
simpl in *.
destruct H.
subst.
rewrite <- app_nil_r.
rewrite projPoint_app.
f_equal.
clear.
induction (qc i).
easy.
simpl.
rewrite eqb_id.
f_equal.
easy.
apply tnones_notin.
easy.
assert (i <> i0).
eapply help35.
exact H.
easy.
change (qc i) with (nil ++ qc i).
rewrite projPoint_app.
f_equal.
clear IHset_list H0 n H.
induction (qc i0).
easy.
simpl.
rewrite eqb_nid.
easy.
easy.
apply IHset_list.
easy.
Qed.

Fixpoint interleave {E F}
  (is : list ThreadName)
  (p : Trace (ThreadLEvent E F))
  (qc : nat -> Trace (LEvent E F))
  : Trace (ThreadLEvent E F) :=
  match p with
  | nil => tnones qc is
  | cons (i, UEvent None) p => interleave is p qc
  | cons (i, e) p =>
    let (ns, q) := get_nones i (qc i) in
    let qc' j := if i =? j then q else qc j in
    app ns (cons (i, e) (interleave is p qc'))
  end.

Open Scope list.

Fixpoint interleave_seq i {E F}
  (p : Trace (LEvent E F))
  (qc : Trace (LEvent E F))
  : Trace (LEvent E F) :=
  match p with
  | nil => qc
  | cons (UEvent None) p => interleave_seq i p qc
  | cons e p =>
    map snd (fst (get_nones i qc)) ++ cons e (interleave_seq i p (snd (get_nones i qc)))
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

Lemma help37 {E F} :
  forall i n qc t0 p l,
  i <> n ->
  projPoint i eqb (@interleave E F (dedup l) p (fun j => if n =? j then t0 else qc j)) =
  projPoint i eqb (interleave (dedup l) p qc).
intros.
generalize dependent qc.
generalize dependent t0.
induction p; intros.
{
  simpl.
  induction (dedup l).
  easy.
  simpl.
  repeat rewrite projPoint_app.
  f_equal.
  2: easy.
  clear IHl0.
  assert (n = a \/ n <> a) by apply excluded_middle.
  destruct H0.
  {
    subst.
    rewrite eqb_id.
    induction t0.
    simpl.
    induction (qc a).
    easy.
    simpl.
    rewrite eqb_nid.
    easy.
    easy.
    simpl.
    rewrite eqb_nid.
    easy.
    easy.
  }
  rewrite eqb_nid.
  easy.
  easy.
}
{
  destruct a.
  destruct l0.
  destruct ev.
  2: apply IHp.
  {
    simpl.
    assert (n = n0 \/ n <> n0) by apply excluded_middle.
    destruct H0.
    {
      subst.
      rewrite eqb_id.
      assert (forall m t, @get_nones E F m t = (fst (get_nones m t), snd (get_nones m t))).
      intros. destruct (get_nones m t). easy.
      rewrite H0.
      rewrite (H0 n0 (qc n0)).
      simpl.
      simpl.
      repeat rewrite @projPoint_app.
      f_equal.
      rewrite get_nones_nil.
      rewrite get_nones_nil.
      easy.
      easy.
      easy.
      simpl.
      rewrite eqb_nid.
      2: easy.
      specialize (IHp (snd (get_nones n0 t0))).
      specialize (IHp (fun j => if n0 =? j then snd (get_nones n0 (qc n0)) else qc j)).
      simpl in *.
      assert (
        (fun j => if n0 =? j then snd (get_nones n0 t0) else if n0 =? j then t0 else qc j) =
        fun j => if n0 =? j then snd (get_nones n0 t0)  else qc j
      ).
      extensionality j. destruct (n0 =? j); easy.
      rewrite H1. clear H1.
      assert (
        (fun j => if n0 =? j then snd (get_nones n0 t0) else if n0 =? j then snd (get_nones n0 (qc n0)) else qc j) =
        fun j => if n0 =? j then snd (get_nones n0 t0)  else qc j
      ).
      extensionality j. destruct (n0 =? j); easy.
      rewrite H1 in IHp. clear H1.
      easy.
    }
    rewrite eqb_nid.
    2: easy.
    destruct (get_nones n0 (qc n0)).
    specialize (IHp t0).
    specialize (IHp (fun j => if n0 =? j then t1 else qc j)).
    simpl in IHp.
    assert (
      (fun j => if n =? j then t0 else if n0 =? j then t1 else qc j) =
      fun j => if n0 =? j then t1 else if n =? j then t0 else qc j
    ).
    extensionality j.
    assert (n = j \/ n <> j) by apply excluded_middle.
    destruct H1.
    subst.
    rewrite eqb_id.
    rewrite eqb_nid.
    easy.
    easy.
    rewrite eqb_nid.
    2: easy.
    easy.
    rewrite H1 in IHp.
    repeat rewrite @projPoint_app.
    f_equal.
    simpl.
    assert (i = n0 \/ i <> n0) by apply excluded_middle.
    destruct H2.
    subst.
    {
      rewrite eqb_id.
      f_equal.
      easy.
    }
    rewrite eqb_nid.
    2: easy.
    easy.
  }
  {
    simpl.
    assert (n = n0 \/ n <> n0) by apply excluded_middle.
    destruct H0.
    {
      subst.
      rewrite eqb_id.
      assert (forall m t, @get_nones E F m t = (fst (get_nones m t), snd (get_nones m t))).
      intros. destruct (get_nones m t). easy.
      rewrite H0.
      rewrite (H0 n0 (qc n0)).
      simpl.
      simpl.
      repeat rewrite @projPoint_app.
      f_equal.
      rewrite get_nones_nil.
      rewrite get_nones_nil.
      easy.
      easy.
      easy.
      simpl.
      rewrite eqb_nid.
      2: easy.
      specialize (IHp (snd (get_nones n0 t0))).
      specialize (IHp (fun j => if n0 =? j then snd (get_nones n0 (qc n0)) else qc j)).
      simpl in *.
      assert (
        (fun j => if n0 =? j then snd (get_nones n0 t0) else if n0 =? j then t0 else qc j) =
        fun j => if n0 =? j then snd (get_nones n0 t0)  else qc j
      ).
      extensionality j. destruct (n0 =? j); easy.
      rewrite H1. clear H1.
      assert (
        (fun j => if n0 =? j then snd (get_nones n0 t0) else if n0 =? j then snd (get_nones n0 (qc n0)) else qc j) =
        fun j => if n0 =? j then snd (get_nones n0 t0)  else qc j
      ).
      extensionality j. destruct (n0 =? j); easy.
      rewrite H1 in IHp. clear H1.
      easy.
    }
    rewrite eqb_nid.
    2: easy.
    destruct (get_nones n0 (qc n0)).
    specialize (IHp t0).
    specialize (IHp (fun j => if n0 =? j then t1 else qc j)).
    simpl in IHp.
    assert (
      (fun j => if n =? j then t0 else if n0 =? j then t1 else qc j) =
      fun j => if n0 =? j then t1 else if n =? j then t0 else qc j
    ).
    extensionality j.
    assert (n = j \/ n <> j) by apply excluded_middle.
    destruct H1.
    subst.
    rewrite eqb_id.
    rewrite eqb_nid.
    easy.
    easy.
    rewrite eqb_nid.
    2: easy.
    easy.
    rewrite H1 in IHp.
    repeat rewrite @projPoint_app.
    f_equal.
    simpl.
    assert (i = n0 \/ i <> n0) by apply excluded_middle.
    destruct H2.
    subst.
    {
      rewrite eqb_id.
      f_equal.
      easy.
    }
    rewrite eqb_nid.
    2: easy.
    easy.
  }
}
Qed.

Lemma projInterleave {E F} :
  forall p qc i,
  (~List.In i (dedup (map fst p)) -> qc i = nil) ->
  euttTrace (projPoint i eqb p) (qc i) ->
  projPoint i eqb (@interleave E F (dedup (map fst p)) p qc) =
  interleave_seq i (projPoint i eqb p) (qc i).
intros.
generalize dependent (map fst p).
generalize dependent qc.
induction p; intros.
{
  simpl.
  assert (In i l \/ ~In i l) by apply excluded_middle.
  destruct H1.
  apply tnones_in.
  rewrite <- dedup_correct.
  easy.
  apply dedup_is_set.
  rewrite H.
  apply tnones_notin.
  rewrite <- dedup_correct.
  easy.
  rewrite <- dedup_correct.
  easy.
}
destruct a, l0.
destruct ev.
2:{
  simpl in *.
  destruct (i =? n).
  simpl in *.
  apply IHp.
  apply help22 in H0.
  easy.
  easy.
  apply IHp.
  easy.
  easy.
}
{
  simpl in *.
  assert (i = n \/ i <> n) by apply excluded_middle.
  destruct H1.
  {
    subst.
    rewrite eqb_id in *.
    apply euttTraceEvt in H0. 2: easy.
    destruct_all.
    rewrite H1.
    rewrite get_nones_beh. 2: easy.
    simpl.
    rewrite @projPoint_app.
    f_equal.
    rewrite get_nones_beh.
    simpl.
    {
      clear.
      induction (nones x).
      easy.
      simpl.
      rewrite eqb_id.
      f_equal.
      easy.
    }
    easy.
    simpl.
    rewrite eqb_id.
    f_equal.
    rewrite get_nones_beh.
    simpl.
    2: easy.
    assert (x0 = (fun j => if n =? j then x0 else qc j) n).
    rewrite eqb_id.
    easy.
    rewrite H2 at 1.
    change (if n =? n then x0 else qc n)
    with ((fun j => if n =? j then x0 else qc j) n).
    apply IHp.
    rewrite eqb_id.
    easy.
    rewrite eqb_id.
    intros.
    apply H in H3.
    rewrite H1 in H3.
    destruct x; simpl in *; congruence.
  }
  {
    rewrite eqb_nid. rewrite eqb_nid in H0.
    2: easy. 2: easy.
    assert (projPoint i eqb (fst (get_nones n (qc n))) = nil).
    {
      clear H H0 IHp.
      induction (qc n).
      easy.
      destruct a.
      destruct ev.
      easy.
      simpl.
      destruct (get_nones n l0).
      simpl.
      rewrite eqb_nid.
      easy.
      easy.
      simpl.
      easy.
    }
    destruct (get_nones n (qc n)).
    rewrite @projPoint_app.
    simpl in *.
    rewrite H2.
    simpl.
    rewrite eqb_nid.
    2: easy.
    rewrite help37.
    apply IHp.
    easy.
    easy.
    easy.
  }
}
{
  simpl in *.
  assert (i = n \/ i <> n) by apply excluded_middle.
  destruct H1.
  {
    subst.
    rewrite eqb_id in *.
    apply euttTraceEvt in H0. 2: easy.
    destruct_all.
    rewrite H1.
    rewrite get_nones_beh. 2: easy.
    simpl.
    rewrite @projPoint_app.
    f_equal.
    rewrite get_nones_beh.
    simpl.
    {
      clear.
      induction (nones x).
      easy.
      simpl.
      rewrite eqb_id.
      f_equal.
      easy.
    }
    easy.
    simpl.
    rewrite eqb_id.
    f_equal.
    rewrite get_nones_beh.
    simpl.
    2: easy.
    assert (x0 = (fun j => if n =? j then x0 else qc j) n).
    rewrite eqb_id.
    easy.
    rewrite H2 at 1.
    change (if n =? n then x0 else qc n)
    with ((fun j => if n =? j then x0 else qc j) n).
    apply IHp.
    rewrite eqb_id.
    easy.
    rewrite eqb_id.
    intros.
    apply H in H3.
    rewrite H1 in H3.
    destruct x; simpl in *; congruence.
  }
  {
    rewrite eqb_nid. rewrite eqb_nid in H0.
    2: easy. 2: easy.
    assert (projPoint i eqb (fst (get_nones n (qc n))) = nil).
    {
      clear H H0 IHp.
      induction (qc n).
      easy.
      destruct a.
      destruct ev0.
      easy.
      simpl.
      destruct (get_nones n l0).
      simpl.
      rewrite eqb_nid.
      easy.
      easy.
      simpl.
      easy.
    }
    destruct (get_nones n (qc n)).
    rewrite @projPoint_app.
    simpl in *.
    rewrite H2.
    simpl.
    rewrite eqb_nid.
    2: easy.
    rewrite help37.
    apply IHp.
    easy.
    easy.
    easy.
  }
}
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


Lemma proj_notin {E F} :
  forall i (p : Trace (ThreadLEvent E F)),
  ~List.In i (map fst p) ->
  projPoint i eqb p = nil.
intros.
induction p.
easy.
destruct a.
simpl in *.
rewrite help41 in H.
destruct_all.
rewrite eqb_nid.
apply IHp.
easy.
easy.
Qed.

Lemma interleaveOverObj {E F} :
  forall p qc,
  (forall i, ~In i (dedup (map fst p)) ->
    qc i = nil) ->
  (forall i,
    euttTrace (projPoint i eqb p) (qc i)) ->
  IsOverObjTrace p ->
  IsOverObjTrace (@interleave E F (dedup (map fst p)) p qc).
Admitted.

Lemma help12 {E F} :
  forall (p : Trace (ThreadLEvent E F)),
  forall (HObj : IsOverObjTrace p),
  forall (qc : nat -> Trace (LEvent E F)),
  (forall i, ~In i (dedup (map fst p)) ->
    qc i = nil) ->
  (forall i,
    euttTrace (projPoint i eqb p) (qc i)) ->
  exists q,
    IsOverObjTrace q /\
    euttThreadTrace p q /\
    forall i, projPoint i eqb q = qc i.
intros p HObj qc qc_nil. intros.
exists (interleave (dedup (List.map fst p)) p qc).
split.
{
  apply interleaveOverObj; easy.
}
clear HObj.
split.
{
  generalize dependent (dedup (List.map fst p)).
  intros.
  rename l into pis.
  generalize dependent qc.
  induction p; intros.
  simpl.
  {
    clear qc_nil.
    induction pis.
    constructor.
    simpl in *.
    change (@nil (ThreadLEvent E F))
    with (@nil (ThreadLEvent E F) ++ nil).
    apply euttTraceThread_app.
    2: easy.
    specialize (H a).
    induction (qc a).
    constructor.
    destruct a0.
    destruct ev.
    dependent destruction H.
    apply help23 in H.
    simpl.
    constructor.
    apply IHt.
    easy.
    dependent destruction H.
  }
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
    easy.
  }
  {
    intros.
    simpl in *.
    assert (H' := H).
    specialize (H n).
    rewrite eqb_id in H.
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
    repeat rewrite eqb_id in *.
    rewrite H0 in H'.
    apply help23_t in H'.
    dependent destruction H'.
    easy.
    rewrite eqb_nid. rewrite eqb_nid in H'.
    easy.
    easy.
    easy.
    {
      intros.
      apply qc_nil in H1.
      rewrite H1.
      cut (n =? i = false).
      {
        intros.
        rewrite H2.
        easy.
      }
      assert (forall i j, qc i <> qc j -> i <> j) by congruence.
      apply eqb_nid.
      apply H2.
      rewrite H0.
      rewrite H1.
      destruct x; simpl; congruence.
    }
    easy.
    easy.
  }
  {
    intros.
    simpl in *.
    assert (H' := H).
    specialize (H n).
    rewrite eqb_id in H.
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
    repeat rewrite eqb_id in *.
    rewrite H0 in H'.
    apply help23_t in H'.
    dependent destruction H'.
    easy.
    rewrite eqb_nid. rewrite eqb_nid in H'.
    easy.
    easy.
    easy.
    {
      intros.
      apply qc_nil in H1.
      rewrite H1.
      cut (n =? i = false).
      {
        intros.
        rewrite H2.
        easy.
      }
      assert (forall i j, qc i <> qc j -> i <> j) by congruence.
      apply eqb_nid.
      apply H2.
      rewrite H0.
      rewrite H1.
      destruct x; simpl; congruence.
    }
    easy.
    easy.
  }
}
{
  intros.
  specialize (H i).
  rewrite projInterleave.
  2: apply qc_nil.
  clear qc_nil.
  generalize dependent qc.
  induction p; intros.
  easy.
  destruct a, l.
  destruct ev.
  2:{
    simpl in *.
    destruct (i =? n).
    simpl in *.
    apply IHp.
    apply help22 in H.
    easy.
    apply IHp.
    easy.
  }
  {
    simpl in *.
    destruct (i =? n).
    simpl in *.
    apply euttTraceEvt in H.
    destruct_all.
    rewrite H0.
    rewrite get_nones_beh.
    simpl.
    repeat f_equal.
    {
      clear.
      induction (nones x).
      easy.
      simpl.
      f_equal.
      easy.
    }
    change x0 with ((fun _ : nat => x0) i).
    apply IHp.
    easy.
    easy.
    easy.
    apply IHp.
    easy.
  }
  {
    simpl in *.
    destruct (i =? n).
    simpl in *.
    apply euttTraceEvt in H.
    destruct_all.
    rewrite H0.
    rewrite get_nones_beh.
    simpl.
    repeat f_equal.
    {
      clear.
      induction (nones x).
      easy.
      simpl.
      f_equal.
      easy.
    }
    change x0 with ((fun _ : nat => x0) i).
    apply IHp.
    easy.
    easy.
    easy.
    apply IHp.
    easy.
  }
  easy.
}
Qed.

Lemma help13 {E F} :
  forall (p : Trace (ThreadLEvent E F)),
  forall (HObj : IsOverObjTrace p),
  forall (qc : nat -> Trace (LEvent E F)),
  (forall i, ~In i (dedup (map fst p)) ->
    qc i = nil) ->
  (forall i, In i (dedup (map fst p)) ->
    euttTrace (projPoint i eqb p) (qc i)) ->
  exists q,
    IsOverObjTrace q /\
    euttThreadTrace p q /\
    forall i, projPoint i eqb q = qc i.
intros.
cut (forall i, euttTrace (projPoint i eqb p) (qc i)).
{
  intros.
  apply help12.
  easy.
  easy.
  easy.
}
intros.
specialize (H i).
specialize (H0 i).
assert (In i (dedup (map fst p)) \/ ~In i (dedup (map fst p))).
apply excluded_middle.
destruct H1.
apply H0.
easy.
assert (H1' := H1).
apply H in H1'.
rewrite H1'.
rewrite proj_notin.
constructor.
rewrite dedup_correct.
easy.
Qed.

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

Inductive eutt_finite {E F A} (om : F A) : Prog E A -> Prog E A -> ThreadState E F -> Prop :=
| EFRet x : eutt_finite om (Return x) (Return x) (Cont om (Return x))
| EFBind A (m : E A) k k' :
    (forall x, eutt (k x) (k' x)) ->
    eutt_finite om (Bind m k) (Bind m k') (Cont om (Bind m k))
| EFLNoOp p p' s :
    eutt_finite om p p' s ->
    eutt_finite om (NoOp p) p' s
| EFRNoOp p p' s :
    eutt_finite om p p' s ->
    eutt_finite om p (NoOp p') s.

Lemma contra_eutt_finite {E F A} :
  forall om p p' (s : ThreadState E F),
  (s = Idle \/ exists A B m' k, s = UCall (A:=A) (B:=B) m' k) ->
  @eutt_finite E F A om p p' s ->
  False.
intros.
induction H0.
destruct H.
congruence.
destruct_all.
congruence.
destruct H.
congruence.
destruct_all.
congruence.
apply IHeutt_finite.
easy.
apply IHeutt_finite.
easy.
Qed.

Lemma derive_eutt_finite {E F A} {impl : Impl E F} :
  forall (m : F A) (p p' : Prog E A) n s s' e,
  e <> UEvent None ->
  euttF (upaco2 euttF bot2) p p' ->
  Steps (ThreadStep impl) (Cont m p) (nones n) s ->
  ThreadStep impl s e s' ->
  eutt_finite m p p' s.
intros.
generalize dependent p.
induction n; intros.
{
  simpl in *.
  dependent destruction H1.
  destruct e.
  destruct ev.
  2:{
    congruence.
  }
  {
    unfold ThreadStep in H2.
    dependent destruction H2.
    clear H.
    dependent induction H0.
    constructor.
    intros.
    specialize (H x).
    destruct H.
    2: destruct H.
    easy.
    constructor.
    apply IHeuttF; easy.
  }
  {
    unfold ThreadStep in H2.
    dependent destruction H2.
    clear H.
    dependent induction H0.
    constructor.
    constructor.
    apply IHeuttF; easy.
  }
}
{
  simpl in *.
  dependent destruction H1.
  unfold ThreadStep in H1.
  dependent destruction H1.
  constructor.
  apply IHn.
  2: easy.
  apply inv_eutt_Noop_left in H0.
  easy.
}
Qed.

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

Lemma ends_oev_overObj {E F} :
  forall p,
    (@ends_in_oev E F p \/ p = nil) = IsOverObjTrace p.
intros.
apply propositional_extensionality.
split; intro.
{
  destruct H.
  2: { subst. constructor. }
  unfold ends_in_oev in H.
  destruct_all.
  subst.
  induction x.
  {
    repeat constructor.
  }
  {
    dependent destruction IHx.
    destruct x2; simpl in x; discriminate.
    simpl.
    rewrite <- x. clear x.
    change (a :: p ++ (i, OEvent e) :: q)
    with ((a :: p) ++ (i, OEvent e) :: q).
    destruct a, l.
    constructor.
    constructor.
    easy.
    easy.
    simpl.
    apply ConsOverObj with (p:=nil).
    constructor.
    constructor.
    easy.
    easy.
  }
}
{
  induction H.
  {
    right.
    easy.
  }
  {
    destruct IHIsOverObjTrace.
    left.
    clear H0 H.
    {
      induction p.
      simpl.
      apply ends_oev_cons.
      easy.
      simpl.
      apply ends_oev_cons.
      easy.
    }
    subst.
    left.
    {
      clear H.
      induction p.
      unfold ends_in_oev.
      repeat econstructor.
      simpl.
      apply ends_oev_cons.
      easy.
    }
  }
}
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
  2: easy.
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
  specialize (H6 i).
  specialize (H2 i).
  rewrite <- H6 in H2.
  easy.
  (* clear H2. *)
  rewrite <- (decompPointSteps eqb (ThreadStep impl')) in H7.
  2: exact threadDecEq.
  eexists (x1, s), x2.
  repeat split.
  apply euttOver.
  easy.
  easy.
  simpl in *.
  clear H7 H2 H3' x1 H6 H4 H3 H0.
  generalize dependent (Init spec).
  clear HObj.
  {
    induction H5; intros.
    easy.
    dependent destruction H1.
    unfold StateStep in H0; simpl in H0; subst.
    apply IHeuttThreadTrace.
    easy.
    econstructor.
    unfold StateStep. easy.
    apply IHeuttThreadTrace.
    easy.
    dependent destruction H1.
    unfold StateStep in H0; simpl in H0; subst.
    econstructor.
    exact H0.
    apply IHeuttThreadTrace.
    easy.
    dependent destruction H1.
    unfold StateStep in H0; simpl in H0; subst.
    econstructor.
    easy.
    apply IHeuttThreadTrace.
    easy.
  }
  easy.
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

Definition assoc_state E F G : Type := ThreadState E F * ThreadState F G * ThreadState E G.


(* at each step, says what the three states are *before* the event *)
(* Inductive assoc_step {E F G} {impl : Impl E F} {impl' : Impl F G} : assoc_state E F G -> assoc_state E F G -> Prop :=
| ASGCall sL R (gm : G R) :
  assoc_step
    (sL, Idle, Idle)
    (sL, Cont gm (impl' _ gm), Cont gm (substProg impl (impl' _ gm)))
| ASGRet sL R (gm : G R) v :
  assoc_step
    (sL, Cont gm (Return v), Cont gm (Return v))
    (sL, Idle, Idle)
| ASFCall R (gm : G R) (fm : F R) fk fp :
  assoc_step
    (Idle, Cont gm (Bind fm fk), Cont gm (NoOp fp))
    (Cont fm (impl _ fm), UCall gm fk, Cont gm fp)
| ASFRet R (gm : G R) (fm : F R) k v sF :
  assoc_step
    (Cont fm (Return v), UCall gm k, sF)
    (Idle, Cont gm (k v), sF)
| ASFNop sL R (gm : G R) p sF :
  assoc_step
    (sL, Cont gm (NoOp p), sF)
    (sL, Cont gm p, sF)
| ASECall R (fm : F R) (em : E R) k sH sF :
  assoc_step
    (Cont fm (Bind em k), sH, sF)
    (UCall fm k, sH, sF)
| ASERet R (fm : F R) v sH sF :
  assoc_step
    (Cont fm (Return v), sH, sF)
    (Idle, sH, sF)
| ASENop R fm (p : Prog E R) sH sF :
  assoc_step
    (Cont fm (NoOp p), sH, sF)
    (Cont fm p, sH, sF)
.
Arguments assoc_step {E F G} impl impl'. *)

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

Inductive Interleave {E F} : (nat -> Trace (LEvent E F)) -> Trace (ThreadLEvent E F) -> Prop :=
| InterleaveEnd qc :
    (forall i, qc i = nil) ->
    Interleave qc nil
| InterleaveCons i e q qc p :
    qc i = e :: q ->
    Interleave (fun j => if i =? j then q else qc j) p ->
    Interleave qc ((i, e) :: p).

Lemma uninterleave {E F} :
  forall qc p,
  @Interleave E F qc p ->
  forall i,
    qc i = projPoint i eqb p.
intros.
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

Lemma full_projOver {E F G} :
  forall (p : Trace (ThreadLEvent F G)) q,
  forall (qc : nat -> Trace (LEvent E G)),
  (forall i, projOverSeq (projPoint i eqb p) = projOverSeq (qc i)) ->
  Interleave qc q ->
  projOver p = projOver q.
Admitted.

Lemma full_projUnderThr {E F G} :
  forall (p : Trace (ThreadLEvent E F)) q,
  forall (qc : nat -> Trace (LEvent E G)),
  (forall i, projUnderThrSeq (projPoint i eqb p) = projUnderThrSeq (qc i)) ->
  Interleave qc q ->
  projUnderThr p = projUnderThr q.
intros.
Admitted.

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

Lemma tollens P Q : (P -> Q) -> ~Q -> ~P.
unfold not.
intros.
apply H0.
apply H.
easy.
Qed.

Axiom dne : forall P, ~~P -> P.

Ltac dec_eq_nats i j :=
  let H := fresh in
  assert (H : i = j \/ i <> j) by apply excluded_middle;
  destruct H; subst.

Lemma if_prune {A B} {x y : B} {z : A -> B} :
  forall (b : A -> bool),
  (fun i : A => if b i then x else if b i then y else z i) =
  (fun i : A => if b i then x else z i).
intros.
extensionality j.
destruct (b j); easy.
Qed.

Lemma interleave_cons {E F} :
  forall qc qc' i e p,
  (forall j, i <> j -> qc j = qc' j) ->
  qc' i = qc i ++ cons e nil ->
  @Interleave E F qc p ->
  Interleave qc' (p ++ (i, e) :: nil).
intros.
generalize dependent qc.
generalize dependent qc'.
induction p; intros.
{
  simpl.
  dependent destruction H1.
  rewrite H1 in H0.
  simpl in *.
  econstructor.
  exact H0.
  constructor.
  intros.
  dec_eq_nats i i0.
  rewrite eqb_id.
  easy.
  rewrite eqb_nid.
  rewrite <- H.
  apply H1.
  easy.
  easy.
}
{
  simpl.
  dependent destruction H1.
  eapply IHp with (qc':=fun j => if i =? j then _ else if i0 =? j then q else qc j) in H2.
  2:{
    intros.
    rewrite eqb_nid with (n:=i) (m:=j).
    easy.
    easy.
  }
  2:{
    rewrite eqb_id.
    easy.
  }
  dec_eq_nats i0 i.
  {
    econstructor.
    rewrite H1 in H0.
    simpl in H0.
    exact H0.
    assert (
      (fun j : nat => if i =? j then q ++ e :: nil else qc' j) =
      (fun j : nat => if i =? j then (if i =? j then q else qc j) ++ e :: nil else if i =? j then q else qc j)
    ).
    {
      extensionality j.
      dec_eq_nats i j.
      rewrite eqb_id.
      easy.
      rewrite eqb_nid.
      symmetry.
      apply H.
      easy.
      easy.
    }
    rewrite H3 at 1. clear H3.
    easy.
  }
  {
    econstructor.
    rewrite <- H.
    exact H1.
    easy.
    assert (
      (fun j : nat => if i0 =? j then q else qc' j) =
      (fun j => if i =? j then (if i0 =? j then q else qc j) ++ e :: nil else if i0 =? j then q else qc j)
    ).
    {
      extensionality j.
      dec_eq_nats i0 j.
      rewrite eqb_id.
      rewrite eqb_nid.
      easy.
      easy.
      rewrite eqb_nid.
      dec_eq_nats i j.
      rewrite eqb_id.
      easy.
      rewrite eqb_nid.
      symmetry.
      apply H.
      easy.
      easy.
      easy.
    }
    rewrite H4 at 1. clear H4.
    easy.
  }
}
Qed.

Lemma help57 {E F} is :
  forall qc,
  (forall i, ~In i is -> qc i = nil) ->
  (exists i, ends_in_oev_seq (qc i)) ->
  exists r, Interleave qc r /\ IsOverObjTrace (E:=E) (F:=F) r.
unfold ends_in_oev_seq.
intros.
destruct_all.
cut (
  exists r,
    Interleave (fun j => if x =? j then x0 else qc j) r
).
{
  intros.
  destruct_all.
  assert (qc = fun j => if x =? j then x0 ++ OEvent x1 :: nil else qc j).
  {
    extensionality j.
    dec_eq_nats x j.
    subst.
    rewrite eqb_id.
    easy.
    rewrite eqb_nid.
    easy.
    easy.
  }
  rewrite H2. clear H2.
  exists (x2 ++ (x, OEvent x1) :: nil).
  clear H.
  split.
  2:{
    clear.
    rewrite <- ends_oev_overObj.
    left.
    induction x2.
    repeat econstructor.
    simpl.
    apply ends_oev_cons.
    easy.
  }
  eapply interleave_cons.
  3: exact H1.
  intros.
  simpl.
  rewrite eqb_nid.
  easy.
  easy.
  repeat rewrite eqb_id.
  easy.
}
cut (
  forall qc,
  (forall i, ~In i is -> qc i = nil) ->
  exists r,
    @Interleave E F qc r
).
{
  intros.
  apply H1.
  intros.
  dec_eq_nats x i.
  rewrite H in H0.
  destruct x0; simpl in H0; congruence.
  easy.
  rewrite eqb_nid.
  apply H.
  easy.
  easy.
}
clear H0 x1 x0 x H qc.
induction is.
{
  intros.
  exists nil.
  constructor.
  intros.
  apply H.
  easy.
}
{
  intros.
  assert (exists r, Interleave (fun j => if a =? j then nil else qc j) r).
  {
    apply IHis.
    intros.
    dec_eq_nats a i.
    rewrite eqb_id.
    easy.
    rewrite eqb_nid.
    apply H.
    simpl.
    rewrite help41.
    easy.
    easy.
  }
  destruct_all.
  exists (map (fun e => (a, e)) (qc a) ++ x).
  clear IHis H is.
  remember (qc a).
  generalize dependent qc.
  induction l; intros.
  {
    assert (qc = (fun j => if a =? j then nil else qc j)).
    {
      extensionality j.
      dec_eq_nats a j.
      rewrite eqb_id.
      easy.
      rewrite eqb_nid.
      easy.
      easy.
    }
    simpl.
    rewrite H.
    easy.
  }
  {
    simpl.
    econstructor.
    symmetry.
    exact Heql.
    apply IHl.
    2: { rewrite eqb_id. easy. }
    rewrite if_prune.
    easy.
  }
}
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
  assert (exists q, Interleave x2 q /\ IsOverObjTrace q).
  {
    rewrite <- ends_oev_overObj in H2.
    rewrite <- ends_oev_overObj in H4.
    destruct H4, H2.
    {
      eapply help57.
      intros.
      specialize (H5 i).
      destruct H5.
      apply H5.
      exact H6.
    }
    {
      subst.
      simpl in *.
      (* contradiction because cant make steps without overlay events*)
    }
    {
      subst.
      simpl in *.
      eapply help57.
      intros.
      specialize (H5 i).
      destruct H5.
      apply H5.
      exact H4.
      admit.
    }
    {
      subst.
      simpl in *.
      exists nil.
      split.
      constructor.
      intros.
      specialize (H5 i).
      destruct H5.
      apply H2.
      easy.
      constructor.
    }
  }
  destruct_all.
  exists x3.
  repeat split.
  {
    eapply full_projOver.
    2: exact H6.
    intros.
    specialize (H5 i).
    easy.
  }
  {
    assert (projUnderThr x1 = projUnderThr x3).
    eapply full_projUnderThr.
    2: exact H6.
    intros.
    specialize (H5 i).
    easy.
    rewrite <- H8.
    easy.
  }
  {
    unfold ThreadsStep.
    rewrite (decompPointSteps eqb (ThreadStep (impl |> impl'))).
    intros.
    specialize (H5 i).
    erewrite <- uninterleave.
    2: exact H6.
    2: exact threadDecEq.
    easy.
  }
  easy.
}
clear H4 H2 H0.
intros.
assert (In i (dedup (map fst x1 ++ map fst x0)) \/ ~In i (dedup (map fst x1 ++ map fst x0))) by apply excluded_middle.
destruct H0.
2:{
  assert (projPoint i eqb x1 = nil).
  {
    rewrite <- dedup_correct in H0.
    rewrite In_split in H0.
    rewrite help41 in H0.
    destruct_all.
    rewrite proj_notin.
    easy.
    easy.
  }
  assert (projPoint i eqb x0 = nil).
  {
    rewrite <- dedup_correct in H0.
    rewrite In_split in H0.
    rewrite help41 in H0.
    destruct_all.
    rewrite proj_notin.
    easy.
    easy.
  }
  exists Idle, nil.
  rewrite H2.
  rewrite H4.
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
generalize dependent (projPoint i eqb x1).
generalize dependent (projPoint i eqb x0).
intros.
rename l into tH.
rename l0 into tL.
apply get_assoc_view in H.
move tL after tH.
move H3 after H1.
cut (
exists (st : ThreadState E G) (q : list (LEvent E G)),
  projOverSeq tH = projOverSeq q /\
  projUnderThrSeq tL = projUnderThrSeq q /\
  Steps (ThreadStep (impl |> impl')) (substTS impl (allIdle i)) q st
).
{
  intros.
  destruct_all.
  exists x, x2.
  easy.
}
eapply help66.
easy.
constructor.
exact H3.
exact H1.
Qed.