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

Lemma help12 {E F} :
  forall (p : Trace (ThreadLEvent E F)),
  forall (qc : nat -> Trace (LEvent E F)),
  (forall i, ~In i (dedup (map fst p)) ->
    qc i = nil) ->
  (forall i,
    euttTrace (projPoint i eqb p) (qc i)) ->
  exists q,
    euttThreadTrace p q /\
    forall i, projPoint i eqb q = qc i.
intros p qc qc_nil. intros.
exists (interleave (dedup (List.map fst p)) p qc).
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
  forall (qc : nat -> Trace (LEvent E F)),
  (forall i, ~In i (dedup (map fst p)) ->
    qc i = nil) ->
  (forall i, In i (dedup (map fst p)) ->
    euttTrace (projPoint i eqb p) (qc i)) ->
  exists q,
    euttThreadTrace p q /\
    forall i, projPoint i eqb q = qc i.
intros.
cut (forall i, euttTrace (projPoint i eqb p) (qc i)).
{
  intros.
  apply help12.
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
  (s = Idle \/ exists A m' k, s = UCall (A:=A) om m' k) ->
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