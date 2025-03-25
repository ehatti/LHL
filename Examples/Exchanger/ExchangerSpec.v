From LHL.Core Require Import
  Program
  Specs.

From LHL.Util Require Import
  Tactics
  TransUtil
  Util.

Variant ExchSig {A} : ESig :=
| Exch (v : A) : ExchSig (option A).
Arguments ExchSig : clear implicits.

Variant ExchState {T A} :=
| ExchDef (p d : set (Name T * A)).
Arguments ExchState : clear implicits.

Notation "{}" := emp.
Notation "{ i => x }" := (insert (i, x) emp).
Notation "{ i => x , j => y }" := (insert (i, x) (insert (j, y) emp)).

Variant ExchStep {T A} : ExchState T A -> ThreadEvent T (ExchSig A) -> ExchState T A -> Prop :=
| ExchCall1 i x : ExchStep
    (ExchDef {} {})
    (i, CallEv (Exch x))
    (ExchDef {i => x} {})
| ExchCall2 i x j y : i <> j -> ExchStep
    (ExchDef {i => x} {})
    (j, CallEv (Exch y))
    (ExchDef {j => y, i => x} {})
| ExchRet1 i x j y : i <> j -> ExchStep
    (ExchDef {i => x, j => y} {})
    (i, RetEv (Exch x) (Some y))
    (ExchDef {i => x} {j => y})
| ExchRet2 i x j y : i <> j -> ExchStep
    (ExchDef {i => x} {j => y})
    (j, RetEv (Exch y) (Some x))
    (ExchDef {} {})
| ExchFail i x : ExchStep
    (ExchDef {i => x} {})
    (i, RetEv (Exch x) None)
    (ExchDef {} {}).

Require Import Coq.Lists.List.
Import ListNotations.

Lemma quad_ind {A} :
  forall P : list A -> Prop,
  P [] ->
  (forall x, P [x]) ->
  (forall x y, P [x; y]) ->
  (forall x y z, P [x; y; z]) ->
  (forall x y z w xs, P xs -> P (x :: y :: z :: w :: xs)) ->
  forall xs, P xs.
intros.
generalize dependent xs.
fix rec 1. intros.
destruct xs.
{ apply H. }
destruct xs.
{ apply H0. }
destruct xs.
{ apply H1. }
destruct xs.
{ apply H2. }
{
  apply H3.
  apply rec.
}
Qed.

Inductive exch_trace {T A} : list (ThreadEvent T (ExchSig A)) -> Prop :=
| ETNil :
  exch_trace
    []
| ETC i v :
  exch_trace
    [(i, CallEv (Exch v))]
| ETCR i v p :
  exch_trace p ->
  exch_trace
    ([(i, CallEv (Exch v)); (i, RetEv (Exch v) None)] ++ p)
| ETCC i v j w :
  i <> j ->
  exch_trace
    [(i, CallEv (Exch v)); (j, CallEv (Exch w))]
| ETCCRi i v j w :
  i <> j ->
  exch_trace
    [(i, CallEv (Exch v)); (j, CallEv (Exch w)); (i, RetEv (Exch v) (Some w))]
| ETCCRj i v j w :
  i <> j ->
  exch_trace
    [(i, CallEv (Exch v)); (j, CallEv (Exch w)); (j, RetEv (Exch w) (Some v))]
| ETCCRRi i v j w p :
  i <> j ->
  exch_trace p ->
  exch_trace
    ([(i, CallEv (Exch v)); (j, CallEv (Exch w)); (i, RetEv (Exch v) (Some w)); (j, RetEv (Exch w) (Some v))] ++ p)
| ETCCRRj i v j w p :
  i <> j ->
  exch_trace p ->
  exch_trace
    ([(i, CallEv (Exch v)); (j, CallEv (Exch w)); (j, RetEv (Exch w) (Some v)); (i, RetEv (Exch v) (Some w))] ++ p).

From Coq Require Import Logic.FunctionalExtensionality.

Lemma disj_cons3 {A} :
  forall x y : A,
  insert x (insert y emp) <> emp.
unfold not, emp. intros.
apply equal_f with (x:=x) in H.
rewrite <- H. now left.
Qed.

Lemma tri_neq {I A} :
  forall (i j k : I) (x y z : A),
  j <> k ->
  {i => x} <> {j => y, k => z}.
unfold not at 2. intros.
unfold insert, emp in H0. assert (H0' := H0).
apply equal_f with (x:=(i, x)) in H0.
assert ((i, x) = (i, x) \/ False).
{ now left. }
rewrite H0 in H1.
destruct H1.
{
  ddestruct H1.
  apply equal_f with (x:=(k, z)) in H0'.
  assert ((i, x) = (k, z) \/ False).
  { rewrite H0'. right. now left. }
  destruct H1; now ddestruct H1.
}
destruct H1. 2: easy.
ddestruct H1.
{
  apply equal_f with (x:=(j, y)) in H0'.
  assert ((i, x) = (j, y) \/ False).
  { rewrite H0'. now left. }
  destruct H1; now ddestruct H1.
}
Qed.

Lemma insert_cong3 {I A} :
  forall (i j k l : I) (x y z w : A),
  i <> j ->
  k <> l ->
  {i => x, j => y} = {k => z, l => w} ->
  (i, x) = (k, z) /\ (j, y) = (l, w) \/
  (i, x) = (l, w) /\ (k, z) = (j, y).
unfold insert, emp.
intros. assert (H1' := H1).
apply equal_f with (x:=(i, x)) in H1.
assert ((k, z) = (i, x) \/ (l, w) = (i, x) \/ False).
{ rewrite <- H1. now left. }
destruct H2.
{
  left.
  ddestruct H2.
  split. easy.
  apply equal_f with (x:=(j, y)) in H1'.
  assert ((i, x) = (j, y) \/ (l, w) = (j, y) \/ False).
  {
    rewrite <- H1'.
    right. now left.
  }
  destruct H2.
  { now ddestruct H2. }
  destruct H2.
  { now ddestruct H2. }
  { easy. }
}
destruct H2.
{
  right.
  ddestruct H2.
  split. easy.
  apply equal_f with (x:=(j, y)) in H1'.
  assert ((k, z) = (j, y) \/ (i, x) = (j, y) \/ False).
  { rewrite <- H1'. right. now left. }
  destruct H2.
  { now ddestruct H2. }
  destruct H2.
  { now ddestruct H2. }
  easy.
}
easy.
Qed.

Ltac simp_sets :=
  repeat match goal with
  | [ H : {?i => ?v} = {} |- _ ] =>
      now apply disj_cons in H
  | [ H : {} = {?i => ?v} |- _ ] =>
      symmetry in H;
      now apply disj_cons in H
  | [ H : insert ?x emp = insert ?y emp |- _ ] =>
      apply insert_cong1 in H;
      ddestruct H
  | [ H : insert (?i, ?x) (insert (?j, ?y) emp) =
          insert (?i, ?x) (insert (?k, ?z) emp),
      H0 : ?i <> ?j
    |-
      _
    ] =>
      apply (insert_cong2_pad _ _ _ _ _ _ H0) in H;
      ddestruct H
  (* | [ H : insert ?x ?xs = insert ?y ?ys |- _ ] =>
      let H2 := fresh in
      let H3 := fresh in
      apply insert_cong in H;
      destruct H as [H2 H3];
      ddestruct H2 *)
  | [ H : emp = emp |- _ ] =>
      clear H
  | [ H : contains ?x (insert ?y ?s) |- _ ] =>
      let HL := fresh in
      let HR := fresh in
      apply contains_invert in H;
      destruct H as [HL | HR];
      [ddestruct HL | idtac]
  | [ H : contains ?x emp |- _ ] =>
      now apply contains_contr in H
  | [ H : insert ?x (insert ?y emp) = emp |- _ ] =>
      now apply disj_cons3 in H
  | [ H : emp = insert ?x (insert ?y emp) |- _ ] =>
      symmetry in H;
      now apply disj_cons3 in H
  | [ H : {?i => ?x} = {?j => ?y, ?k => ?z} |- _ ] =>
      now apply tri_neq in H
  | [ H : {?j => ?y, ?k => ?z} = {?i => ?x} |- _ ] =>
      symmetry in H;
      now apply tri_neq in H
  | [ H : {?i => ?x, ?j => ?y} = {?k => ?z, ?l => ?w} |- _ ] =>
      apply insert_cong3 in H; auto
  end.

Axiom undef:forall{a},a.

From Coq Require Import
  Program.Wf.

Require Import Lia.

Program Fixpoint get_exch_trace {T A} s p {measure (length p)} :
  Steps ExchStep (ExchDef {} {}) p s ->
  @exch_trace T A p := _.
Next Obligation.
destruct p.
{ constructor. }
destruct p.
{
  do 2 ddestruct H.
  { constructor. }
  all: simp_sets.
}
ddestruct H. ddestruct H; simp_sets.
ddestruct H0. ddestruct H; simp_sets.
{
  ddestruct H0.
  { now constructor. }
  {
    ddestruct H0; simp_sets.
    {
      destruct x; destruct H2;
      ddestruct H2; ddestruct H3.
      {
        ddestruct H1.
        { now constructor. }
        {
          ddestruct H1; simp_sets.
          constructor. easy.
          apply get_exch_trace with (s:=s).
          simpl. lia. easy.
        }
      }
      {
        ddestruct H1.
        { now constructor. }
        {
          ddestruct H1; simp_sets.
          constructor. easy.
          apply get_exch_trace with (s:=s).
          simpl. lia. easy.
        }
      }
    }
  }
}
{
  constructor.
  apply get_exch_trace with (s:=s).
  simpl. lia. easy.
}
Qed.

Arguments existT {A} {P} {x}.

Lemma exchSeqCons {T A} :
  forall (p : list (ThreadEvent T (ExchSig A))) (s : ExchState T A),
    Steps ExchStep (ExchDef {} {}) p s ->
    SeqConsistent (fun _ : Name T => None) p.
intros.
apply get_exch_trace in H.
induction H.
{ constructor. }
{
  eapply SCCall with
    (a':=fun k =>
      if i =? k then
        Some (existT (Exch v))
      else
        (fun _ : Name T => None) k).
  { easy. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  constructor.
}
{
  eapply SCCall with
    (a':=fun k =>
      if i =? k then
        Some (existT (Exch v))
      else
        (fun _ : Name T => None) k).
  { easy. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  eapply SCRet with
    (a':=fun k => None).
  { now rewrite eqb_id. }
  { easy. }
  {
    unfold differ_pointwise.
    intros. now rewrite eqb_nid.
  }
  easy.
}
{
  eapply SCCall with
    (a':=fun k =>
      if i =? k then
        Some (existT (Exch v))
      else
        (fun _ : Name T => None) k).
  { easy. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  eapply SCCall with
    (a':=fun k =>
      if j =? k then
        Some (existT (Exch w))
      else if i =? k then
        Some (existT (Exch v))
      else
        (fun _ : Name T => None) k).
  { now rewrite eqb_nid. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  constructor.
}
{
  eapply SCCall with
    (a':=fun k =>
      if i =? k then
        Some (existT (Exch v))
      else
        (fun _ : Name T => None) k).
  { easy. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  eapply SCCall with
    (a':=fun k =>
      if j =? k then
        Some (existT (Exch w))
      else if i =? k then
        Some (existT (Exch v))
      else
        (fun _ : Name T => None) k).
  { now rewrite eqb_nid. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  eapply SCRet with
    (a':=fun k =>
      if i =? k then
        None
      else if j =? k then
        Some (existT (Exch w))
      else if i =? k then
        Some (existT (Exch v))
      else
        (fun _ : Name T => None) k).
  { now rewrite eqb_id, eqb_nid. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  constructor.
}
{
  eapply SCCall with
    (a':=fun k =>
      if i =? k then
        Some (existT (Exch v))
      else
        (fun _ : Name T => None) k).
  { easy. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  eapply SCCall with
    (a':=fun k =>
      if j =? k then
        Some (existT (Exch w))
      else if i =? k then
        Some (existT (Exch v))
      else
        (fun _ : Name T => None) k).
  { now rewrite eqb_nid. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  eapply SCRet with
    (a':=fun k =>
      if j =? k then
        None
      else if j =? k then
        Some (existT (Exch w))
      else if i =? k then
        Some (existT (Exch v))
      else
        (fun _ : Name T => None) k).
  { now rewrite eqb_id. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  constructor.
}
{
  eapply SCCall with
    (a':=fun k =>
      if i =? k then
        Some (existT (Exch v))
      else
        (fun _ : Name T => None) k).
  { easy. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  eapply SCCall with
    (a':=fun k =>
      if j =? k then
        Some (existT (Exch w))
      else if i =? k then
        Some (existT (Exch v))
      else
        (fun _ : Name T => None) k).
  { now rewrite eqb_nid. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  eapply SCRet with
    (a':=fun k =>
      if i =? k then
        None
      else if j =? k then
        Some (existT (Exch w))
      else if i =? k then
        Some (existT (Exch v))
      else
        (fun _ : Name T => None) k).
  { now rewrite eqb_id, eqb_nid. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  eapply SCRet with
    (a':=fun k => None).
  { now rewrite eqb_id, eqb_nid. }
  { easy. }
  {
    unfold differ_pointwise.
    intros. dec_eq_nats i j0.
    { now rewrite eqb_id. }
    { now rewrite eqb_nid, eqb_nid. }
  }
  easy.
}
{
  eapply SCCall with
    (a':=fun k =>
      if i =? k then
        Some (existT (Exch v))
      else
        (fun _ : Name T => None) k).
  { easy. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  eapply SCCall with
    (a':=fun k =>
      if j =? k then
        Some (existT (Exch w))
      else if i =? k then
        Some (existT (Exch v))
      else
        (fun _ : Name T => None) k).
  { now rewrite eqb_nid. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  eapply SCRet with
    (a':=fun k =>
      if j =? k then
        None
      else if j =? k then
        Some (existT (Exch w))
      else if i =? k then
        Some (existT (Exch v))
      else
        (fun _ : Name T => None) k).
  { now rewrite eqb_id. }
  { now rewrite eqb_id. }
  { apply differ_pointwise_trivial. }
  eapply SCRet with
    (a':=fun k => None).
  { now rewrite eqb_id, eqb_nid. }
  { easy. }
  {
    unfold differ_pointwise.
    intros. dec_eq_nats j j0.
    { now rewrite eqb_id. }
    { now rewrite eqb_nid, eqb_nid. }
  }
  easy.
}
Qed.

Definition exchSpec {T A} : Spec T (ExchSig A) := {|
  State := ExchState T A;
  Step := ExchStep;
  Init := ExchDef {} {};
  seq_cons := exchSeqCons
|}.