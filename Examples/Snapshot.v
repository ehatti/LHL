From LHL.Core Require Import
  LogicPaco
  ProgramRules
  LogicFacts
  SingConds
  Program
  ProgramFacts
  VisPoss
  Tensor
  Traces
  Specs
  Logic.

From Paco Require Import paco.

From LHL.Examples Require Import
  SnapshotSpec
  AtomicSpec
  ArraySpec
  NameSpec
  RegSpec.

From LHL.Util Require Import
  TransUtil
  Tactics
  Util.

From Coq Require Import
  Logic.PropExtensionality
  Logic.FunctionalExtensionality
  Relations.Relation_Operators
  Relations.Operators_Properties
  Unicode.Utf8
  Classical.

Record reg_st {A} := MkReg {
  val : option A;
  ran : bool
}.
Arguments MkReg {A}.
Arguments reg_st : clear implicits.

Definition E T A :=
  NameSig T |+|
  ArraySig (RegSig (reg_st A)) T.

Definition RegCond {T A} (m1 m2 : Name T * sigT (RegSig A)) :=
  match snd m1 with
  | existT _ _ Read => False
  | _ =>
    match snd m2 with
    | existT _ _ Read => False
    | _ => True
    end
  end.

Definition VE T A : Spec T (E T A) :=
  tensorSpec
    nameSpec
    (arraySpec T
      (LiftSemiRacy
        RegCond
        (regSpec {| val := None; ran := false |}))).

Definition F A := SnapSig A.
Definition VF T A := @snapSpec T A.

Notation arrSt s i := (
  RState (snd s) i
).

Notation valSt s i := (
  ((RState (snd s) i).(racy_val))
).

Notation oranSt ρ i := (
  match ρ.(PState) with
  | SnapDef _ _ c => c i
  end
).

Notation uranSt s i := (
  ((RState (snd s) i).(racy_val))
).

Notation snapSt x := (
  match PState x with
  | SnapDef s _ _ => s
  end
).

Notation pendSt x := (
  match PState x with
  | SnapDef s _ _ => s
  end
).

Notation "` x" := (proj1_sig x) (at level 40).

Definition StateM E A R :=
  A -> Prog E (R * A).

Definition runStateM {E A R} (a : A) (m : StateM E A R) : Prog E (R * A) :=
  m a.

Definition get {E A} : StateM E A A :=
  λ a, ret (a, a).

Definition put {E A} (s : A) : StateM E A unit :=
  λ _, ret (tt, s).

Definition upd {E A} (f : A -> A) : StateM E A unit :=
  λ s, ret (tt, f s).

Definition bindM {E A B C}
  (m : StateM E A B)
  (k : B -> StateM E A C)
: StateM E A C :=
  λ s,
    p <- m s;
    k (fst p) (snd p).

Definition retM {E A R} (x : R) : StateM E A R :=
  λ s, ret (x, s).

Definition lift {E A R} (p : Prog E R) : StateM E A R :=
  λ s,
    r <- p;
    ret (r, s).

Notation "x <- f ;' m" := (bindM f (λ x, m)) (at level 80, right associativity).
Notation "f ;;' m" := (bindM f (λ _, m)) (at level 80, right associativity).

Section while.

Context {E A} (b : A -> bool) (e : StateM E A unit).

CoFixpoint whileAux (e' : Prog E (unit * A)) : Prog E (unit * A) :=
  match e' with
  | Return (tt, t) =>
    if b t then
      NoOp (whileAux (e t))
    else
      ret (tt, t)
  | Bind m k =>
    Bind m (λ x, whileAux (k x))
  | NoOp e' => NoOp (whileAux e')
  end.

Definition while s := whileAux (e s).

End while.

Require Import Lia.

Program Fixpoint range {E A} (n : nat) (e : Index n -> StateM E A unit) : StateM E A unit :=
  match n with
  | 0 => retM tt
  | S n => e n ;;' range n e
  end.
Next Obligation.
  destruct x.
  cbn. lia.
Qed.

Program Definition wkIx {N} (i : Index N) : Index (S N) := i.
Next Obligation.
  destruct i.
  cbn. lia.
Qed.

Section control_lemmas.

Context
  {T : nat} {E F : ESig}
  {VE : Spec T E} {VF : Spec T F}
  {R G : Relt VE VF}.

Lemma lemWhile {A} {i : Name T} :
  ∀ (b : A -> bool) (e : StateM E A unit)
    (I : A -> Relt VE VF),
    (* (∀ ths tht s x ρs,
      PointStep UnderThreadStep ths (i, None) tht ->
      I x (ths, s) ρs ()) *)
    (∀ x,
      VerifyProg i R G
        (λ s ρs t σs,
          b x = true /\
          I x s ρs t σs)
        (runStateM x e)
        (λ '(tt, y), I y)) ->
    ∀ x,
      VerifyProg i R G
        (I x)
        (runStateM x (while b e))
        (λ '(tt, y) s ρs t σs,
          b y = false /\
          I y s ρs t σs).
Proof.
  intros b e I H x. unfold while.
  unfold VerifyProg. rewrite paco_eqv.
  generalize dependent x. pcofix rec.
  intros x. pfold. unfold runStateM.
Admitted.

Lemma lemRange {A} {i : Name T} :
  ∀ (N : nat) (e : Index N -> StateM E A unit)
    (I : nat -> A -> Relt VE VF),
    (∀ n s,
      ∀ p : n < N,
      VerifyProg i R G
        (I (S n) s)
        (runStateM s (e (exist _ n p)))
        (λ '(tt, t), I n t)) ->
    ∀ s,
      VerifyProg i R G
        (I N s)
        (runStateM s (range N e))
        (λ r, I 0 (snd r)).
Proof.
  intros N e I H.
  induction N;
  cbn; intros s.
  { now constructor. }
  {
    eapply lemBind.
    { apply H. }
    {
      intros [[] t]. simpl in *.
      apply IHN. intros. apply H.
    }
  }
Qed.

End control_lemmas.

Program Definition zeroIx {N} : Index (S N) := 0.
Next Obligation. lia. Qed.

Lemma ret_lunit {E A B} :
  ∀ (v : A) (k : A -> Prog E B),
    (x <- ret v; k x) = k v.
Proof.
  intros v k.
  rewrite frobProgId at 1.
  simpl. now destruct (k v).
Qed.

Definition prop (P : Prop) : bool :=
  if classicT P then true else false.

Lemma prop_split P :
  (P /\ prop P = true) \/ (~P /\ prop P = false).
Proof.
  unfold prop.
  destruct (classicT P).
  now left.
  now right.
Qed.

Record loop_st {A} := MkSt {
  old : set A;
  new : set A
}.
Arguments loop_st : clear implicits.
Arguments MkSt {A}.

Definition fill_new {A} T : StateM (E T A) (loop_st A) unit :=
  range T (λ i,
    v <- lift (call (At i Read));'
    s <- get;'
    match v.(val) with
    | Some v => put {| old := s.(old); new := insert v s.(new)|}
    | None => retM tt
    end
  ).

(* fst is old, snd is new *)
Definition write_snapshot {T A} (v : A) : Prog (E T A) (option (set A)) :=
  i <- call Self;
  st <- call (At i Read);
  if st.(ran) then
    ret None
  else
    call (At i (Write {| val := Some v; ran := true |}));;
    res <- runStateM {| old := emp; new := emp |} (
      fill_new T;;'
      while (λ s, negb (s.(new) =? s.(old))) (
        s <- get;'
        put {| old := s.(new); new := emp |};;'
        fill_new T
      );;'
      s <- get;'
      retM (Some s.(new))
    );
    ret (fst res).

Definition snapImpl T A : Impl (E T A) (SnapSig A) :=
  λ _ m, match m with
  | WriteSnap v => write_snapshot v
  end.

Definition Relt T A := Relt (VE T A) (VF T A).
Definition Prec T A := Prec (VE T A) (VF T A).

Notation "x ⊆ y" :=
  (forall v, v ∈ x -> v ∈ y)
  (at level 40).

Lemma sub_trans {A} :
  ∀ s1 s3 : set A,
    (∃ s2,
      s1 ⊆ s2 /\
      s2 ⊆ s3) ->
    s1 ⊆ s3.
Proof.
  intros. psimpl.
  now apply H1, H.
Qed.

Notation "x ⊂ y" :=
  (x ≠ y /\ forall v, v ∈ x -> v ∈ y)
  (at level 40).

Record Idling {T} {F : ESig} {VF : Spec T F} (i : Name T)
  (x : Poss VF)
:= {
  p_idle : PCalls x i = CallIdle;
  r_idle : PRets x i = RetIdle;
}.

Record Called {T R} {F : ESig} {VF : Spec T F} (i : Name T) (m : F R)
  (x : Poss VF)
:= {
  pcalled : PCalls x i = CallDone m;
  ridle : PRets x i = RetIdle;
}.

Definition arr_set {T A} (s : InterState (F A) (VE T A)) (i : Name T) (v : A) := (
  ∃ w,
    (arrSt s i).(racy_val) = Some w /\
    w.(val) = Some v
).

Notation bound_set vs n s := (
  λ v, v ∈ vs /\ ∃ j, `j ≥ n /\ arr_set s j v
).

Lemma bound_set_emp {T A} :
  ∀ (vs : set A) (s : InterState (F A) (VE T A)),
    bound_set vs T s = emp.
Proof.
  intros. set_ext v.
  split; intros.
  {
    psimpl. destruct x.
    simpl in *. lia.
  }
  { easy. }
Qed.

Arguments MkPoss {T F VF}.

Definition RRet' (T : nat) (A R : Type) :=
  option (A * option (option (option (set R)))).

Definition RRet (T : nat) (A : Type) :=
  RRet' T A A.

Definition RPoss (T : nat) (A : Type) :=
  Name T -> RRet T A.
Notation PIdle := (None : RRet' _ _ _).
Notation PWait v := (Some (v, None) : RRet' _ _ _).
Notation PCall v := (Some (v, Some None) : RRet' _ _ _).
Notation PRetn v vs := (Some (v, Some (Some vs))).

Definition RPossSet (T : nat) (A : Type) :=
  RPoss T A -> Prop.

Record pdata {T A} := MkD {
  und_vals : Index T -> reg_st A;
  rets_map : Name T -> RRet' T A A
}.
Arguments pdata : clear implicits.
Arguments MkD {T A}.

Notation collect s := (λ v, ∃ i, (s i).(val) = Some v).

Definition conPoss {T A} d (ρ : RPoss T A) : Poss (VF T A) :=
  MkPoss (VF:= VF T A)
    (SnapDef
      (collect d)
      (λ i,
        match ρ i with
        | Some (v, Some None) => Some v
        | _ => None
        end)
      (λ i, (d i).(ran)))
    (λ i,
      match ρ i with
      | Some (v, None) => CallPoss (WriteSnap v)
      | Some (v, Some _) => CallDone (WriteSnap v)
      | _ => CallIdle
      end)
    (λ i,
      match ρ i with
      | Some (v, Some (Some vs)) => RetPoss (WriteSnap v) vs
      | _ => RetIdle
      end).

Variant PossDef {T A} {st : Name T -> reg_st A} :
  RRet' T A A -> RRet' T A A -> Prop :=
| PDIdle :
  PossDef None None
| PDWait v :
  PossDef (Some (v, None)) (Some (v, None))
| PDCall v :
  PossDef (Some (v, Some None)) (Some (v, Some None))
| PDRetnNone v :
  PossDef (Some (v, Some (Some None))) (Some (v, Some (Some None)))
| PDRetnSomeRetn v vi vs :
  vi ⊆ vs ->
  vs ⊆ collect st ->
  PossDef (Some (v, Some (Some (Some vi)))) (Some (v, Some (Some (Some vs))))
| PDRetnSomeCall v vi :
  PossDef (Some (v, Some (Some (Some vi)))) (Some (v, Some None)).
Arguments PossDef {T A} st _ _.

(* global invariant, should always hold *)
Record Inv {T A}
  {d : pdata T A}
  {s : InterState (F A) (VE T A)} {ρs : PossSet (VF T A)}
: Prop := {
  und_def :
    ∀ i, (arrSt s i).(racy_val) = Some (d.(und_vals) i);
  ovr_def :
    ρs = (λ ρ,
      ∃ dρ,
        (∀ i, PossDef d.(und_vals) (d.(rets_map) i) (dρ i)) /\
        ρ = conPoss d.(und_vals) dρ
    );
  vi_subs :
    ∀ i v vs,
      d.(rets_map) i = PRetn v (Some vs) ->
      vs ⊆ collect d.(und_vals)
}.
Arguments Inv {T A} d s ρs.

Definition updf {A B} (m : A -> B) (i : A) (v : B) : A -> B :=
  λ j, if i =? j then v else m j.

Record updt {A B} (m1 m2 : A -> B) (i : A) (v1 v2 : B) : Prop := {
  m1_set : m1 i = v1;
  m2_set : m2 i = v2;
  m_diff : differ_pointwise m1 m2 i
}.

Variant SnapTran {T A} {i : Name T} : pdata T A -> pdata T A -> Prop :=
| SnapInvoke v s x :
  x i = PIdle ->
  SnapTran
    (MkD s x)
    (MkD s (updf x i (PWait v)))
| SnapReturn v vi s (x : Name T -> RRet' T A A) :
  x i = PRetn v vi ->
  SnapTran
    (MkD s x)
    (MkD s (updf x i PIdle))
| SnapNoOp d :
  SnapTran d d
| SnapFail s v x :
  x i = PCall v ->
  SnapTran
    (MkD s x)
    (MkD s (updf x i (PRetn v None)))
| SnapWrite v s x :
  s i = MkReg None false ->
  x i = PCall v ->
  SnapTran
    (MkD s x)
    (MkD
      (updf s i (MkReg (Some v) true))
      (updf x i (PRetn v (Some (collect s))))).
Arguments SnapTran {T A} i.

Definition Guar {T A} (i : Name T) : Relt T A :=
  λ s ρs t σs,
    ∀ d,
      Inv d s ρs ->
      ∃ d',
        SnapTran i d d' /\
        Inv d' t σs.

Definition SnapTrans {T A} :=
  clos_refl_trans_1n (pdata T A) (λ d d', ∃ i, SnapTran i d d').

Definition OtherSnapTrans {T A} (i : Name T) :=
  clos_refl_trans_1n (pdata T A) (λ d d', ∃ j, i ≠ j /\ SnapTran j d d').

Definition Rely {T A} (i : Name T) : Relt T A :=
  λ s ρs t σs,
    ∀ d,
      Inv d s ρs ->
      ∃ d',
        OtherSnapTrans i d d' /\
        Inv d' t σs.

Lemma rely_refl {T A} :
  ∀ (i : Name T) s ρs,
    Rely (A:=A) i s ρs s ρs.
Proof.
  unfold Rely. intros.
  exists d. split.
  constructor. easy.
Qed.

Lemma rely_trans {T A} :
  ∀ i : Name T,
    Rely (A:=A) i ->> Rely i ==> Rely i.
Proof.
  unfold sub, subRelt, Rely.
  intros. psimpl.
  apply H in H0. psimpl.
  apply H1 in H2. psimpl.
  exists x2. split. 2: easy.
  eapply clos_rt_rt1n_iff.
  eapply rt_trans.
  {
    eapply clos_rt_rt1n_iff.
    exact H0.
  }
  {
    eapply clos_rt_rt1n_iff.
    exact H2.
  }
Qed.

Lemma sub_inter {A} :
  ∀ s1 s2 : set A,
    s1 ⊆ s2 ->
    (λ x, s1 x /\ s2 x) = s1.
Proof.
  intros. set_ext y.
  split; intros; psimpl.
  { easy. }
  {
    split. easy.
    now apply H.
  }
Qed.

Lemma done_ret {T F R} {VF : Spec T F} :
  ∀ (i j : Name T) (m : F R) (v : R) (ρ : Poss VF),
    i ≠ j ->
    Done i m v ρ ->
    Done i m v (retPoss j ρ).
Proof.
  intros. destruct H0.
  constructor; simpl;
  now rewrite eqb_nid.
Qed.

Lemma called_ret {T F R} {VF : Spec T F} :
  ∀ (i j : Name T) (m : F R) (ρ : Poss VF),
    i ≠ j ->
    Called i m ρ ->
    Called i m (retPoss j ρ).
Proof.
  intros. destruct H0.
  constructor; simpl;
  now rewrite eqb_nid.
Qed.

Lemma guar_in_rely {T A} :
  ∀ i j,
    i ≠ j ->
    @Guar T A i ==> @Rely T A j.
Proof.
  unfold sub, subRelt, Guar, Rely.
  intros. apply H0 in H1. psimpl.
  exists x. split.
  {
    econstructor.
    {
      exists i.
      split. easy.
      exact H1.
    }
    constructor.
  }
  { easy. }
Qed.

Definition Lift {T A} (P : pdata T A -> Prop) : Prec T A :=
  λ s ρs, ∃ d, Inv d s ρs /\ P d.

Lemma one_shot {T A} :
  ∀ d d',
    SnapTrans d d' ->
    ∀ (i : Name T) (v : A),
      (d.(und_vals) i).(val) = Some v ->
      d.(und_vals) i = d'.(und_vals) i.
Proof.
  intros.
  induction H. easy.
  cut (und_vals x i = und_vals y i).
  {
    intros.
    rewrite <-IHclos_refl_trans_1n.
    { easy. }
    { now rewrite <- H2. }
  }
  clear IHclos_refl_trans_1n H1.
  psimpl. destruct H; simpl in *; auto.
  unfold updf in *. dec_eq_nats x0 i.
  { now rewrite H in H0. }
  { now rewrite eqb_nid in *. }
Qed.

Lemma sub_ins {A} :
  ∀ (s1 s2 : set A) (v : A),
    s1 ⊆ s2 ->
    s1 ⊆ insert v s2.
Proof.
  intros s1 s2 v H ??.
  apply H in H0. now right.
Qed.

Lemma updt_triv {A B} :
  ∀ (m : A -> B) (i : A) (v1 v2 : B),
    m i = v1 ->
    updt m (updf m i v2) i v1 v2.
Proof.
  intros.
  constructor.
  { easy. }
  {
    unfold updf.
    now rewrite eqb_id.
  }
  { apply differ_pointwise_trivial. }
Qed.

Lemma map_ret_triv {T F R} {VF : Spec T F} :
  ∀ (i : Name T) (m : F R) (v : R) (ρ : Poss VF),
    Done i m v ρ ->
    mapRetPoss i m v ρ (retPoss i ρ).
Proof.
  unfold mapRetPoss.
  intros. simpl. destruct H.
  rewrite eqb_id. repeat split;
  (easy || apply differ_pointwise_trivial).
Qed.

Ltac specf H y := apply equal_f with (x:=y) in H.
Ltac gendep H := generalize dependent H.

Lemma conPoss_inj {T A} :
  ∀ (ρ σ : RPoss T A) u,
    conPoss u ρ = conPoss u σ ->
    ρ = σ.
Proof.
  intros.
  extensionality i.
  unfold conPoss in H.
  ddestruct H.
  specf x0 i.
  specf x1 i.
  specf x i.
  destruct (ρ i); simpl in *.
  {
    destruct p, o; simpl in *.
    {
      destruct o; simpl in *.
      {
        destruct (σ i); simpl in *.
        {
          destruct p, o0; simpl in *.
          {
            destruct o0; simpl in *.
            { now ddestruct x0. }
            { easy. }
          }
          { easy. }
        }
        { easy. }
      }
      {
        destruct (σ i); simpl in *.
        {
          destruct p, o; simpl in *.
          {
            destruct o.
            { easy. }
            { now ddestruct x1. }
          }
          { easy. }
        }
        { easy. }
      }
    }
    {
      destruct (σ i); simpl in *.
      {
        destruct p, o.
        { easy. }
        { now ddestruct x1. }
      }
      { easy. }
    }
  }
  {
    destruct (σ i).
    {
      destruct p, o.
      { easy. }
      { easy. }
    }
    { easy. }
  }
Qed.

Lemma ex_eq :
  ∀ A B (f : A -> B) (x : A) (P : A -> Prop),
    (∀ x y, f x = f y -> x = y) ->
    (∃ y, P y /\ f x = f y) = P x.
Proof.
  intros.
  apply propositional_extensionality.
  split; intros; psimpl.
  {
    apply H in H1.
    now subst.
  }
  { now exists x. }
Qed.

Lemma set_eq {A} :
  ∀ P Q : A -> Prop,
    (P = Q) = (∀ x, P x <-> Q x).
Proof.
  intros.
  apply propositional_extensionality.
  split; intros.
  { now subst. }
  { now set_ext x. }
Qed.

Ltac dstr_rposs :=
  repeat match goal with
  | x : option _ |- _ => destruct x
  | x : prod _ _ |- _ => destruct x
  end.

Lemma PS_refl {T A} :
  ∀ (s : Name T -> reg_st A) ls,
  (∀ v vs, ls = PRetn v (Some vs) -> vs ⊆ collect s) ->
  PossDef s ls ls.
Proof.
  intros.
  dstr_rposs;
  constructor; auto.
  now eapply H.
Qed.

Lemma rets_map_uniq {T A} :
  ∀ (d : pdata T A) s ρs,
    Inv d s ρs ->
    ∀ ls,
      Inv (MkD d.(und_vals) ls) s ρs ->
      d.(rets_map) = ls.
Proof.
  intros.
  destruct H, H0, d. psimpl.
  rename rets_map0 into ls'.
  assert (
    (λ ρ, ∀ i, PossDef und_vals0 (ls' i) (ρ i)) =
    (λ ρ, ∀ i, PossDef und_vals0 (ls i) (ρ i))
  ).
  {
    set_ext ρ.
    apply equal_f with
      (x:= conPoss und_vals0 ρ)
      in ovr_def1.
    do 2 rewrite ex_eq in ovr_def1.
    all: try (
      intros;
      now apply conPoss_inj
        with (u:=und_vals0)
    ).
    now rewrite ovr_def1.
  }
  clear - H vi_subs0 vi_subs1.
  rewrite set_eq in H.
  assert (H' := H).
  specialize (H ls).
  specialize (H' ls').
  assert (∀ i, PossDef und_vals0 (ls i) (ls i)).
  {
    intros.
    apply PS_refl.
    apply vi_subs1.
  }
  assert (∀ i, PossDef und_vals0 (ls' i) (ls' i)).
  {
    intros.
    apply PS_refl.
    apply vi_subs0.
  }
  destruct H, H'.
  extensionality i.
  apply H2 with (i:=i) in H0.
  apply H3 with (i:=i) in H1.
  generalize dependent (ls' i).
  generalize dependent (ls i).
  intros. clear - H0 H1.
  destruct H0; ddestruct H1; try easy.
  assert (vs = vi).
  {
    set_ext y.
    split; intros.
    { now apply H1. }
    { now apply H. }
  }
  now subst.
Qed.

Lemma Inv_eqv {T A} :
  ∀ (d1 d2 : pdata T A) s ρs,
    Inv d1 s ρs ->
    Inv d2 s ρs ->
    d1 = d2.
Proof.
  intros.
  destruct d1, d2.
  destruct H, H0.
  simpl in *.
  assert (und_vals1 = und_vals0).
  {
    extensionality i.
    clear ovr_def0 ovr_def1.
    specialize (und_def0 i).
    specialize (und_def1 i).
    rewrite und_def0 in und_def1.
    now ddestruct und_def1.
  }
  subst. f_equal.
  eapply rets_map_uniq with
    (d:= MkD _ _).
  {
    constructor.
    { exact und_def0. }
    { easy. }
    { easy. }
  }
  { now constructor. }
Qed.

Lemma invoke_in_rely {T A} :
  ∀ i j,
    i ≠ j ->
    InvokeAny (snapImpl T A) i ==> Rely j.
Proof.
  unfold
    InvokeAny, TInvoke, TIdle,
    sub, subRelt, Rely.
  intros. psimpl. destruct d, x0.
  exists (MkD und_vals0 (updf rets_map0 i (PWait v))).
  destruct H1. psimpl.
  assert (rets_map0 i = PIdle).
  {
    specialize (H5 (conPoss und_vals0 rets_map0)).
    eassert _.
    {
      apply H5.
      exists rets_map0.
      split. 2: easy. intros.
      apply PS_refl, vi_subs0.
    }
    clear - X.
    unfold conPoss in *. psimpl.
    gendep (rets_map0 i). intros.
    unfold RRet' in r. now dstr_rposs.
  }
  split.
  {
    econstructor.
    2: constructor.
    exists i. split. easy.
    now apply SnapInvoke.
  }
  {
    constructor; simpl.
    {now setoid_rewrite <- H3. }
    {
      set_ext σ.
      split; intros; psimpl.
      exists (updf x0 i (PWait v)).
      split.
      {
        unfold updf. intros.
        dec_eq_nats i0 i.
        {
          rewrite eqb_id.
          constructor.
        }
        { rewrite eqb_nid; auto. }
      }
      {
        unfold updf, conPoss in *.
        destruct σ. psimpl.
        repeat f_equal.
        {
          extensionality k.
          dec_eq_nats k i.
          {
            rewrite eqb_id.
            specialize (H4 i).
            rewrite H1 in H4.
            ddestruct H4.
            now rewrite <- x.
          }
          { now rewrite eqb_nid; auto. }
        }
        {
          extensionality k.
          dec_eq_nats k i.
          { now rewrite eqb_id. }
          { now rewrite eqb_nid, H9. }
        }
        {
          extensionality k.
          dec_eq_nats k i.
          { now rewrite eqb_id. }
          { now rewrite eqb_nid, H10. }
        }
      }
      {
        exists (conPoss und_vals0 (updf x i PIdle)).
        split.
        {
          eexists.
          split. 2: easy.
          intros. specialize (H4 i0).
          unfold updf in *. dec_eq_nats i0 i.
          {
            rewrite eqb_id in *.
            rewrite H1. constructor.
          }
          { rewrite eqb_nid in *; auto. }
        }
        specialize (H4 i).
        unfold updf in H4.
        rewrite eqb_id in H4.
        ddestruct H4.
        unfold updf, conPoss.
        psimpl. rewrite <- x.
        split.
        {
          repeat f_equal.
          extensionality k.
          dec_eq_nats k i.
          { now rewrite eqb_id, <- x. }
          { rewrite eqb_nid; auto. }
        }
        split.
        { easy. }
        split.
        { easy. }
        split.
        {
          intros ??.
          now rewrite eqb_nid.
        }
        {
          intros ??.
          now rewrite eqb_nid.
        }
      }
    }
    {
      unfold updf. intros.
      dec_eq_nats i0 i.
      { now rewrite eqb_id in H4. }
      {
        rewrite eqb_nid in H4; auto.
        eapply vi_subs0. exact H4. easy.
      }
    }
  }
Qed.

Lemma return_in_rely {T A} :
  ∀ i j,
    i ≠ j ->
    ReturnAny (snapImpl T A) i ==> Rely j.
Proof.
  unfold
    ReturnAny, TReturn,
    sub, subRelt, Rely,
    mapRetPoss, Returned.
  intros. psimpl. destruct d, x0.
  exists (MkD und_vals0 (updf rets_map0 i PIdle)).
  destruct H1. psimpl. rename x1 into vi.
  ddestruct H2. psimpl. ddestruct H1.
  assert (rets_map0 i = PRetn v vi).
  {
    symmetry in x0.
    specialize (H0 x0 (conPoss und_vals0 rets_map0)).
    eassert _.
    {
      apply H0.
      exists rets_map0.
      split. 2: easy. intros.
      apply PS_refl, vi_subs0.
    }
    clear - X.
    unfold conPoss in *. psimpl.
    gendep (rets_map0 i). intros.
    unfold RRet' in r.
    dstr_rposs; try easy.
    {
      ddestruct H0.
      gendep (Some s0). gendep (Some s).
      intros. now ddestruct H.
    }
    { ddestruct H0. }
    { ddestruct H0. }
    { now ddestruct H0. }
  }
  split.
  {
    econstructor.
    2: constructor.
    exists i. split. easy.
    now apply SnapReturn with
      (v:=v) (vi:=vi).
  }
  {
    constructor; simpl.
    { now setoid_rewrite <- H3. }
    {
      set_ext σ.
      split; intros; psimpl.
      {
        exists (updf x2 i None).
        split.
        {
          unfold updf.
          intros. dec_eq_nats i0 i.
          {
            rewrite eqb_id.
            constructor.
          }
          { rewrite eqb_nid; auto. }
        }
        {
          unfold conPoss, updf in *.
          unfold updf, conPoss in *.
          destruct σ. psimpl.
          repeat f_equal.
          {
            extensionality k.
            dec_eq_nats k i.
            {
              rewrite eqb_id.
              destruct (x2 i).
              2: easy.
              destruct p, o.
              2: easy.
              now destruct o.
            }
            { now rewrite eqb_nid; auto. }
          }
          {
            extensionality k.
            dec_eq_nats k i.
            { now rewrite eqb_id. }
            { now rewrite eqb_nid, H9. }
          }
          {
            extensionality k.
            dec_eq_nats k i.
            { now rewrite eqb_id. }
            { now rewrite eqb_nid, H10. }
          }
        }
      }
      {
        exists (conPoss und_vals0 (updf x1 i (PRetn v vi))).
        split.
        {
          eexists.
          split. 2: easy.
          intros. unfold updf in *.
          dec_eq_nats i0 i.
          {
            rewrite eqb_id, H1.
            destruct vi; constructor.
            { easy. }
            { eapply vi_subs0. exact H1. }
          }
          {
            specialize (H4 i0).
            rewrite eqb_nid in *; auto.
          }
        }
        assert (x1 i = None).
        {
          specialize (H4 i).
          unfold updf in H4.
          rewrite eqb_id in H4.
          now ddestruct H4.
        }
        unfold conPoss, updf. psimpl.
        rewrite eqb_id, H5.
        split. easy.
        split. easy.
        split. easy.
        split. easy.
        split.
        {
          unfold differ_pointwise.
          intros. now rewrite eqb_nid.
        }
        split.
        {
          unfold differ_pointwise.
          intros. now rewrite eqb_nid.
        }
        {
          repeat f_equal.
          extensionality k.
          dec_eq_nats k i.
          { now rewrite eqb_id, H5. }
          { now rewrite eqb_nid; auto. }
        }
      }
    }
    {
      unfold updf. intros.
      dec_eq_nats i0 i.
      { now rewrite eqb_id in H4. }
      {
        rewrite eqb_nid in H4; auto.
        eapply vi_subs0. exact H4. easy.
      }
    }
  }
Qed.

Lemma return_step {T A} :
  ∀ (i : Name T) (v : A) (r : option (set A)),
    ReturnStep i (Guar i)
      (λ s ρs,
        ∃ d, Inv d s ρs /\
          ((
            r = None /\
            d.(rets_map) i = PRetn v None
          ) \/
          (
            ∃ vi new,
              r = Some new /\
              d.(rets_map) i = PRetn v (Some vi) /\
              vi ⊆ new /\
              new ⊆ collect d.(und_vals)
          )))
      (WriteSnap v) r
      (λ _ _ s ρs,
        ∃ d, Inv d s ρs).
Proof.
  intros i v r s ρs H _.
  psimpl. destruct H0; psimpl.
  {
    rename x into d.
    exists (λ σ, ρs σ /\
      Done i (WriteSnap v) None σ).
    split.
    {
      destruct d, H. psimpl.
      pose (σ j :=
        if i =? j then
          PRetn v None
        else
          rets_map0 j).
      exists (conPoss und_vals0 σ).
      split.
      {
        eexists.
        split. 2: easy.
        intros. subst σ.
        simpl. dec_eq_nats i0 i.
        {
          rewrite H1, eqb_id.
          now constructor.
        }
        {
          rewrite eqb_nid; auto.
          apply PS_refl, vi_subs0.
        }
      }
      {
        subst σ. unfold conPoss.
        constructor; simpl;
        now rewrite eqb_id.
      }
    }
    split.
    {
      intros. psimpl. exists σ.
      split. easy. constructor.
    }
    split.
    {
      intros. psimpl.
      now destruct H2.
    }
    destruct d.
    assert (
      Inv
        (MkD
          und_vals0
          (updf rets_map0 i None))
        (λ j, if i =? j then Idle else fst s j, snd s)
        (λ τ,
          ∃ σ,
          (ρs σ ∧ Done i (WriteSnap v) None σ) /\
          mapRetPoss i (WriteSnap v) None σ τ)
    ).
    {
      destruct H. psimpl.
      constructor; simpl; auto.
      {
        set_ext σ. unfold mapRetPoss.
        split; intros; psimpl.
        {
          exists (λ j,
            if i =? j then
              None
            else
              x0 j).
          split.
          {
            intros. unfold updf.
            dec_eq_nats i0 i.
            {
              rewrite eqb_id.
              constructor.
            }
            { rewrite eqb_nid; auto. }
          }
          {
            destruct H8.
            unfold conPoss in *.
            destruct σ. psimpl.
            repeat f_equal.
            {
              extensionality j.
              dec_eq_nats j i.
              {
                rewrite eqb_id.
                destruct (x0 i).
                2: easy.
                destruct p, o.
                2: easy.
                now destruct o.
              }
              { now rewrite eqb_nid. }
            }
            {
              extensionality j.
              dec_eq_nats j i.
              { now rewrite eqb_id. }
              { now rewrite eqb_nid, H5. }
            }
            {
              extensionality j.
              dec_eq_nats j i.
              { now rewrite eqb_id. }
              { now rewrite eqb_nid, H6. }
            }
          }
        }
        {
          exists (conPoss und_vals0 (updf x i (PRetn v None))).
          split.
          {
            split.
            {
              eexists.
              split. 2: easy.
              unfold updf in *.
              intros. specialize (H i0).
              dec_eq_nats i0 i.
              {
                rewrite eqb_id in *.
                rewrite H1. now constructor.
              }
              { rewrite eqb_nid in *; auto. }
            }
            {
              unfold conPoss, updf.
              constructor; simpl;
              now rewrite eqb_id.
            }
          }
          assert (x i = None).
          {
            specialize (H i).
            unfold updf in H.
            rewrite eqb_id in H.
            now ddestruct H.
          }
          unfold updf. simpl.
          rewrite eqb_id, H0.
          split. easy.
          split. easy.
          split. easy.
          split. easy.
          split.
          {
            intros ??.
            now rewrite eqb_nid.
          }
          split.
          {
            intros ??.
            now rewrite eqb_nid.
          }
          {
            repeat f_equal.
            extensionality j.
            dec_eq_nats j i.
            { now rewrite eqb_id, H0. }
            { rewrite eqb_nid; auto. }
          }
        }
      }
      {
        unfold updf.
        intros. dec_eq_nats i0 i.
        { now rewrite eqb_id in H. }
        {
          rewrite eqb_nid in H; auto.
          eapply vi_subs0. exact H. easy.
        }
      }
    }
    split.
    { eexists. exact H0. }
    {
      intros ??.
      eapply Inv_eqv in H2.
      2: exact H. psimpl.
      eexists. split.
      {
        now apply SnapReturn with
          (v:=v) (vi:=None).
      }
      { easy. }
    }
  }
  {
    rename x into d.
    rename x0 into vi.
    rename x1 into new.
    exists (λ σ, ρs σ /\
      Done i (WriteSnap v) (Some new) σ).
    split.
    {
      destruct d, H. psimpl.
      pose (σ j :=
        if i =? j then
          PRetn v (Some new)
        else
          rets_map0 j).
      exists (conPoss und_vals0 σ).
      split.
      {
        eexists.
        split. 2: easy.
        intros. subst σ.
        simpl. dec_eq_nats i0 i.
        {
          rewrite H1, eqb_id.
          now constructor.
        }
        {
          rewrite eqb_nid; auto.
          apply PS_refl, vi_subs0.
        }
      }
      {
        subst σ. unfold conPoss.
        constructor; simpl;
        now rewrite eqb_id.
      }
    }
    split.
    {
      intros. psimpl.
      exists σ. split.
      easy. constructor.
    }
    split.
    {
      intros. psimpl.
      now destruct H4.
    }
    destruct d.
    assert (
      Inv
        {| und_vals := und_vals0; rets_map := updf rets_map0 i None |}
        (λ j, if i =? j then Idle else fst s j, snd s)
        (λ τ,
          ∃ σ,
            (ρs σ ∧ Done i (WriteSnap v) (Some new) σ) /\
            mapRetPoss i (WriteSnap v) (Some new) σ τ)
    ).
    {
      destruct H. psimpl.
      constructor; simpl; auto.
      {
        set_ext σ. unfold mapRetPoss.
        split; intros; psimpl.
        {
          exists (λ j,
            if i =? j then
              None
            else
              x0 j).
          split.
          {
            intros. unfold updf.
            dec_eq_nats i0 i.
            {
              rewrite eqb_id.
              constructor.
            }
            { rewrite eqb_nid; auto. }
          }
          {
            destruct H10.
            unfold conPoss in *.
            destruct σ. psimpl.
            repeat f_equal.
            {
              extensionality j.
              dec_eq_nats j i.
              {
                rewrite eqb_id.
                destruct (x0 i).
                2: easy.
                destruct p, o.
                2: easy.
                now destruct o.
              }
              { now rewrite eqb_nid. }
            }
            {
              extensionality j.
              dec_eq_nats j i.
              { now rewrite eqb_id. }
              { now rewrite eqb_nid, H7. }
            }
            {
              extensionality j.
              dec_eq_nats j i.
              { now rewrite eqb_id. }
              { now rewrite eqb_nid, H8. }
            }
          }
        }
        {
          exists (conPoss und_vals0 (updf x i (PRetn v (Some new)))).
          split.
          {
            split.
            {
              eexists.
              split. 2: easy.
              unfold updf in *.
              intros. specialize (H i0).
              dec_eq_nats i0 i.
              {
                rewrite eqb_id in *.
                rewrite H1. now constructor.
              }
              { rewrite eqb_nid in *; auto. }
            }
            {
              unfold conPoss, updf.
              constructor; simpl;
              now rewrite eqb_id.
            }
          }
          assert (x i = None).
          {
            specialize (H i).
            unfold updf in H.
            rewrite eqb_id in H.
            now ddestruct H.
          }
          unfold updf. simpl.
          rewrite eqb_id, H0.
          split. easy.
          split. easy.
          split. easy.
          split. easy.
          split.
          {
            intros ??.
            now rewrite eqb_nid.
          }
          split.
          {
            intros ??.
            now rewrite eqb_nid.
          }
          {
            repeat f_equal.
            extensionality j.
            dec_eq_nats j i.
            { now rewrite eqb_id, H0. }
            { rewrite eqb_nid; auto. }
          }
        }
      }
      {
        unfold updf.
        intros. dec_eq_nats i0 i.
        { now rewrite eqb_id in H. }
        {
          rewrite eqb_nid in H; auto.
          eapply vi_subs0. exact H. easy.
        }
      }
    }
    split.
    { eexists. exact H0. }
    {
      intros ??.
      eassert (_ = d).
      {
        eapply Inv_eqv.
        exact H. easy.
      }
      psimpl. eexists.
      split.
      {
        now apply SnapReturn with
          (v:=v) (vi:= Some vi).
      }
      { easy. }
    }
  }
Qed.

Check @lemCall.
Arguments lemCall {T i E F VE VF R G A} Q S.

Lemma write_correct {T A} (i : Name T) (v : A) :
  VerifyProg i (Rely i) (Guar i)
    (λ _ _ s ρs,
      ∃ d,
        Inv d s ρs /\
        d.(rets_map) i = PWait v)
    (call (At i (Write (MkReg (Some v) true))))
    (λ 'tt _ _ s ρs,
      ∃ d vi,
        Inv d s ρs /\
        d.(rets_map) i = PRetn v (Some vi)).
Proof.
Admitted.

Lemma fill_new_correct {T A} (i : Name T) (v : A) (x : loop_st A) :
  VerifyProg i (Rely i) (Guar i)
    (λ _ _ s ρs,
      ∃ d vi,
        Inv d s ρs /\
        d.(rets_map) i = PRetn v (Some vi))
    (fill_new T x)
    (λ '(tt, y) _ _ s ρs,
      ∃ d vi,
        Inv d s ρs /\
        d.(rets_map) i = PRetn v (Some vi) /\
        vi ⊆ x.(new) /\
        x.(new) ⊆ collect d.(und_vals)).
Proof.
  unfold fill_new, runStateM, bindM.
  simpl. eapply weakenPost.
Admitted.

Lemma ws_correct {T A} (i : Name T) (v : A) :
  VerifyProg i (Rely i) (Guar i)
    (prComp
      (λ s ρs,
        ∃ d, Inv d s ρs)
      (TInvoke (snapImpl T A) i _ (WriteSnap v)) ->> Rely i)
    (write_snapshot v)
    (λ r _ _ s ρs,
      ∃ d, Inv d s ρs /\
        ((
          r = None /\
          d.(rets_map) i = PRetn v None
        ) \/
        (
          ∃ vi new,
            r = Some new /\
            d.(rets_map) i = PRetn v (Some vi) /\
            vi ⊆ new /\
            new ⊆ collect d.(und_vals)
        ))).
Proof.
  (* eapply weakenPrec with
    (P:=λ _ _ s ρs,
      ∃ d,
        Inv d s ρs /\
        d.(rets_map) i = PWait v).
  2:{
    unfold sub, subRelt.
    intros. psimpl.
    rename x1 into d.
    rename ρ into ρs.
    rename σ into σs.
    assert (
      Inv
        (MkD d.(und_vals) (updf d.(rets_map) i (PWait v)))
        x x0
    ).
    {
      clear - H H1.
      unfold TInvoke, TIdle in H1.
      destruct H. psimpl.
      constructor; simpl.
      { now setoid_rewrite <- H1. }
      {
        set_ext σ.
        split; intros; psimpl.
        {
          assert (
            PCalls (conPoss d.(und_vals) x1) i = CallIdle /\
            PRets (conPoss d.(und_vals) x1) i = RetIdle
          ).
          {
            admit.
          }
          exists (updf x1 i (PWait v)).
          split.
          {
            unfold updf.
            intros. dec_eq_nats i0 i.
            {
              rewrite eqb_id.
              constructor.
            }
            { rewrite eqb_nid; auto. }
          }
          {
            unfold conPoss, updf in *.
            destruct σ. psimpl.
            repeat f_equal.
            {
              extensionality j.
              dec_eq_nats j i.
              {
                rewrite eqb_id. clear - H9 H10.
                gendep (x1 i). unfold RRet'.
                intros. now dstr_rposs.
              }
              { rewrite eqb_nid; auto. }
            }
            {
              extensionality j.
              dec_eq_nats j i.
              { now rewrite eqb_id. }
              { now rewrite eqb_nid, H7. }
            }
            {
              extensionality j.
              dec_eq_nats j i.
              { now rewrite eqb_id. }
              { now rewrite eqb_nid, H8. }
            }
          }
        }
        {
          exists (conPoss d.(und_vals) (updf x0 i (PWait v))).
          split.
          {
            eexists.
            split. 2: easy.
            intros. specialize (H2 i0).
            unfold updf in *.
            dec_eq_nats i0 i.
            {
              rewrite eqb_id in H2.
            }
          }
        }
      }
    }
  }
  unfold write_snapshot.
  eapply lemBindSelf.
  {
    admit.
  }
  eapply lemBind.
  {
    eapply lemCall with
      (Q:=).
  } *)
Admitted.

Check ReturnStep.

Lemma wk_return_step {T E F} {VE : Spec T E} {VF : Spec T F} :
  ∀ (P P' : Logic.Prec VE VF)
    (G Q : Logic.Relt VE VF)
    (i : Name T) A
    (m : F A) (v : A),
    P' ==> P ->
    ReturnStep i G P m v Q ->
    ReturnStep i G P' m v Q.
Proof.
  unfold ReturnStep.
  intros. apply H0; auto.
Qed.

Theorem writeSnapshotCorrect {T A} :
  VerifyImpl (VE T A) (VF T A)
    Rely Guar
    (λ i _ _ s ρs,
      ∃ d,
        Inv d s ρs)
    (snapImpl T A)
    (λ i _ '(WriteSnap v) r _ _ s ρs,
      ∃ d, Inv d s ρs /\
        ((
          r = None /\
          d.(rets_map) i = PRetn v None
        ) \/
        (
          ∃ vi new,
            r = Some new /\
            d.(rets_map) i = PRetn v (Some vi) /\
            vi ⊆ new /\
            new ⊆ collect d.(und_vals)
        )))
    (λ i _ _ _ _ _ s ρs,
      ∃ d,
        Inv d s ρs).
Proof.
  constructor.
  { apply rely_refl. }
  { apply rely_trans. }
  { apply guar_in_rely. }
  { apply invoke_in_rely. }
  { apply return_in_rely. }
  {
    intros.
    exists (MkD (λ _, MkReg None false) (λ _, PIdle)).
    constructor; psimpl; auto.
    {
      set_ext ρ.
      split; intros; psimpl.
      {
        exists (λ _, PIdle).
        split.
        {
          intros.
          constructor.
        }
        {
          unfold initPoss, conPoss.
          repeat f_equal. cbv.
          repeat f_equal. set_ext v.
          split; intro; now psimpl.
        }
      }
      {
        unfold initPoss, conPoss.
        repeat f_equal.
        {
          cbv.
          repeat f_equal.
          {
            set_ext v.
            split; intro; now psimpl.
          }
          {
            extensionality j.
            specialize (H j).
            ddestruct H.
            now rewrite <- x.
          }
        }
        {
          extensionality j.
          specialize (H j).
          ddestruct H.
          now rewrite <- x.
        }
        {
          extensionality j.
          specialize (H j).
          ddestruct H.
          now rewrite <- x.
        }
      }
    }
    { easy. }
  }
  {
    unfold
      Stable, stablePrec,
      sub, subPrec, Rely.
    intros. psimpl.
    apply H0 in H.
    psimpl. now exists x2.
  }
  {
    unfold sub, subPrec.
    intros. psimpl.
    now exists x1.
  }
  {
    intros. destruct m.
    apply ws_correct.
  }
  {
    intros. destruct m.
    eapply wk_return_step.
    2: apply return_step.
    {
      intros ???. psimpl.
      now exists x1.
    }
  }
Qed.