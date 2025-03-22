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
  OrderedSpec
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
  Logic.ClassicalChoice
  Program.Equality
  Relations.Relation_Operators
  Relations.Operators_Properties
  Lists.List
  Unicode.Utf8
  Classical.

Set Warnings "-cannot-define-projection".

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
    (ordSpec
      (arraySpec T
        (LiftSemiRacy
          RegCond
          (regSpec {| val := None; ran := false |})))).

Definition F A := SnapSig A.
Definition VF T A := @snapSpec T A.

Notation arrSt s i := (
  (RState (snd s)).(os_st) i
).

Notation valSt s i := (
  ((RState (snd s) i).(racy_val))
).

Notation oranSt ρ i := (
  match ρ.(PState) with
  | SnapDef _ _ _ => i
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
    (I : A -> Prec VE VF),
    (forall x, Stable R (I x)) ->
    (forall x, SilentStep i G (I x) (λ _ _, I x)) ->
    (∀ x,
      VerifyProg i R G
        (λ _ _, I x)
        (e x)
        (λ '(tt, y) _ _, I y)) ->
    ∀ x,
      VerifyProg i R G
        (λ _ _, I x)
        (while b e x)
        (λ '(tt, y) _ _ t σs, I y t σs /\ b y = false).
Proof.
  intros b e I.
  intros S_stable.
  intros I_silent.
  intros.
  unfold VerifyProg in *.
  rewrite paco_eqv.
  unfold while.
  pose proof (H' := H).
  specialize (H x).
  generalize dependent (e x).
  generalize dependent (λ (_ : InterState F VE) (_ : PossSet VF), I x).
  clear x. pcofix rec. intros.
  rewrite frobProgId at 1.
  destruct p0; cbn; ddestruct H0; pfold.
  {
    econstructor.
    { exact H. }
    { exact H0. }
    { easy. }
    {
      intros.
      specialize (H2 v).
      destruct H2.
      split. easy.
      right. now eapply rec.
    }
  }
  {
    simpl (frobProgram _).
    destruct p0, u.
    remember (b a) as test eqn:Htest.
    destruct test.
    {
      eapply LogicPaco.SafeNoOp with
        (QS:= λ _ _, I a).
      {
        intros ?????.
        apply S_stable.
        psimpl. psplit.
        exact H0. easy.
      }
      {
        intros ???????.
        apply I_silent; auto.
        destruct H0, H0.
        now apply H in H0.
      }
      {
        right.
        eapply rec.
        eapply weakenPrec.
        { apply H'. }
        {
          intros ?????.
          now psimpl.
        }
      }
    }
    {
      rewrite foldProg.
      constructor.
      intros ?????.
      now apply H in H0.
    }
  }
  {
    econstructor.
    { exact H. }
    { easy. }
    {
      right.
      now eapply rec.
    }
  }
Qed.

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

Lemma lemCallWk {A} {P : Relt VE VF} {m : E A} :
  ∀ (i : Name T) Q S,
  Stable R Q ->
  (∀ v, Stable R (S v)) ->
  Commit i G P (CallEv m) (λ _ _, Q) ->
  (forall v, Commit i G Q (RetEv m v) (λ _ _, S v)) ->
  VerifyProg i R G P (call m) (λ v _ _, S v).
Proof.
  intros.
  eapply weakenPost.
  eapply (lemCall
    (Q:=λ _ _, Q)
    (S:=λ v _ _, S v)).
  { easy. }
  {
    unfold
      Stable, stablePost,
      stableRelt, sub, subRelt.
    intros. psimpl.
    apply H0.
    now exists x, x0.
  }
  { easy. }
  {
    unfold Commit.
    intros. apply H2.
    now psimpl.
    all: easy.
  }
  {
    intros ??????.
    now psimpl.
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

Definition OWr T A := list (Name T * Index T * A).

Definition Prefix {A} (xs zs : list A) :=
  ∃ ys, zs = xs ++ ys.

Lemma prefix_cons {A} :
  ∀ (xs ys zs : list A),
    Prefix xs ys ->
    Prefix xs (ys ++ zs).
Proof.
  unfold Prefix.
  intros. psimpl.
  exists (x ++ zs).
  now rewrite app_assoc.
Qed.

Lemma prefix_trans {A} :
  ∀ xs ys zs : list A,
    Prefix xs ys ->
    Prefix ys zs ->
    Prefix xs zs.
Proof.
  unfold Prefix.
  intros. psimpl.
  exists (x0 ++ x).
  now rewrite app_assoc.
Qed.

Lemma prefix_refl {A} :
  ∀ xs : list A,
    Prefix xs xs.
Proof.
  intros. exists nil.
  now rewrite app_nil_r.
Qed.


Notation set_of xs := (λ v, ∃ i, List.In (i, i, v) xs).

Record ObWr {T A} (vs : set A) (wr : OWr T A) : Prop := {
  pfx : OWr T A;
  pfx_def : vs = (λ v, ∃ i, List.In (i, i, v) pfx);
  pfx_prefix : Prefix pfx wr
}.
Arguments ObWr {T A} vs wr.

Record pdata {T A} := MkD {
  und_vals : Index T -> reg_st A;
  rets_map : Name T -> RRet' T A A;
  wrt_ordn : OWr T A
}.
Arguments pdata : clear implicits.
Arguments MkD {T A}.

Notation collect s := (λ v, ∃ i, (s i).(val) = Some v).

Definition conPoss {T A} (d : Index T -> reg_st A) (ρ : RPoss T A) : Poss (VF T A) :=
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

Variant PossDef {T A} {wr : OWr T A} {st : Name T -> reg_st A} :
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
  ObWr vs wr ->
  vi ⊆ vs ->
  vs ⊆ collect st ->
  PossDef (Some (v, Some (Some (Some vi)))) (Some (v, Some (Some (Some vs))))
| PDRetnSomeCall v vi :
  PossDef (Some (v, Some (Some (Some vi)))) (Some (v, Some None)).
Arguments PossDef {T A} wr st _ _.

Inductive WrtDef {T A} :
  list (Name T * {R & prod (ArraySig (RegSig (reg_st A)) T R) R}) ->
  OWr T A ->
  Prop :=
| WDEnd :
  WrtDef nil nil
| WDSkip i n v os wr :
  WrtDef os wr ->
  WrtDef ((i, existT _ _ (At n Read, v)) :: os) wr
| WDKeep (i : Name T) (v : A) os (wr : OWr T A) :
  WrtDef os wr ->
  WrtDef ((i, existT _ _ (At i (Write (MkReg (Some v) true)), tt)) :: os) ((i, i, v) :: wr).

Record bisub {X} (A B : set X) := {
  sub_fwd : A ⊆ B;
  sub_bwd : B ⊆ A
}.
Infix "≡" := bisub (at level 40).

(* global invariant, should always hold *)
Record Inv {T A}
  {d : pdata T A}
  {s : InterState (F A) (VE T A)} {ρs : PossSet (VF T A)}
: Prop := {
  und_def :
    ∀ i, (arrSt s i).(racy_val) = Some (d.(und_vals) i);
  wrt_def :
    WrtDef (RState (snd s)).(os_ord) d.(wrt_ordn);
  ovr_def :
    ρs = (λ ρ,
      ∃ dρ,
        (∀ i, PossDef d.(wrt_ordn) d.(und_vals) (d.(rets_map) i) (dρ i)) /\
        ρ = conPoss d.(und_vals) dρ
    );
  vi_subs :
    ∀ i v vs,
      d.(rets_map) i = PRetn v (Some vs) ->
      vs ⊆ collect d.(und_vals);
  resp_own :
    ∀ i,
      ¬∃ j r, i ≠ j /\
        (j, existT _ _ (Write r)) ∈ (arrSt s i).(racy_pend);
  resp_write :
    ∀ i,
      (d.(und_vals) i).(ran) = false ->
      (d.(und_vals) i).(val) = None;
  resp_ran :
    ∀ i,
      (∃ v o, d.(rets_map) i = Some (v, Some o)) ->
      (d.(und_vals) i).(ran) = true;
  ordn_val :
    ∀ i v, List.In (i, i, v) d.(wrt_ordn) <-> (d.(und_vals) i).(val) = Some v;
  ob_write :
    ∀ i v vi,
      d.(rets_map) i = PRetn v (Some vi) ->
      ObWr vi d.(wrt_ordn)
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
| SnapInvoke v s x o :
  x i = PIdle ->
  SnapTran
    (MkD s x o)
    (MkD s (updf x i (PWait v)) o)
| SnapReturn v vi s (x : Name T -> RRet' T A A) o :
  x i = PRetn v vi ->
  SnapTran
    (MkD s x o)
    (MkD s (updf x i PIdle) o)
| SnapNoOp d :
  SnapTran d d
| SnapFail s v x o :
  x i = PWait v ->
  SnapTran
    (MkD s x o)
    (MkD s (updf x i (PRetn v None)) o)
| SnapWrite v s x o :
  s i = MkReg None false ->
  x i = PWait v ->
  SnapTran
    (MkD s x o)
    (MkD
      (updf s i (MkReg (Some v) true))
      (updf x i (PRetn v (Some (insert v (collect s)))))
      (app o (cons (i, i, v) nil))).
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
      ∃' d',
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


Ltac specf H y := apply equal_f with (x:=y) in H.
Ltac gendep H := generalize dependent H.

Ltac case_match :=
  match goal with
  | |- context[classicT ?P] => destruct (classicT P)
  end.

Ltac dstr_rposs :=
  repeat match goal with
  | x : option _ |- _ => destruct x
  | x : prod _ _ |- _ => destruct x
  end.

Lemma In_app {A} :
  ∀ (x : A) ys zs,
    In x (ys ++ zs) ->
    In x ys \/ In x zs.
Proof.
  intros x ys.
  induction ys; simpl.
  { tauto. }
  {
    intros.
    destruct H.
    { subst. now do 2 left. }
    {
      apply IHys in H.
      destruct H.
      { left. now right. }
      { now right. }
    }
  }
Qed.

Lemma In_app_rev {A} :
  ∀ (x : A) ys zs,
    In x ys \/ In x zs ->
    In x (ys ++ zs).
Proof.
  intros.
  destruct H.
  {
    induction ys; simpl in *;
    try easy; destruct H.
    { subst. now left. }
    { right. now apply IHys. }
  }
  {
    induction ys; simpl;
    try easy; now right.
  }
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
    2: constructor.
    now exists i.
  }
  { easy. }
Qed.

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

Lemma iff_and :
  ∀ PL QL PR QR,
    PL <-> QL ->
    PR <-> QR ->
    (PL /\ PR) <-> (QL /\ QR).
Proof.
  intros.
  tauto.
Qed.

Lemma eq_iff :
  ∀ P Q,
    P = Q ->
    P <-> Q.
Proof.
  intros.
  now rewrite H.
Qed.

Lemma iff_str :
  ∀ P Q R,
    (P /\ R) <-> (Q /\ R) ->
    R -> (P <-> Q).
Proof. tauto. Qed.

Lemma PS_refl {T A} :
  ∀ (d : pdata T A) s ρs i,
    Inv d s ρs ->
    PossDef d.(wrt_ordn) d.(und_vals) (d.(rets_map) i) (d.(rets_map) i).
Proof.
  intros. destruct H.
  remember (rets_map d i).
  unfold RRet' in r. dstr_rposs;
  try constructor.
  {
    eapply ob_write0.
    symmetry. exact Heqr.
  }
  { easy. }
  {
    eapply vi_subs0.
    symmetry. exact Heqr.
  }
Qed.

Lemma forget_othr {T A} :
  ∀ i (d d' : pdata T A),
    OtherSnapTrans i d d' ->
    SnapTrans d d'.
Proof.
  intros.
  induction H.
  { constructor. }
  {
    psimpl.
    econstructor.
    { exists x0. exact H1. }
    { easy. }
  }
Qed.

Lemma Inv_pres_self {T A} :
  ∀ (i : Name T) (d d' : pdata T A),
    OtherSnapTrans i d d' ->
    d.(rets_map) i = d'.(rets_map) i.
Proof.
  intros.
  induction H. easy.
  rewrite <- IHclos_refl_trans_1n.
  clear IHclos_refl_trans_1n H0.
  psimpl. destruct H0; psimpl;
  unfold updf; now try rewrite eqb_nid.
Qed.

Lemma Inv_pres_und {T A} :
  ∀ (i : Name T) (d d' : pdata T A),
    OtherSnapTrans i d d' ->
    d.(und_vals) i = d'.(und_vals) i.
Proof.
  intros.
  induction H. easy.
  rewrite <- IHclos_refl_trans_1n.
  clear IHclos_refl_trans_1n H0.
  psimpl. destruct H0; psimpl;
  unfold updf; now try rewrite eqb_nid.
Qed.

Lemma Inv_mono {T A} :
  ∀ (d d' : pdata T A),
    SnapTrans d d' ->
    ∀ i v,
      (d.(und_vals) i).(val) = Some v ->
      (d'.(und_vals) i).(val) = Some v.
Proof.
  intros.
  induction H. easy.
  apply IHclos_refl_trans_1n.
  clear IHclos_refl_trans_1n H1.
  psimpl. destruct H; psimpl; try easy.
  unfold updf. dec_eq_nats x0 i.
  { now rewrite H in H0. }
  { now rewrite eqb_nid. }
Qed.

Lemma Inv_mono'' {T A} :
  ∀ (d d' : pdata T A),
    SnapTrans d d' ->
    ∀ i v,
      (d.(und_vals) i).(val) = Some v ->
      d.(und_vals) i = d'.(und_vals) i.
Proof.
  intros.
  induction H. easy.
  assert (und_vals x i = und_vals y i).
  {
    clear IHclos_refl_trans_1n H1.
    psimpl. destruct H; psimpl; try easy.
    unfold updf. dec_eq_nats x0 i.
    { now rewrite H in H0. }
    { now rewrite eqb_nid. }
  }
  rewrite <-IHclos_refl_trans_1n.
  2: now rewrite <-H2.
  easy.
Qed.

Lemma Inv_mono' {T A} :
  ∀ j (d d' : pdata T A),
    OtherSnapTrans j d d' ->
    ∀ i v,
      (d.(und_vals) i).(val) = Some v ->
      (d'.(und_vals) i).(val) = Some v.
Proof.
  intros.
  assert (SnapTrans d d').
  {
    eapply forget_othr.
    exact H.
  }
  eapply Inv_mono.
  exact H1. easy.
Qed.

Lemma wrt_ordn_uniq {T A} :
  ∀ und ord1 ord2,
    @WrtDef T A und ord1 ->
    WrtDef und ord2 ->
    ord1 = ord2.
Proof.
  intros.
  generalize dependent ord2.
  induction H; intros.
  { now ddestruct H0. }
  {
    ddestruct H0.
    now apply IHWrtDef.
  }
  {
    ddestruct H0.
    f_equal. now apply IHWrtDef.
  }
Qed.

Lemma rets_map_uniq {T A} :
  ∀ (d : pdata T A) s ρs,
    Inv d s ρs ->
    ∀ ls,
      Inv (MkD d.(und_vals) ls d.(wrt_ordn)) s ρs ->
      d.(rets_map) = ls.
Proof.
  intros.
  assert (Hp := H).
  assert (H0p := H0).
  destruct H, H0, d. psimpl.
  rename rets_map0 into ls'.
  assert (
    (λ ρ, ∀ i, PossDef wrt_ordn0 und_vals0 (ls' i) (ρ i)) =
    (λ ρ, ∀ i, PossDef wrt_ordn0 und_vals0 (ls i) (ρ i))
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
  clear - H Hp H0p vi_subs0 vi_subs1.
  rewrite set_eq in H.
  assert (H' := H).
  specialize (H ls).
  specialize (H' ls').
  assert (∀ i, PossDef wrt_ordn0 und_vals0 (ls i) (ls i)).
  {
    intros.
    eapply PS_refl with (d:= MkD _ _ _).
    exact H0p.
  }
  assert (∀ i, PossDef wrt_ordn0 und_vals0 (ls' i) (ls' i)).
  {
    intros.
    eapply PS_refl with (d:= MkD _ _ _).
    exact Hp.
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
    { now apply H3. }
    { now apply H0. }
  }
  now subst.
Qed.

Lemma Inv_eqv {T A} :
  ∀ s ρs (d1 d2 : pdata T A),
    Inv d1 s ρs ->
    Inv d2 s ρs ->
    d1 = d2.
Proof.
  intros.
  destruct d1, d2.
  assert (und_vals0 = und_vals1).
  {
    destruct H, H0. psimpl.
    clear - und_def0 und_def1.
    extensionality i.
    specialize (und_def0 i).
    specialize (und_def1 i).
    rewrite und_def0 in und_def1.
    now ddestruct und_def1.
  }
  subst.
  assert (wrt_ordn0 = wrt_ordn1).
  {
    destruct H, H0. psimpl.
    clear - wrt_def0 wrt_def1.
    destruct s, s, RState. psimpl.
    eapply wrt_ordn_uniq.
    { exact wrt_def0. }
    { exact wrt_def1. }
  }
  subst.
  f_equal.
  eapply rets_map_uniq with
    (d:= MkD _ _ _).
  { exact H. }
  { exact H0. }
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
  assert (H1' := H1).
  exists (MkD und_vals0 (updf rets_map0 i (PWait v)) wrt_ordn0).
  destruct H1. psimpl.
  assert (rets_map0 i = PIdle).
  {
    specialize (H5 (conPoss und_vals0 rets_map0)).
    eassert _.
    {
      apply H5.
      exists rets_map0.
      split. 2: easy. intros.
      eapply PS_refl with (d:=MkD _ _ _).
      exact H1'.
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
    { now setoid_rewrite <-H3. }
    { now setoid_rewrite <-H3. }
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
    { now setoid_rewrite <-H3. }
    { easy. }
    {
      unfold updf. intros.
      dec_eq_nats i0 i.
      { psimpl. now rewrite eqb_id in H4. }
      { rewrite eqb_nid in H4; auto. }
    }
    { easy. }
    {
      unfold updf. intros.
      dec_eq_nats i0 i.
      { now rewrite eqb_id in H4. }
      {
        rewrite eqb_nid in H4; auto.
        eapply ob_write0. exact H4.
      }
    }
  }
Qed.

Lemma neg_som : ∀ A (P : A -> Prop), (¬(∃ x, P x)) -> ∀ x, ¬P x.
Proof.
  intros ?????.
  apply H. now exists x.
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
  assert (H1' := H1).
  exists (MkD und_vals0 (updf rets_map0 i PIdle) wrt_ordn0).
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
      eapply PS_refl with (d:=MkD _ _ _).
      exact H1'.
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
            { eapply ob_write0. exact H1. }
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
    { now setoid_rewrite <- H3. }
    { easy. }
    {
      unfold updf. intros.
      dec_eq_nats i0 i.
      { psimpl. now rewrite eqb_id in H4. }
      { rewrite eqb_nid in H4; auto. }
    }
    { easy. }
    {
      clear - ob_write0.
      unfold updf. intros.
      dec_eq_nats i0 i.
      { now rewrite eqb_id in H. }
      {
        rewrite eqb_nid in H; auto.
        eapply ob_write0. exact H.
      }
    }
  }
Qed.

Lemma return_none_step {T A} :
  ∀ (i : Name T) (v : A) (r : option (set A)),
    ReturnStep i (Guar i)
    (λ s ρs, ∃ d,
      Inv d s ρs /\
      r = None /\
      d.(rets_map) i = PRetn v None)
    (WriteSnap v) r
    (λ _ _ s ρs,
      ∃ d, Inv d s ρs).
Proof.
  unfold ReturnStep.
  intros. clear H0. psimpl.
  exists (λ σ,
    ρs σ /\
    Done i (WriteSnap v) None σ).
  split.
  {
    assert (H' := H).
    destruct H. psimpl.
    exists (conPoss x.(und_vals) x.(rets_map)).
    split.
    {
      exists x.(rets_map). split. 2: easy.
      intros. eapply PS_refl. exact H'.
    }
    {
      constructor; simpl;
      now rewrite H1.
    }
  }
  split.
  {
    intros. exists σ.
    split. easy. constructor.
  }
  split.
  {
    intros. psimpl.
    now destruct H2.
  }
  eassert _.
  2:{
    split.
    exists (MkD x.(und_vals) (updf x.(rets_map) i PIdle) x.(wrt_ordn)).
    exact X. intros ??.
    eapply Inv_eqv in H0.
    2: exact H. psimpl.
    destruct d. eexists. split.
    { eapply SnapReturn. exact H1. }
    { easy. }
  }
  {
    destruct H. psimpl.
    constructor; psimpl; auto.
    {
      set_ext y;
      unfold mapRetPoss;
      split; intros; do 2 psimpl.
      {
        assert (x1 i = PRetn v None).
        {
          specialize (H i).
          rewrite H1 in H.
          now ddestruct H.
        }
        exists (updf x1 i PIdle).
        split.
        {
          unfold updf.
          intros. dec_eq_nats i0 i.
          { rewrite eqb_id. constructor. }
          { rewrite eqb_nid; auto. }
        }
        {
          unfold conPoss.
          destruct y. psimpl.
          f_equal.
          {
            f_equal. unfold updf.
            extensionality j.
            dec_eq_nats j i.
            { now rewrite eqb_id, H9. }
            { now rewrite eqb_nid. }
          }
          {
            unfold updf.
            extensionality j.
            dec_eq_nats j i.
            { now rewrite eqb_id. }
            { now rewrite eqb_nid, H5. }
          }
          {
            unfold updf.
            extensionality j.
            dec_eq_nats j i.
            { now rewrite eqb_id. }
            { now rewrite eqb_nid, H6. }
          }
        }
      }
      {
        exists (conPoss x.(und_vals) (updf x0 i (PRetn v None))).
        split.
        {
          split.
          {
            exists (updf x0 i (PRetn v None)).
            split. 2: easy. intros. specialize (H i0).
            unfold updf in *. dec_eq_nats i0 i.
            { rewrite eqb_id, H1. constructor. }
            { rewrite eqb_nid in *; auto. }
          }
          {
            constructor; simpl;
            unfold updf; now rewrite eqb_id.
          }
        }
        assert (x0 i = PIdle).
        {
          specialize (H i).
          unfold updf in H.
          rewrite eqb_id in H.
          now ddestruct H.
        }
        simpl. unfold updf.
        rewrite H0, eqb_id.
        do 4 split;[easy|idtac].
        split.
        { intros ??. now rewrite eqb_nid. }
        split.
        { intros ??. now rewrite eqb_nid. }
        {
          f_equal.
          extensionality j.
          dec_eq_nats j i.
          { now rewrite H0, eqb_id. }
          { now rewrite eqb_nid. }
        }
      }
    }
    {
      unfold updf.
      intros. dec_eq_nats i0 i.
      { now rewrite eqb_id in H. }
      { rewrite eqb_nid in H; eauto. }
    }
    {
      unfold updf.
      intros. dec_eq_nats i0 i.
      { now rewrite eqb_id in H; psimpl. }
      { rewrite eqb_nid in H; eauto. }
    }
    {
      unfold updf.
      intros. dec_eq_nats i0 i.
      { now rewrite eqb_id in H. }
      { rewrite eqb_nid in H; eauto. }
    }
  }
Qed.

Lemma return_some_step {T A} :
  ∀ (i : Name T) (v : A) (r : option (set A)),
    ReturnStep i (Guar i)
    (λ s ρs, ∃ d,
      Inv d s ρs /\
      ∃ lb vi new,
        r = Some new /\
        d.(rets_map) i = PRetn v (Some lb) /\
        lb ⊆ vi /\
        PossDef d.(wrt_ordn) d.(und_vals) (PRetn v (Some vi)) (PRetn v (Some new)))
    (WriteSnap v) r
    (λ _ _ s ρs,
      ∃ d, Inv d s ρs).
Proof.
  unfold ReturnStep.
  intros. clear H0. psimpl.
  rename x0 into lb.
  rename x1 into vi.
  rename x2 into new.
  rename H2 into Hlb.
  rename H3 into H2.
  exists (λ σ,
    ρs σ /\
    Done i (WriteSnap v) (Some new) σ).
  split.
  {
    assert (H' := H).
    destruct H. psimpl.
    exists (conPoss x.(und_vals) (updf x.(rets_map) i (PRetn v (Some new)))).
    split.
    {
      exists (updf x.(rets_map) i (PRetn v (Some new))).
      split. 2: easy. intros. unfold updf.
      dec_eq_nats i0 i.
      {
        rewrite eqb_id, H1.
        clear - H2 Hlb.
        ddestruct H2.
        constructor; eauto.
      }
      {
        rewrite eqb_nid; eauto.
        eapply PS_refl. exact H'.
      }
    }
    {
      unfold updf.
      constructor; simpl;
      now rewrite eqb_id.
    }
  }
  split.
  {
    intros. exists σ.
    split. easy. constructor.
  }
  split.
  {
    intros. psimpl.
    now destruct H3.
  }
  eassert _.
  2:{
    split.
    exists (MkD x.(und_vals) (updf x.(rets_map) i PIdle) x.(wrt_ordn)).
    exact X. intros ??.
    eapply Inv_eqv in H0.
    2: exact H. psimpl.
    destruct d. eexists. split.
    { eapply SnapReturn. exact H1. }
    { easy. }
  }
  {
    destruct H. psimpl.
    constructor; psimpl; auto.
    {
      set_ext y;
      unfold mapRetPoss;
      split; intros; do 2 psimpl.
      {
        exists (updf x1 i PIdle).
        split.
        {
          unfold updf.
          intros. dec_eq_nats i0 i.
          { rewrite eqb_id. constructor. }
          { rewrite eqb_nid; auto. }
        }
        {
          assert (x1 i = PRetn v (Some new)).
          {
            clear - H5.
            destruct (x1 i). 2: easy.
            destruct p, o. 2: easy.
            destruct o. 2: easy.
            now ddestruct H5.
          }
          unfold conPoss.
          destruct y. psimpl.
          f_equal.
          {
            f_equal. unfold updf.
            extensionality j.
            dec_eq_nats j i.
            { now rewrite eqb_id, H10. }
            { now rewrite eqb_nid. }
          }
          {
            unfold updf.
            extensionality j.
            dec_eq_nats j i.
            { now rewrite eqb_id. }
            { now rewrite eqb_nid, H6. }
          }
          {
            unfold updf.
            extensionality j.
            dec_eq_nats j i.
            { now rewrite eqb_id. }
            { now rewrite eqb_nid, H7. }
          }
        }
      }
      {
        exists (conPoss x.(und_vals) (updf x0 i (PRetn v (Some new)))).
        split.
        {
          split.
          {
            exists (updf x0 i (PRetn v (Some new))).
            split. 2: easy. intros. specialize (H i0).
            unfold updf in *. dec_eq_nats i0 i.
            {
              rewrite eqb_id, H1 in *.
              clear - H2 Hlb. ddestruct H2.
              constructor; eauto.
            }
            { rewrite eqb_nid in *; auto. }
          }
          {
            constructor; simpl;
            unfold updf; now rewrite eqb_id.
          }
        }
        assert (x0 i = PIdle).
        {
          specialize (H i).
          unfold updf in H.
          rewrite eqb_id in H.
          now ddestruct H.
        }
        simpl. unfold updf.
        rewrite H0, eqb_id.
        do 4 split;[easy|idtac].
        split.
        { intros ??. now rewrite eqb_nid. }
        split.
        { intros ??. now rewrite eqb_nid. }
        {
          f_equal.
          extensionality j.
          dec_eq_nats j i.
          { now rewrite H0, eqb_id. }
          { now rewrite eqb_nid. }
        }
      }
    }
    {
      unfold updf.
      intros. dec_eq_nats i0 i.
      { now rewrite eqb_id in H. }
      { rewrite eqb_nid in H; eauto. }
    }
    {
      unfold updf.
      intros. dec_eq_nats i0 i.
      { now rewrite eqb_id in H; psimpl. }
      { rewrite eqb_nid in H; eauto. }
    }
    {
      unfold updf.
      intros. dec_eq_nats i0 i.
      { now rewrite eqb_id in H. }
      { rewrite eqb_nid in H; eauto. }
    }
  }
Qed.

Lemma return_step {T A} :
  ∀ (i : Name T) (v : A) (r : option (set A)),
    ReturnStep i (Guar i)
      (λ s ρs, ∃ d,
        Inv d s ρs /\
        ((
          r = None /\
          d.(rets_map) i = PRetn v None
        ) \/
        (
          ∃ lb vi new,
            r = Some new /\
            d.(rets_map) i = PRetn v (Some lb) /\
            lb ⊆ vi /\
            PossDef d.(wrt_ordn) d.(und_vals) (PRetn v (Some vi)) (PRetn v (Some new))
        )))
      (WriteSnap v) r
      (λ _ _ s ρs,
        ∃ d, Inv d s ρs).
Proof.
  intros i v r s ρs H H0.
  psimpl. destruct H1; psimpl.
  {
    eapply return_none_step.
    { now exists x. }
    { easy. }
  }
  {
    eapply return_some_step.
    {
      exists x.
      split. easy.
      now exists x0, x1, x2.
    }
    { easy. }
  }
Qed.

Arguments lemCall {T i E F VE VF R G A} Q S.

Lemma Inv_stable {T A} :
  ∀ i c,
    Stable (@Rely T A i) (λ s ρs,
      ∃ d,
        Inv d s ρs /\
        d.(rets_map) i = c).
Proof.
  unfold
    Stable, stablePrec,
    sub, subPrec.
  intros. psimpl.
  apply H0 in H. psimpl.
  exists x2. split. easy.
  symmetry. now apply Inv_pres_self.
Qed.

Lemma help {T} :
  ∀ (A B : set T) (v : T),
    A ⊆ insert v B ->
    ¬(v ∈ A) ->
    A ⊆ B.
Proof.
  intros.
  assert (H1' := H1).
  apply H in H1.
  destruct H1.
  { now subst. }
  { easy. }
Qed.

Lemma pr1_eq {A} {P : A -> Prop} :
  ∀ (x y : sig P),
    x = y ->
    `x = `y.
Proof.
  intros.
  destruct x, y.
  now ddestruct H.
Qed.

Lemma pr1_neq {A} {P : A -> Prop} :
  ∀ (x y : sig P),
    x ≠ y ->
    `x ≠ `y.
Proof.
  intros ????. apply H.
  destruct x, y. simpl in *.
  subst. repeat f_equal.
  apply proof_irrelevance.
Qed.

Lemma red_sub {A} :
  ∀ (vs us : set A) (v : A),
    ¬ v ∈ us ->
    vs ⊆ insert v us ->
    ¬ v ∈ vs ->
    vs ⊆ us.
Proof.
  intros.
  assert (H2' := H2).
  apply H0 in H2.
  destruct H2.
  { now subst. }
  { easy. }
Qed.

Inductive Lock {P : Prop} :=
| lock : P -> Lock.
Arguments Lock : clear implicits.

Lemma ins_lock {P} : P -> Lock P.
Proof. now constructor. Qed.

Ltac lock H := apply ins_lock in H.

Lemma out_lock {P} : Lock P -> P.
Proof. intros. now destruct H. Qed.

Ltac unlock H := apply out_lock in H.

Lemma wrt_def_snoc {T A} :
  ∀ und wrs i v,
    @WrtDef T A und wrs ->
    WrtDef
      (und ++ cons (i, existT _ _ (At i (Write (MkReg (Some v) true)), tt)) nil)
      (wrs ++ cons (i, i, v) nil).
Proof.
  intros.
  induction H; simpl;
  now repeat constructor.
Qed.

Lemma split_prefixes {A} :
  ∀ xs ys zs (x : A),
    xs ++ x :: nil = ys ++ zs ->
    (∃ zs', zs = zs' ++ x :: nil) \/
    ( zs = nil /\ ∃ ys', ys = ys' ++ x :: nil).
Proof.
  intros.
  generalize dependent ys.
  generalize dependent zs.
  induction xs;
  intros; simpl in *.
  {
    destruct ys;
    simpl in *; subst.
    { left. now exists nil. }
    {
      ddestruct H.
      assert (ys = nil)
        by now destruct ys.
      subst. psimpl.
      right. split. easy.
      now exists nil.
    }
  }
  {
    destruct ys;
    simpl in *; subst.
    { left. now exists (a :: xs). }
    {
      ddestruct H.
      apply IHxs in x.
      destruct x; psimpl.
      { left. now exists x. }
      {
        right. split. easy.
        now exists (a0 :: x).
      }
    }
  }
Qed.

Ltac adjust H P :=
  let H' := fresh in
  assert (H' : P);[
    idtac |
    clear H;
    rename H' into H
  ].

Lemma write_correct {T A} (i : Name T) (v : A) :
  VerifyProg i (Rely i) (Guar i)
    (λ _ _ s ρs,
      ∃ d,
        Inv d s ρs /\
        d.(rets_map) i = PWait v /\
        (d.(und_vals) i).(ran) = false)
    (call (At i (Write (MkReg (Some v) true))))
    (λ 'tt _ _ s ρs,
      ∃ d vi,
        Inv d s ρs /\
        (∀ i, vi i -> (d.(und_vals) i).(val) ≠ None) /\
        d.(rets_map) i = PRetn v (Some (λ v, ∃ i, vi i /\ (und_vals d i).(val) = Some v))).
Proof.
  eapply weakenPost.
  eapply lemCallWk with
    (Q:=λ s ρs,
      ∃ d,
        Inv d s ρs /\
        d.(rets_map) i = PWait v /\
        (d.(und_vals) i).(ran) = false /\
        (d.(und_vals) i).(val) = None)
    (S:=λ _ s ρs,
      ∃ d vi,
        Inv d s ρs /\
        (∀ i, vi i -> (d.(und_vals) i).(val) ≠ None) /\
        d.(rets_map) i = PRetn v (Some (λ v, ∃ i, vi i /\ (und_vals d i).(val) = Some v))).
  {
    unfold
      Stable, stablePrec,
      sub, subPrec.
    intros. psimpl.
    apply H0 in H. psimpl.
    exists x2. split. easy.
    assert (H' := H).
    apply Inv_pres_self in H.
    apply Inv_pres_und in H'.
    split. congruence.
    split; congruence.
  }
  {
    unfold
      Stable, stablePrec,
      sub, subPrec.
    intros. psimpl.
    apply H0 in H. psimpl.
    exists x3, x2.
    split. easy.
    assert (H' := H).
    apply Inv_pres_self in H.
    assert (∀ i, x2 i -> (und_vals x3 i).(val) = (und_vals x1 i).(val)).
    {
      intros. apply H1 in H4.
      remember (und_vals x1 i0).
      destruct r, val0; try easy. simpl in *.
      eapply forget_othr, one_shot in H'.
      2: now rewrite <-Heqr.
      now rewrite <-H', <-Heqr.
    }
    split.
    {
      intros.
      eassert _.
      { apply H4 in H5. exact H5. }
      apply H1 in H5.
      now rewrite X.
    }
    {
      assert (
        (λ v, ∃ i, x2 i /\ val (und_vals x1 i) = Some v) =
        (λ v, ∃ i, x2 i /\ val (und_vals x3 i) = Some v)
      ).
      {
        set_ext y.
        split; intros; psimpl.
        exists x4. split. easy.
        apply H4 in H5. congruence.
        exists x4. split. easy.
        apply H4 in H5. congruence.
      }
      now rewrite <-H5, <-H.
    }
  }
  {
    unfold Commit.
    intros. do 2 psimpl.
    exists ρs.
    split.
    {
      clear - H. destruct H. psimpl.
      exists (conPoss x1.(und_vals) x1.(rets_map)), x1.(rets_map).
      split. 2: easy. intros.
      eapply PS_refl with (d:= MkD _ _ _).
      now constructor.
    }
    split.
    {
      intros. exists σ.
      split. easy. constructor.
    }
    assert (Inv x1 t ρs).
    {
      destruct H. psimpl.
      ddestruct H2. psimpl.
      ddestruct H. psimpl.
      ddestruct H7.
      2:{
        unfold RegCond in H2. psimpl.
        destruct m1. 2: easy.
        exfalso. apply (resp_own0 i).
        exists i0, x5. split. easy.
        rewrite <-x3, <-x2 at 1. simpl.
        now left.
      }
      constructor.
      {
        intros.
        rewrite <-und_def0.
        dec_eq_nats i0 i.
        { now rewrite <-x3, <-x4, <-x2, <-x at 1. }
        { now rewrite <-x3, <-x4, H6 at 1. }
      }
      {
        rewrite <-x4 at 1.
        rewrite <-x3 in wrt_def0.
        easy.
      }
      { easy. }
      { easy. }
      {
        intros.
        dec_eq_nats i0 i.
        {
          setoid_rewrite <-x4.
          setoid_rewrite <-x.
          intros ?. psimpl.
          destruct H10.
          now ddestruct H10.
          easy.
        }
        {
          setoid_rewrite <-x4 at 1.
          rewrite <-x3 in resp_own0.
          now setoid_rewrite H6.
        }
      }
      { easy. }
      { easy. }
      { easy. }
      { easy. }
    }
    split.
    {
      exists x1.
      split. easy.
      split. easy.
      split. easy.
      destruct H.
      now apply resp_write0.
    }
    {
      intros ??.
      eapply Inv_eqv in H10.
      2: exact H. psimpl.
      exists d. split.
      constructor. easy.
    }
  }
  intros [].
  {
    unfold Commit.
    intros. do 2 psimpl.
    ddestruct H2. psimpl.
    ddestruct H2. psimpl.
    ddestruct H9; psimpl.
    2:{
      destruct H.
      clear - und_def0 x x2 x3 x4. exfalso.
      psimpl. specialize (und_def0 i).
      now rewrite <-x3, <-x2 in und_def0 at 1.
    }
    2:{
      destruct H.
      clear - und_def0 x x2 x3 x4. exfalso.
      psimpl. specialize (und_def0 i).
      now rewrite <-x3, <-x2 in und_def0 at 1.
    }
    ddestruct H6.
    assert (H' := H).
    destruct x1, H. psimpl.
    clear H11 H10 H9 H7 H2 H1.
    pose (und_vals1 :=
      updf und_vals0 i (MkReg (Some v) true)).
    pose (rets_map1 :=
      updf rets_map0 i (PRetn v (Some (insert v (collect und_vals0))))).
    pose (wrt_ordn1 :=
      app wrt_ordn0 (cons (i, i, v) nil)).
    assert (Heq : collect und_vals1 = insert v (collect und_vals0)).
    {
      subst und_vals1.
      unfold updf. set_ext v0.
      split; intros; psimpl.
      {
        dec_eq_nats x1 i.
        {
          rewrite eqb_id in H.
          ddestruct H. now left.
        }
        {
          rewrite eqb_nid in H; auto.
          right. now exists x1.
        }
      }
      {
        destruct H; psimpl.
        { exists i. now rewrite eqb_id. }
        {
          dec_eq_nats x1 i.
          { now rewrite H5 in H. }
          exists x1. now rewrite eqb_nid.
        }
      }
    }
    assert ( IH : 
      Inv
        (MkD und_vals1 rets_map1 wrt_ordn1)
        t
        (λ σ,
          ∃ dσ,
          (∀ i0, PossDef wrt_ordn1 und_vals1 (rets_map1 i0) (dσ i0)) /\
          σ = conPoss und_vals1 dσ) /\
        rets_map1 i = PRetn v (Some (insert v (collect und_vals0))) /\
        (∀ i0, val (und_vals1 i0) ≠ None → val (und_vals1 i0) ≠ None) /\
        rets_map1 i = PRetn v (Some (λ v0, ∃ i0, val (und_vals1 i0) ≠ None ∧ val (und_vals1 i0) = Some v0))
    ).
    {
      split.
      {
        subst rets_map1 und_vals1.
        constructor; simpl.
        {
          intros. unfold updf in *.
          specialize (und_def0 i0).
          dec_eq_nats i0 i.
          { now rewrite eqb_id, <-x4, <-x at 1. }
          { rewrite eqb_nid, <-x4, <-und_def0, H8, <-x3 at 1; auto. }
        }
        {
          subst wrt_ordn1.
          rewrite <-x4 at 1.
          simpl. apply wrt_def_snoc.
          clear - wrt_def0 x3.
          now rewrite <-x3 in wrt_def0.
        }
        { easy. }
        {
          unfold updf. intros.
          dec_eq_nats i0 i.
          {
            rewrite eqb_id in H.
            ddestruct H.
            destruct H1.
            {
              subst. exists i.
              now rewrite eqb_id.
            }
            {
              psimpl.
              dec_eq_nats x1 i.
              { now rewrite H5 in H. }
              exists x1. now rewrite eqb_nid.
            }
          }
          {
            rewrite eqb_nid in H; auto.
            eapply vi_subs0 in H1. 2: exact H.
            destruct H1. dec_eq_nats x1 i.
            { now rewrite H5 in H1. }
            exists x1. now rewrite eqb_nid.
          }
        }
        {
          intros ??. psimpl.
          dec_eq_nats i0 i.
          { now rewrite <-x4, <-x in H1 at 1. }
          {
            eapply resp_own0.
            exists x1, x5. split. exact H.
            rewrite <-x3 at 1. simpl in *.
            rewrite <-x4 in H1 at 1.
            now rewrite <-H8.
          }
        }
        {
          simpl. unfold updf.
          intros. dec_eq_nats i0 i.
          { now rewrite eqb_id in H. }
          { rewrite eqb_nid in *; auto. }
        }
        {
          unfold updf.
          intros ??. psimpl.
          dec_eq_nats i0 i.
          { now rewrite eqb_id in *. }
          {
            rewrite eqb_nid in *; auto.
            eapply resp_ran0.
            now exists x1, x5.
          }
        }
        {
          unfold updf.
          subst wrt_ordn1.
          split; intros.
          {
            rename i0 into i'.
            apply In_app in H. destruct H.
            {
              apply ordn_val0 in H.
              {
                dec_eq_nats i' i.
                { now rewrite H5 in H. }
                { now rewrite eqb_nid. }
              }
            }
            {
              destruct H. 2: easy.
              ddestruct H.
              now rewrite eqb_id.
            }
          }
          {
            dec_eq_nats i0 i.
            {
              rewrite eqb_id in H. ddestruct H.
              apply In_app_rev. right. now left.
            }
            {
              rewrite eqb_nid in H; auto.
              apply In_app_rev. left.
              now apply ordn_val0.
            }
          }
        }
        {
          unfold updf. subst wrt_ordn1.
          intros. dec_eq_nats i0 i.
          {
            rewrite eqb_id in H.
            ddestruct H.
            apply Build_ObWr with
              (pfx:=wrt_ordn0 ++ (i, i, v0) :: nil).
            {
              set_ext v. split.
              intros. psimpl.
              {
                destruct H; psimpl.
                {
                  exists i.
                  apply In_app_rev.
                  right. now left.
                }
                {
                  apply ordn_val0 in H.
                  exists x1. apply In_app_rev.
                  now left.
                }
              }
              {
                intros. destruct H.
                apply In_app in H.
                destruct H.
                {
                  right.
                  apply ordn_val0 in H.
                  now exists x1.
                }
                {
                  psimpl.
                  destruct H;
                  ddestruct H.
                  now left.
                }
              }
            }
            {
              exists nil.
              now rewrite app_nil_r.
            }
          }
          {
            rewrite eqb_nid in H; auto.
            assert (H'' := H).
            apply ob_write0 in H.
            destruct H. subst.
            apply Build_ObWr with
              (pfx:=pfx).
            { easy. }
            { now apply prefix_cons. }
          }
        }
      }
      split.
      {
        subst rets_map1. unfold updf.
        now rewrite eqb_id.
      }
      split.
      { easy. }
      {
        subst rets_map1 und_vals1.
        unfold updf. rewrite eqb_id.
        repeat f_equal. set_ext z.
        split; intros; psimpl.
        {
          destruct H; psimpl.
          { exists i. now rewrite eqb_id. }
          {
            exists x1.
            dec_eq_nats x1 i.
            { now rewrite H5 in H. }
            { now rewrite eqb_nid, H. }
          }
        }
        {
          dec_eq_nats x1 i.
          {
            rewrite eqb_id in *.
            simpl in *. ddestruct H1.
            now left.
          }
          {
            rewrite eqb_nid in *; auto.
            right. now exists x1.
          }
        }
      }
    }
    decide_prop (v ∈ collect und_vals0);
    rename H into v_nin.
    {
      exists (λ σ,
        ∃ dσ,
          (∀ i, PossDef wrt_ordn1 und_vals1 (rets_map1 i) (dσ i)) /\
          σ = conPoss und_vals1 dσ).
      split.
      {
        exists (conPoss und_vals1 rets_map1), rets_map1.
        split. 2: easy. intros.
        eapply PS_refl with (d:= MkD _ _ _).
        psimpl. exact i1.
      }
      split.
      {
        intros. psimpl.
        exists (conPoss und_vals0 (updf x1 i (PWait v))).
        split.
        {
          eexists.
          split. 2: easy.
          unfold updf. intros.
          dec_eq_nats i0 i.
          {
            rewrite eqb_id, H3.
            constructor.
          }
          {
            subst rets_map1. unfold updf in H. specialize (H i0).
            rewrite eqb_nid in *; auto. ddestruct H;
            rewrite <-x6, <-x at 1; try constructor.
            {
              ddestruct H. subst.
              destruct pfx_prefix.
              assert (H'' := H).
              apply split_prefixes in H.
              destruct H; psimpl.
              {
                rewrite app_assoc in H''.
                apply app_inj_tail in H''.
                psimpl. clear H12.
                apply Build_ObWr with
                  (pfx:=pfx).
                { easy. }
                { now apply prefix_cons, prefix_refl. }
              }
              {
                rewrite app_nil_r in H''.
                apply app_inj_tail in H''.
                psimpl. clear H12.
                apply Build_ObWr with
                  (pfx:= x8).
                {
                  set_ext v1. split.
                  intros; psimpl.
                  {
                    apply In_app in H.
                    destruct H.
                    { now exists x7. }
                    {
                      psimpl.
                      destruct H; ddestruct H.
                      destruct v_nin.
                      apply ordn_val0 in H.
                      now exists x9.
                    }
                  }
                  {
                    intros. psimpl. exists x7.
                    apply In_app_rev; auto.
                  }
                }
                { apply prefix_refl. }
              }
            }
            { easy. }
            {
              intros. subst und_vals1.
              apply H10 in H12.
              rewrite Heq in H12 at 1.
              now (destruct H12; subst).
            }
          }
        }
        {
          eapply PossStepsStep with
            (i:=i)
            (σ:= conPoss und_vals1 (updf x1 i (PCall v))).
          {
            eapply PCommitCall with
              (m:= WriteSnap v).
            {
              simpl. rewrite Heq.
              apply SnapCallPass.
              { easy. }
              { subst und_vals1. unfold updf. now rewrite eqb_id. }
              { intros ??. subst und_vals1. unfold updf. now rewrite eqb_nid. }
              { unfold updf. now rewrite eqb_id. }
              {
                subst rets_map1. simpl in *.
                specialize (H i). unfold updf in *.
                now rewrite eqb_id in *.
              }
              { intros ??. subst und_vals1. unfold updf. now rewrite eqb_nid. }
            }
            { simpl. unfold updf. now rewrite eqb_id. }
            {
              subst rets_map1. unfold updf in *.
              specialize (H i). rewrite eqb_id in H.
              simpl. now rewrite eqb_id.
            }
            { simpl. unfold updf. now rewrite eqb_id. }
            {
              subst rets_map1. unfold updf in *.
              specialize (H i). rewrite eqb_id in H.
              ddestruct H; simpl; rewrite <-x;
              try (easy || case_match);
              now rewrite eqb_id.
            }
          }
          { subst rets_map1. unfold updf. intros. simpl. now rewrite eqb_nid. }
          { subst rets_map1. unfold updf. intros. simpl. now rewrite eqb_nid. }
          specialize (H i). subst rets_map1.
          unfold updf in H. rewrite eqb_id in H.
          ddestruct H.
          {
            eapply PossStepsStep with
              (i:=i)
              (σ:= conPoss und_vals1 (updf x1 i (PRetn v (Some (collect und_vals1))))).
            {
              eapply PCommitRet with
                (m:= WriteSnap v)
                (v:= Some (collect und_vals1)).
              {
                simpl.
                apply SnapRetPass.
                { subst und_vals1. unfold updf. now rewrite eqb_id. }
                { unfold updf. now rewrite eqb_id. }
                { unfold updf. now rewrite eqb_id. }
                { intros ??. subst und_vals1. unfold updf. now rewrite eqb_nid. }
              }
              { simpl. unfold updf. now rewrite eqb_id. }
              { simpl. unfold updf. now rewrite eqb_id. }
              { simpl. unfold updf. now rewrite eqb_id. }
              { simpl. unfold updf. now rewrite eqb_id. }
            }
            { unfold updf. intros. simpl. now rewrite eqb_nid. }
            { unfold updf. intros. simpl. now rewrite eqb_nid. }
            assert (vs = collect und_vals1).
            {
              set_ext z.
              split; intros.
              { now apply H10. }
              { apply H9. now rewrite <-Heq at 1. }
            }
            subst.
            assert (updf x1 i (PRetn v (Some (collect und_vals1))) = x1).
            {
              extensionality j.
              unfold updf. dec_eq_nats j i.
              { now rewrite eqb_id. }
              { now rewrite eqb_nid. }
            }
            rewrite H11.
            subst und_vals1.
            constructor.
          }
          {
            assert (updf x1 i (PCall v) = x1).
            {
              extensionality j.
              unfold updf. dec_eq_nats j i.
              { now rewrite eqb_id. }
              { now rewrite eqb_nid. }
            }
            rewrite H.
            constructor.
          }
        }
      }
      split.
      {
        psimpl.
        eexists _, _.
        split. exact H.
        psimpl.
        split. exact H2.
        easy.
      }
      {
        psimpl.
        intros ??.
        eapply Inv_eqv in H7.
        2: exact H'. psimpl.
        eexists. split. 2: exact H.
        subst wrt_ordn1 rets_map1 und_vals1.
        apply SnapWrite.
        { destruct (und_vals0 i). now psimpl. }
        { easy. }
      }
    }
    exists (λ σ,
      ∃ dσ,
        (∀ i0, PossDef wrt_ordn1 und_vals1 (rets_map1 i0) (dσ i0)) /\
        σ = conPoss und_vals1 dσ).
    split.
    {
      psimpl. eexists _, _.
      split. 2: easy. intros.
      eapply PS_refl with (d:= MkD _ _ _).
      exact H.
    }
    split.
    {
      lock IH.
      intros. psimpl.
      rename x1 into σ.
      cut (
        ∃ ρ,
          (∀ i0, PossDef wrt_ordn0 und_vals0 (rets_map0 i0) (ρ i0)) /\
          PossSteps (conPoss und_vals0 ρ) (conPoss und_vals1 σ)
      ).
      {
        intros. psimpl.
        eexists. split. 2: exact H2.
        eexists. split. 2: easy.
        easy.
      }
      pose (rp j :=
        match σ j with
        | PRetn w (Some ws) => 
          if classicT (PossDef wrt_ordn0 und_vals0 (rets_map0 j) (PRetn w (Some ws))) then
            PRetn w (Some ws)
          else
            PCall w : RRet T A
        | r => r
        end).
      exists (updf rp i (Some (v, None))).
      split.
      {
        intros. specialize (H i0).
        subst rp rets_map1. simpl.
        unfold updf in H. unfold updf.
        dec_eq_nats i0 i.
        {
          rewrite eqb_id, H3.
          constructor.
        }
        {
          rewrite eqb_nid in *; auto.
          ddestruct H; rewrite <-x5, <-x;
          try now constructor.
          case_match. easy.
          constructor.
        }
      }
      {
        eapply PossStepsStep with
          (i:=i)
          (σ:= conPoss und_vals1 rp).
        {
          eapply PCommitCall with
            (m:= WriteSnap v).
          {
            simpl. rewrite Heq.
            apply SnapCallPass.
            { easy. }
            { subst und_vals1. unfold updf. now rewrite eqb_id. }
            { intros ??. subst und_vals1. unfold updf. now rewrite eqb_nid. }
            { subst rp. unfold updf. now rewrite eqb_id. }
            {
              subst rp rets_map1. simpl in *.
              specialize (H i). unfold updf in H.
              rewrite eqb_id in H. ddestruct H;
              rewrite <-x; try case_match; try easy.
              now rewrite H3 in p.
            }
            { intros ??. subst und_vals1. unfold updf. now rewrite eqb_nid. }
          }
          { simpl. subst rp. unfold updf. now rewrite eqb_id. }
          {
            subst rp rets_map1. unfold updf in *.
            specialize (H i). rewrite eqb_id in H.
            ddestruct H; simpl; rewrite <-x;
            now (easy || case_match).
          }
          { simpl. subst rp. unfold updf. now rewrite eqb_id. }
          {
            subst rp rets_map1. unfold updf in *.
            specialize (H i). rewrite eqb_id in H.
            ddestruct H; simpl; rewrite <-x;
            try (easy || case_match).
            now rewrite H3 in p. easy.
          }
        }
        { subst rets_map1. unfold updf. intros. simpl. now rewrite eqb_nid. }
        { subst rets_map1. unfold updf. intros. simpl. now rewrite eqb_nid. }
        pose (rp' n j :=
          match σ j with
          | PRetn w (Some ws) =>
            if classicT (`j < n) then
              if classicT (PossDef wrt_ordn0 und_vals0 (rets_map0 j) (PRetn w (Some ws))) then
                PRetn w (Some ws)
              else
                PCall w : RRet T A
            else
              PRetn w (Some ws)
          | r => r
          end).
        assert (rp = rp' T).
        {
          clear. subst rp rp'.
          extensionality j. gendep (σ j).
          unfold RRet'. intro. dstr_rposs;
          try easy; repeat case_match;
          try easy. destruct j. psimpl. lia.
        }
        assert (rp' 0 = σ).
        {
          clear. subst rp'.
          extensionality j. gendep (σ j).
          unfold RRet'. intro. dstr_rposs;
          try easy; now case_match.
        }
        rewrite H1. clear H1 rp.
        cut (
          ∀ n,
            (∀ m, n = S m -> m < T) ->
            PossSteps
              (conPoss und_vals1 (rp' n))
              (conPoss und_vals1 σ)
        ).
        {
          intros. apply H1.
          intros. rewrite H6.
          lia.
        }
        intros.
        induction n.
        {
          rewrite H2.
          constructor.
        }
        {
          assert (n < T)
            by now apply H1.
          pose (nt := exist (λ i, i < T) n H6).
          remember (σ nt). unfold RRet' in r.
          dstr_rposs.
          {
            decide_prop (PossDef wrt_ordn0 und_vals0 (rets_map0 nt) (PRetn a (Some s1))).
            {
              assert (rp' (S n) = rp' n).
              {
                subst rp'. simpl.
                extensionality j.
                dec_eq_nats nt j.
                {
                  rewrite <-Heqr.
                  repeat case_match;
                  try easy; try lia.
                }
                {
                  gendep (σ j). unfold RRet'.
                  intros. dstr_rposs; try easy;
                  repeat case_match; try (easy||lia).
                  apply pr1_neq in H9. subst nt.
                  destruct j. simpl in *. lia.
                }
              }
              rewrite H9. apply IHn.
              intros. lia.
            }
            {
              decide_prop (v ∈ s1).
              {
                rename H9 into v_in.
                specialize (H nt).
                rewrite <-Heqr in H.
                ddestruct H.
                assert (s1 = insert v (collect und_vals0)).
                {
                  set_ext z.
                  split; intros.
                  {
                    clear - Heq H2 H11.
                    subst und_vals1. apply H2 in H11.
                    now rewrite Heq in H11 at 1.
                  }
                  {
                    clear H7 IHn IH.
                    destruct H11.
                    { now subst. }
                    {
                      destruct H, pfx_prefix. psimpl.
                      assert (H'' := H).
                      apply split_prefixes in H.
                      destruct H; psimpl.
                      {
                        rewrite app_assoc in H''.
                        apply app_inj_tail in H''.
                        psimpl. clear H11. subst rets_map1.
                        unfold updf in x. dec_eq_nats nt i.
                        {
                          rewrite eqb_id in x.
                          symmetry in x. ddestruct x.
                          apply H1. right. now exists x6.
                        }
                        {
                          rewrite eqb_nid in x; auto.
                          exfalso. destruct v_in.
                          apply v_nin. exists x5.
                          apply ordn_val0, In_app_rev; auto.
                        }
                      }
                      {
                        rewrite app_nil_r in H''.
                        apply app_inj_tail in H''.
                        psimpl. clear H11.
                        apply ordn_val0 in H7.
                        exists x6. apply In_app_rev; auto.
                      }
                    }
                  }
                }
                subst.
                eapply PossStepsStep
                  with (i:=nt).
                4:{
                  apply IHn.
                  intros. subst.
                  lia.
                }
                2:{
                  simpl. intros.
                  dec_eq_nats nt j.
                  {
                    rewrite <-Heqr.
                    now repeat case_match.
                  }
                  {
                    gendep (σ j). unfold RRet'.
                    intros. dstr_rposs;
                    now repeat case_match.
                  }
                }
                2:{
                  simpl. intros.
                  repeat case_match; try (easy || lia).
                  destruct j. simpl in *. rename x5 into j.
                  assert (j = n) by lia. subst. subst nt.
                  exfalso. apply H11. repeat f_equal.
                  apply proof_irrelevance.
                }
                {
                  eapply PCommitRet with
                    (m:= WriteSnap a)
                    (v:= Some (collect und_vals1)).
                  {
                    simpl.
                    eapply SnapRetPass.
                    {
                      subst rets_map1. unfold updf in *.
                      dec_eq_nats nt i.
                      { now rewrite eqb_id. }
                      {
                        assert (i ≠ nt) by easy.
                        rewrite eqb_nid; auto.
                        rewrite eqb_nid in x; auto.
                        apply resp_ran0. repeat eexists.
                        now rewrite x at 1.
                      }
                    }
                    {
                      rewrite <-Heqr. repeat case_match;
                      try easy. subst nt. simpl in *. try lia.
                    }
                    {
                      rewrite <-Heqr. repeat case_match;
                      try easy. subst nt. simpl in *. lia.
                    }
                    {
                      intros ??.
                      assert (`j ≠ `nt) by now apply pr1_neq.
                      repeat case_match; try easy; destruct j;
                      subst nt; simpl in *; lia.
                    }
                  }
                  { simpl. rewrite <-Heqr. now repeat case_match. }
                  { simpl. rewrite <-Heqr. now repeat case_match. }
                  {
                    simpl. rewrite <-Heqr.
                    repeat case_match; easy || lia.
                  }
                  {
                    simpl. rewrite <-Heqr, Heq.
                    repeat case_match; easy || lia.
                  }
                }
              }
              {
                clear H2 IH IHn. subst rp'.
                specialize (H nt).  subst rets_map1.
                unfold updf in H.
                assert (i ≠ nt).
                {
                  intros ?. subst.
                  rewrite eqb_id, <-Heqr in H.
                  ddestruct H. apply H10, H0. now left.
                }
                rewrite eqb_nid in H; auto. exfalso.
                apply H7. ddestruct H; rewrite <-x in *;
                try easy. rewrite <-x5 at 1. ddestruct Heqr.
                constructor.
                {
                  destruct H, pfx_prefix. psimpl.
                  assert (H'' := H).
                  apply split_prefixes in H.
                  destruct H; psimpl.
                  {
                    rewrite app_assoc in H''.
                    apply app_inj_tail in H''.
                    psimpl. clear H11.
                    apply Build_ObWr with
                      (pfx:=pfx).
                    { easy. }
                    { now apply prefix_cons, prefix_refl. }
                  }
                  {
                    exfalso. apply H10. exists i.
                    apply In_app_rev. right. now left.
                  }
                }
                { easy. }
                {
                  subst und_vals1. intros.
                  assert (H12' := H12). apply H2 in H12.
                  rewrite Heq in H12 at 1. destruct H12.
                  { now subst. }
                  { easy. } 
                }
              }
            }
          }
          {
            assert (rp' (S n) = rp' n).
            {
              clear - Heqr. subst rp'.
              simpl. extensionality j.
              dec_eq_nats nt j.
              { now rewrite <-Heqr. }
              {
                gendep (σ j). unfold RRet'.
                intros. dstr_rposs; try easy;
                repeat case_match; try easy;
                apply pr1_neq in H; subst nt;
                destruct j; psimpl; lia.
              }
            }
            rewrite H7. apply IHn.
            intros. lia.
          }
          {
            assert (rp' (S n) = rp' n).
            {
              clear - Heqr. subst rp'.
              simpl. extensionality j.
              dec_eq_nats nt j.
              { now rewrite <-Heqr. }
              {
                gendep (σ j). unfold RRet'.
                intros. dstr_rposs; try easy;
                repeat case_match; try easy;
                apply pr1_neq in H; subst nt;
                destruct j; psimpl; lia.
              }
            }
            rewrite H7. apply IHn.
            intros. lia.
          }
          {
            assert (rp' (S n) = rp' n).
            {
              clear - Heqr. subst rp'.
              simpl. extensionality j.
              dec_eq_nats nt j.
              { now rewrite <-Heqr. }
              {
                gendep (σ j). unfold RRet'.
                intros. dstr_rposs; try easy;
                repeat case_match; try easy;
                apply pr1_neq in H; subst nt;
                destruct j; psimpl; lia.
              }
            }
            rewrite H7. apply IHn.
            intros. lia.
          }
          {
            assert (rp' (S n) = rp' n).
            {
              clear - Heqr. subst rp'.
              simpl. extensionality j.
              dec_eq_nats nt j.
              { now rewrite <-Heqr. }
              {
                gendep (σ j). unfold RRet'.
                intros. dstr_rposs; try easy;
                repeat case_match; try easy;
                apply pr1_neq in H; subst nt;
                destruct j; psimpl; lia.
              }
            }
            rewrite H7. apply IHn.
            intros. lia.
          }
        }
      }
    }
    split.
    {
      now exists
        (MkD und_vals1 rets_map1 wrt_ordn1),
        (λ i, val (und_vals1 i) ≠ None).
    }
    {
      intros ??.
      eapply Inv_eqv in H.
      2: exact H'. psimpl.
      eexists. split.
      {
        eapply SnapWrite.
        {
          destruct (und_vals0 i).
          simpl in *. now subst.
        }
        { exact H3. }
      }
      { easy. }
    }
  }
  { now intros []. }
Qed.

Lemma wrt_ordn_read {T A} :
  ∀ ord wrt i n v,
    @WrtDef T A ord wrt ->
    WrtDef (ord ++ cons (i, existT _ _ (At n Read, v)) nil) wrt.
Proof.
  intros.
  induction H; simpl;
  now repeat constructor.
Qed.

Inductive WrtPfxRes {T A} {c : nat} :
  list (Name T * {R & prod (ArraySig (RegSig (reg_st A)) T R) R}) ->
  OWr T A ->
  OWr T A ->
  Prop :=
| WDREnd os :
  WrtPfxRes os nil nil
| WDRSkipR i n v os wr wrp :
  WrtPfxRes os wr wrp ->
  WrtPfxRes ((i, existT _ _ (At n Read, v)) :: os) wr wrp
| WDRKeep (i : Name T) (v : A) os (wr wrp : OWr T A) :
  `i ≥ c ->
  WrtPfxRes os wr wrp ->
  WrtPfxRes ((i, existT _ _ (At i (Write (MkReg (Some v) true)), tt)) :: os) ((i, i, v) :: wr) ((i, i, v) :: wrp)
| WDRSkipW (i : Name T) (v : A) os (wr wrp : OWr T A) :
  `i < c ->
  WrtPfxRes os wr wrp ->
  WrtPfxRes ((i, existT _ _ (At i (Write (MkReg (Some v) true)), tt)) :: os) ((i, i, v) :: wr) wrp.
Arguments WrtPfxRes {T A} c.

Lemma wrt_res_ordn_read {T A} :
  ∀ c ord wrt wrt' i n v,
    @WrtPfxRes T A c ord wrt wrt' ->
    WrtPfxRes c (ord ++ cons (i, existT _ _ (At n Read, v)) nil) wrt wrt'.
Proof.
  intros.
  induction H; simpl;
  now repeat constructor.
Qed.

(* Lemma wdr_unres {T A} :
  ∀ und ord,
    @WrtDefRes T A 0 und ord <-> WrtDef und ord.
Proof.
  split; intros; induction H;
  try constructor; intuition lia.
Qed.

Lemma wdr_all_res {T A} :
  ∀ und,
    (∀ i n r,
      List.In (i, existT _ _ (At n (Write r), tt)) und ->
      ∃ v, r = MkReg (Some v) true) ->
    @WrtDefRes T A T und nil.
Proof.
  intros.
  induction und.
  { constructor. }
  {
    destruct a, s, p, a, m.
    {
      destruct x0.
      eassert _.
      { eapply H. now left. }
      psimpl. constructor.
      { destruct i. now psimpl. }
      {
        apply IHund.
        intros. eapply H.
        right. exact H0.
      }
    }
    {
      constructor.
      apply IHund.
      {
        intros. eapply H.
        right. exact H0.
      }
    }
  }
Qed. *)

(* Lemma ob_stable {T A} :
  ∀ s d d',
    @SnapTrans T A d d' ->
    s ⊆ (λ v, ∃ i, In v d.(wrt_ordn)) ->
    ObWr s d.(wrt_ordn) ->
    ObWr s d'.(wrt_ordn).
Proof.
  intros s d d' H Hsub H0.
  induction H; auto.
  psimpl. ddestruct H; auto; psimpl.
  apply IHclos_refl_trans_1n;
  clear IHclos_refl_trans_1n H1.
  {
    intros.
    apply In_app_rev.
    left. now apply Hsub.
  }
  destruct H2. subst.
  apply Build_ObWr with
    (pfx:=pfx)
    (qfx:= qfx ++ v :: nil).
  { now rewrite app_assoc. }
  { easy. }
  {
    intros.
    apply In_app in H1.
    destruct H1; psimpl.
    { now apply all_dups. }
    {
      destruct H1;
      subst. 2: easy.
      assert (H2' := H2).
      apply Hsub, In_app in H2.
      destruct H2. easy. eauto.
    }
  }
Qed. *)
(* 
Lemma wdr_stable {T A} :
  ∀ c und d d' o t σs,
    WrtDefRes c (os_ord (RState (snd s))) o ->
    SnapTrans d d' ->
    Inv d' t σs ->
    WrtDefRes (T:=T) c (os_ord (RState (snd t))) o. *)

Lemma ob_help {T A} :
  ∀ pfx ord : list (Name T * Index T * A),
    Prefix pfx ord ->
    ObWr (set_of pfx) ord.
Proof.
  intros.
  destruct H. psimpl.
  apply Build_ObWr with
    (pfx:= pfx).
  {
    set_ext v. split;
    intros; psimpl.
    { now exists x0. }
    {
      now exists x0.
    }
  }
  { now apply prefix_cons, prefix_refl. }
Qed.

Lemma pfx_stable {T A} :
  ∀ d d',
    @SnapTrans T A d d' ->
    Prefix d.(wrt_ordn) d'.(wrt_ordn).
Proof.
  intros.
  induction H.
  {
    exists nil.
    now rewrite app_nil_r.
  }
  {
    eapply prefix_trans.
    2: exact IHclos_refl_trans_1n.
    clear H0 IHclos_refl_trans_1n.
    psimpl. ddestruct H; simpl;
    try now apply prefix_refl.
    now exists ((x0, x0, v) :: nil).
  }
Qed.

Fixpoint del_reads {T A} (wrt : list (Name T * {R : Type & prod (ArraySig (RegSig (reg_st A)) T R) R})) :=
  match wrt with
  | nil => nil
  | cons (_, existT _ _ (At _ Read, _)) wrt => del_reads wrt
  | cons ((_, existT _ _ (At _ (Write _), _)) as e) wrt => cons e (del_reads wrt)
  end.

Lemma res_stable {T A} :
  ∀ n wrt wrt' p p',
    Prefix (del_reads wrt') (del_reads wrt) ->
    @WrtPfxRes T A n wrt' p p' ->
    WrtPfxRes n wrt p p'.
Proof.
  intros. destruct H.
  gendep wrt. psimpl.
  induction H0; simpl in *;
  intros.
  { constructor. }
  { now apply IHWrtPfxRes. }
  {
    clear - IHWrtPfxRes H1 H.
    induction wrt; simpl in *.
    { easy. }
    {
      destruct a, s, p.
      destruct a, m.
      {
        ddestruct H1.
        constructor.
        { easy. }
        { now apply IHWrtPfxRes. }
      }
      {
        constructor.
        now apply IHwrt.
      }
    }
  }
  {
    clear - IHWrtPfxRes H1 H.
    induction wrt; simpl in *.
    { easy. }
    {
      destruct a, s, p.
      destruct a, m.
      {
        ddestruct H1.
        constructor.
        { easy. }
        { now apply IHWrtPfxRes. }
      }
      {
        constructor.
        now apply IHwrt.
      }
    }
  }
Qed.

Local Fixpoint remove {T A} (n : nat) (p : OWr T A) : OWr T A :=
  match p with
  | nil => nil
  | (i, m, v) :: p =>
    if classicT (`i < n) then
      remove n p
    else
      (i, m, v) :: remove n p
  end.

Lemma wrt_pfx_triv {T A} :
  ∀ n wrt p q,
    @WrtPfxRes T A n wrt p q ->
    q = remove n p.
Proof.
  intros.
  induction H;
  simpl; auto.
  { subst. case_match; lia||easy. }
  { subst. now case_match. }
Qed.

Lemma wrt_pfx_next {T A} :
  ∀ n wrt (p : OWr T A),
    WrtPfxRes (S n) wrt p (remove (S n) p) ->
    WrtPfxRes n wrt p (remove n p).
Proof.
  intros.
  dependent induction H;
  simpl in *.
  { constructor. }
  { constructor. now eapply IHWrtPfxRes. }
  {
    case_match; try lia.
    constructor.
    { lia. }
    {
      eapply IHWrtPfxRes.
      { easy. }
      {
        eapply wrt_pfx_triv.
        exact H0.
      }
    }
  }
  {
    case_match.
    constructor.
    { lia. }
    {
      eapply IHWrtPfxRes.
      { easy. }
      {
        eapply wrt_pfx_triv.
        exact H0.
      }
    }
    {
      assert (`i = n)
        by lia. subst.
      constructor.
      { lia. }
      {
        eapply IHWrtPfxRes.
        { easy. }
        { case_match; lia||easy. }
      }
    }
  }
Qed.

Lemma remove_set {T A} :
  ∀ (n : nat) (p : OWr T A),
    set_of (remove n p) = (λ v, ∃ i, `i ≥ n /\ List.In (i, i, v) p).
Proof.
  intros. set_ext v.
  split; intros; psimpl.
  {
    induction p;
    simpl in *.
    { easy. }
    {
      destruct a, p0.
      destruct (classicT (`n0 < n));
      simpl in *.
      {
        apply IHp in H. clear IHp.
        psimpl. exists x0. auto.
      }
      {
        destruct H.
        {
          ddestruct H.
          exists x.
          split; auto. lia.
        }
        {
          apply IHp in H. clear IHp.
          psimpl. exists x0. auto.
        }
      }
    }
  }
  {
    induction p;
    simpl in *.
    { easy. }
    {
      destruct a, p0.
      destruct H0.
      {
        ddestruct H0. exists x.
        case_match; lia || (simpl; auto).
      }
      {
        apply IHp in H0. clear IHp.
        psimpl. exists x0.
        case_match; simpl; auto.
      }
    }
  }
Qed.

Lemma wrt_pfx_defn {T A} :
  ∀ n wrt p q i,
    @WrtPfxRes T A n wrt p q ->
    (∃ v, In (i, i, v) q) ->
    `i ≥ n.
Proof.
  intros. psimpl.
  induction H;
  simpl in *;
  easy || auto.
  {
    destruct H0.
    { now ddestruct H0. }
    { auto. }
  }
Qed.

Lemma fill_new_correct {T A} (i : Name T) (v : A) (x : loop_st A) :
  x.(new) = emp ->
  VerifyProg i (Rely i) (Guar i)
    (λ _ _ s ρs,
      ∃ d lb vi,
        Inv d s ρs /\
        (∀ i, vi i -> (d.(und_vals) i).(val) ≠ None) /\
        lb ⊆ vi /\
        d.(rets_map) i = PRetn v (Some (λ v, ∃ i, lb i /\ (und_vals d i).(val) = Some v)) /\
        ∃ p,
          (∀ i v, List.In (i, i, v) p -> vi i) /\
          Prefix p d.(wrt_ordn) /\
          x.(old) ⊆ set_of p)
    (fill_new T x)
    (λ '(tt, y) _ _ s ρs,
      ∃ d lb vi,
        Inv d s ρs /\
        (∀ i, vi i -> (d.(und_vals) i).(val) ≠ None) /\
        lb ⊆ vi /\
        d.(rets_map) i = PRetn v (Some (λ v, ∃ i, lb i /\ (und_vals d i).(val) = Some v)) /\
        (λ v, ∃ i, vi i /\ (und_vals d i).(val) = Some v) ⊆ y.(new) /\
        y.(new) ⊆ collect d.(und_vals) /\
        ∃ p,
          (∀ i v, List.In (i, i, v) p -> vi i) /\
          Prefix p d.(wrt_ordn) /\
          y.(old) ⊆ set_of p /\
          set_of p ⊆ y.(new)).
Proof.
  intros Heq.
  unfold fill_new, runStateM, bindM.
  simpl.
  eapply weakenPost.
  eapply weakenPrec.
  apply lemRange with
    (I:=λ n y _ _ s ρs,
      ∃ d lb vi,
        Inv d s ρs /\
        (∀ i, vi i -> (d.(und_vals) i).(val) ≠ None) /\
        lb ⊆ vi /\
        rets_map d i = PRetn v (Some (λ v, ∃ i, lb i /\ (und_vals d i).(val) = Some v)) /\
        (λ v1, ∃ i0, vi i0 /\ `i0 ≥ n ∧ val (und_vals d i0) = Some v1) ⊆ new y /\
        new y ⊆ collect (und_vals d) /\
        ∃ p,
          (∀ i v, List.In (i, i, v) p -> vi i) /\
          Prefix p d.(wrt_ordn) /\
          y.(old) ⊆ set_of p /\
          ∃ p',
            WrtPfxRes n (snd s).(RState).(os_ord) p p' /\
            set_of p' ⊆ y.(new)).
  2:{
    unfold sub, subRelt.
    intros. psimpl.
    exists x0, x1, x2.
    split. easy.
    split. easy.
    split. easy.
    split. easy.
    split.
    {
      intros ??.
      destruct H6, H6, H7.
      destruct x4. psimpl.
      lia.
    }
    split.
    {
      rewrite Heq.
      now intros ??.
    }
    exists x3.
    split. easy.
    split. easy.
    split. easy.
    {
      exists nil.
      split.
      2: intros; now destruct H6, H6.
      destruct H4, H.
      rewrite H4 in wrt_def0.
      clear - wrt_def0.
      cut (
        ∀ wrt p p',
          WrtDef wrt (p ++ p') ->
          @WrtPfxRes T A T wrt p nil
      ).
      {
        intros. eapply H.
        exact wrt_def0.
      }
      clear. intros.
      dependent induction H.
      {
        destruct p.
        constructor.
        easy.
      }
      {
        constructor.
        now eapply IHWrtDef.
      }
      {
        destruct p; psimpl.
        { constructor. }
        {
          ddestruct x. constructor.
          { destruct i. now psimpl. }
          { now eapply IHWrtDef. }
        }
      }
    }
  }
  2:{
    intros [[]].
    unfold sub, subRelt.
    intros. psimpl.
    exists x0, x1, x2.
    split. easy.
    split. easy.
    split. easy.
    assert (x4 = x3).
    {
      clear - H8. revert H8.
      cut (
        ∀ wrt p p',
          @WrtPfxRes T A 0 wrt p p' → p' = p
      ).
      {
        intros.
        eapply H.
        exact H8.
      }
      clear. intros.
      induction H; now subst.
    }
    split. easy.
    clear H8. subst.
    split.
    {
      intros ??.
      destruct H8, H8.
      apply H3. exists x4.
      repeat split; (easy || lia).
    }
    split. easy.
    now exists x3.
  }
  {
    clear.
    intros.
    unfold runStateM.
    unfold lift.
    rename p into pp.
    eapply lemBind with
      (Q:=λ '(r, s) _ _ s0 ρs,
        ∃ d lb vi,
          Inv d s0 ρs /\
          (∀ i, vi i -> (d.(und_vals) i).(val) ≠ None) /\
          lb ⊆ vi /\
          rets_map d i = PRetn v (Some (λ v, ∃ i, lb i /\ (und_vals d i).(val) = Some v)) /\
          (λ v1, ∃ i0, vi i0 /\ `i0 ≥ S n ∧ val (und_vals d i0) = Some v1) ⊆ new s /\
          new s ⊆ collect (und_vals d) /\
          True /\
          ∃ p,
            (∀ i v, List.In (i, i, v) p -> vi i) /\
            match r.(val) with
            | Some w => (d.(und_vals) (exist _ n pp)) = r
            | None => ¬vi (exist _ n pp)
            end /\
            Prefix p d.(wrt_ordn) /\
            s.(old) ⊆ set_of p /\
            ∃ p',
              WrtPfxRes (S n) (snd s0).(RState).(os_ord) p p' /\
              set_of p' ⊆ s.(new)).
    {
      unfold lift.
      eapply lemBind.
      {
        pose (I:=λ s0 ρs,
          ∃ d lb vi,
            Inv d s0 ρs /\
            (∀ i, vi i -> (d.(und_vals) i).(val) ≠ None) /\
            lb ⊆ vi /\
            rets_map d i = PRetn v (Some (λ v, ∃ i, lb i /\ (und_vals d i).(val) = Some v)) /\
            (λ v1, ∃ i0, vi i0 /\ `i0 ≥ S n ∧ val (und_vals d i0) = Some v1) ⊆ new s /\
            new s ⊆ collect (und_vals d) /\
            ∃ p,
              (∀ i v, List.In (i, i, v) p -> vi i) /\
              Prefix p d.(wrt_ordn) /\
              s.(old) ⊆ set_of p /\
              ∃ p',
                WrtPfxRes (S n) (snd s0).(RState).(os_ord) p p' /\
                set_of p' ⊆ s.(new)
        ).
        assert (I_stable : Stable (Rely i) I).
        {
          unfold
            Stable, stablePrec,
            sub, subPrec.
          intros.
          destruct H as [t' [σ' [[d [lb [vi [HI [HviS [Hlb [Hr [Hns [Hus [p [Hvi [Hpfx [Hold [p' [Hwrt Hnew]]]]]]]]]]]]]]] HR]]].
          assert (HI' := HI).
          apply HR in HI. psimpl.
          exists x, lb, vi.
          split. easy.
          split.
          {
            intros i0 Hi0.
            apply HviS in Hi0.
            remember (und_vals d i0).
            destruct r, val0. simpl in *.
            eapply forget_othr, one_shot in H.
            2: now rewrite <-Heqr at 1.
            now rewrite <-H, <-Heqr.
            easy.
          }
          split. easy.
          split.
          {
            assert (
              (λ v, ∃ i, lb i /\ val (und_vals x i) = Some v) =
              (λ v, ∃ i, lb i /\ val (und_vals d i) = Some v)
            ).
            {
              set_ext y.
              split; intros [i0 [Hlbs Hy]].
              {
                exists i0.
                split. easy.
                apply Hlb, HviS in Hlbs.
                remember (und_vals d i0).
                destruct r. simpl in *.
                destruct val0. 2: easy.
                eapply forget_othr, one_shot in H.
                2: now rewrite <-Heqr.
                rewrite H in Heqr.
                rewrite <-Heqr in Hy at 1.
                easy.
              }
              {
                exists i0.
                split. easy.
                apply Hlb, HviS in Hlbs.
                remember (und_vals d i0).
                destruct r. simpl in *.
                destruct val0. 2: easy.
                eapply forget_othr, one_shot in H.
                2: now rewrite <-Heqr.
                now rewrite <-H, <-Heqr.
              }
            }
            erewrite <-Inv_pres_self.
            setoid_rewrite H1. exact Hr.
            easy.
          }
          split.
          {
            intros ??.
            destruct H1, H1, H2.
            apply Hns.
            exists x0.
            split. easy.
            split. easy.
            apply HviS in H1.
            remember (und_vals d x0).
            destruct r, val0. simpl in *.
            eapply forget_othr, one_shot in H.
            2: now rewrite <-Heqr at 1.
            rewrite <-H, <-Heqr in H3.
            now ddestruct H3.
            easy.
          }
          split.
          {
            intros.
            apply Hus in H1.
            destruct H1. exists x0.
            eapply forget_othr, one_shot in H.
            2: exact H1. now rewrite <-H.
          }
          exists p.
          split. easy.
          split.
          {
            eapply prefix_trans. exact Hpfx.
            eapply pfx_stable, forget_othr.
            exact H.
          }
          split. easy.
          exists p'. split. 2: easy.
          eapply res_stable. 2: exact Hwrt.
          clear - H H0 HI'. destruct H0, HI'.
          clear - H wrt_def0 wrt_def1.
          eapply forget_othr, pfx_stable in H.
          destruct H. rewrite H in *. clear H.
          cut (
            ∀ s t ord q,
              @WrtDef T A t (ord ++ q) ->
              WrtDef s ord ->
              Prefix (del_reads s) (del_reads t)
          ).
          {
            intros. eapply H.
            exact wrt_def0. easy.
          }
          clear. intros. gendep t.
          induction H0; simpl; intros.
          { now exists (del_reads t). }
          {
            apply IHWrtDef in H.
            clear - H0 H. destruct H.
            rewrite H. clear H.
            now exists x.
          }
          {
            adjust H (
              ∃ l,
                l = (i, i, v) :: wr ++ q /\
                WrtDef t l
            ).
            { now eexists. }
            destruct H, H.
            induction H1; psimpl; try easy;
            try specialize (IHWrtDef0 eq_refl).
            { easy. }
            {
              ddestruct H.
              apply IHWrtDef in H1.
              destruct H1. rewrite H.
              now exists x.
            }
          }
        }
        eapply weakenPrec with (P:=λ _ _, I).
        2: easy.
        eapply lemCallWk with
          (Q:=I)
          (S:=λ r s0 ρs,
            ∃ d lb vi,
              Inv d s0 ρs /\
              (∀ i, vi i -> (d.(und_vals) i).(val) ≠ None) /\
              lb ⊆ vi /\
              rets_map d i = PRetn v (Some (λ v, ∃ i, lb i /\ (und_vals d i).(val) = Some v)) /\
              (λ v1, ∃ i0, vi i0 /\ `i0 ≥ S n ∧ val (und_vals d i0) = Some v1) ⊆ new s /\
              new s ⊆ collect (und_vals d) /\
              True /\
              ∃ p,
                (∀ i v, List.In (i, i, v) p -> vi i) /\
                match r.(val) with
                | Some w => (d.(und_vals) (exist _ n pp)) = r
                | None => ¬vi (exist _ n pp)
                end /\
                Prefix p d.(wrt_ordn) /\
                s.(old) ⊆ set_of p /\
                ∃ p',
                  WrtPfxRes (S n) (snd s0).(RState).(os_ord) p p' /\
                  set_of p' ⊆ s.(new)).
        { easy. }
        {
          unfold
            Stable, stablePrec,
            sub, subPrec.
          intros.
          destruct H as [t' [σ' [[d [lb [vi [HI [HviS [Hlb [Hr [Hns [Hus [Htrue [p [Hvi [Hval [Hpfx [Hold [p' [Hwrt Hnew]]]]]]]]]]]]]]]]] HR]]].
          assert (HI' := HI).
          apply HR in HI. psimpl.
          exists x, lb, vi.
          split. easy.
          split.
          {
            intros i0 Hi0.
            apply HviS in Hi0.
            remember (und_vals d i0).
            destruct r, val0. simpl in *.
            eapply forget_othr, one_shot in H.
            2: now rewrite <-Heqr at 1.
            now rewrite <-H, <-Heqr.
            easy.
          }
          split. easy.
          split.
          {
            assert (
              (λ v, ∃ i, lb i /\ val (und_vals x i) = Some v) =
              (λ v, ∃ i, lb i /\ val (und_vals d i) = Some v)
            ).
            {
              set_ext y.
              split; intros [i0 [Hlbs Hy]].
              {
                exists i0.
                split. easy.
                apply Hlb, HviS in Hlbs.
                remember (und_vals d i0).
                destruct r. simpl in *.
                destruct val0. 2: easy.
                eapply forget_othr, one_shot in H.
                2: now rewrite <-Heqr.
                rewrite H in Heqr.
                rewrite <-Heqr in Hy at 1.
                easy.
              }
              {
                exists i0.
                split. easy.
                apply Hlb, HviS in Hlbs.
                remember (und_vals d i0).
                destruct r. simpl in *.
                destruct val0. 2: easy.
                eapply forget_othr, one_shot in H.
                2: now rewrite <-Heqr.
                now rewrite <-H, <-Heqr.
              }
            }
            erewrite <-Inv_pres_self.
            setoid_rewrite H1. exact Hr.
            easy.
          }
          split.
          {
            intros ??.
            destruct H1, H1, H2.
            apply Hns.
            exists x0.
            split. easy.
            split. easy.
            apply HviS in H1.
            remember (und_vals d x0).
            destruct r, val0. simpl in *.
            eapply forget_othr, one_shot in H.
            2: now rewrite <-Heqr at 1.
            rewrite <-H, <-Heqr in H3.
            now ddestruct H3.
            easy.
          }
          split.
          {
            intros.
            apply Hus in H1.
            destruct H1. exists x0.
            eapply forget_othr, one_shot in H.
            2: exact H1. now rewrite <-H.
          }
          split. easy.
          exists p.
          split. easy.
          split.
          {
            remember (val v0).
            destruct o. 2: easy.
            subst. symmetry in Heqo.
            symmetry. eapply one_shot.
            { eapply forget_othr, H. }
            { exact Heqo. }
          }
          split.
          {
            eapply prefix_trans. exact Hpfx.
            eapply pfx_stable, forget_othr.
            exact H.
          }
          split. easy.
          exists p'. split. 2: easy.
          eapply res_stable. 2: exact Hwrt.
          clear - H H0 HI'. destruct H0, HI'.
          clear - H wrt_def0 wrt_def1.
          eapply forget_othr, pfx_stable in H.
          destruct H. rewrite H in *. clear H.
          cut (
            ∀ s t ord q,
              @WrtDef T A t (ord ++ q) ->
              WrtDef s ord ->
              Prefix (del_reads s) (del_reads t)
          ).
          {
            intros. eapply H.
            exact wrt_def0. easy.
          }
          clear. intros. gendep t.
          induction H0; simpl; intros.
          { now exists (del_reads t). }
          {
            apply IHWrtDef in H.
            clear - H0 H. destruct H.
            rewrite H. clear H.
            now exists x.
          }
          {
            adjust H (
              ∃ l,
                l = (i, i, v) :: wr ++ q /\
                WrtDef t l
            ).
            { now eexists. }
            destruct H, H.
            induction H1; psimpl; try easy;
            try specialize (IHWrtDef0 eq_refl).
            { easy. }
            {
              ddestruct H.
              apply IHWrtDef in H1.
              destruct H1. rewrite H.
              now exists x.
            }
          }
        }
        {
          unfold Commit.
          intros. do 2 psimpl.
          clear H6 H5 H4 H3 H1 H0.
          ddestruct H2. psimpl.
          ddestruct H0. psimpl.
          ddestruct H4; psimpl.
          2:{
            unfold RegCond in H1.
            now destruct m1.
          }
          clear H0. exists ρs.
          subst I. do 2 psimpl.
          split.
          {
            assert (H' := H).
            destruct H. psimpl.
            exists (conPoss x4.(und_vals) x4.(rets_map)).
            exists x4.(rets_map). split. 2: easy.
            intros. eapply PS_refl. exact H'.
          }
          split.
          {
            intros. exists σ.
            split. easy. constructor.
          }
          assert (Inv x4 t ρs).
          {
            destruct H.
            constructor; psimpl; auto.
            {
              intros.
              specialize (und_def0 i0).
              dec_eq_nats i0 (exist (λ i, i < T) n pp).
              {
                rewrite <-x3 at 1. simpl.
                rewrite <-x at 1. simpl.
                rewrite <-und_def0 at 1.
                rewrite <-x2 at 1. simpl.
                now rewrite <-x1 at 1.
              }
              {
                rewrite <-x3 at 1. simpl.
                rewrite <-und_def0 at 1.
                rewrite <-x2 at 1. simpl.
                now rewrite H3.
              }
            }
            {
              rewrite <-x2 in wrt_def0 at 1.
              rewrite <-x3 at 1. easy.
            }
            {
              intros ??. psimpl.
              dec_eq_nats i0 (exist (λ i, i < T) n pp).
              {
                rewrite <-x3, <-x in H11 at 1.
                psimpl. destruct H11.
                now ddestruct H11.
                easy.
              }
              {
                apply (resp_own0 i0).
                exists x9, x10.
                rewrite <-x2 at 1.
                rewrite <-x3 in H11 at 1.
                now rewrite <-H3.
              }
            }
          }
          split.
          {
            exists x4, x5, x6.
            split. easy.
            split. easy.
            split. easy.
            split. easy.
            split. easy.
            split. easy.
            exists x7.
            split. easy.
            split. easy.
            split. easy.
            exists x8.
            split. 2: easy.
            rewrite <-x3 at 1.
            rewrite <-x2 in H9.
            easy.
          }
          {
            intros ??.
            eapply Inv_eqv in H12.
            2: exact H. psimpl.
            exists d. split.
            constructor. easy.
          }
        }
        {
          unfold Commit.
          intros. do 2 psimpl.
          clear H6 H5 H4 H3 H1 H0.
          ddestruct H2. psimpl.
          ddestruct H0. psimpl.
          ddestruct H4; psimpl.
          2:{
            subst I. do 2 psimpl.
            destruct H. exfalso.
            clear - x1 x x2 x3 x4 und_def0.
            specialize (und_def0 (exist _ n pp)).
            now rewrite <-x2, <-x1 in und_def0 at 1.
          }
          2:{
            subst I. do 2 psimpl.
            destruct H. exfalso.
            clear - x1 x x2 x3 x4 und_def0.
            specialize (und_def0 (exist _ n pp)).
            now rewrite <-x2, <-x1 in und_def0 at 1.
          }
          ddestruct H1.
          clear H0. exists ρs.
          subst I. do 2 psimpl.
          split.
          {
            assert (H' := H).
            destruct H. psimpl.
            exists (conPoss x4.(und_vals) x4.(rets_map)).
            exists x4.(rets_map). split. 2: easy.
            intros. eapply PS_refl. exact H'.
          }
          split.
          {
            intros. exists σ.
            split. easy. constructor.
          }
          assert (Inv x4 t ρs).
          {
            destruct H.
            constructor; psimpl; auto.
            {
              intros.
              specialize (und_def0 i0).
              dec_eq_nats i0 (exist (λ i, i < T) n pp).
              {
                rewrite <-x2, <-x1 in und_def0 at 1.
                simpl in und_def0. ddestruct und_def0.
                now rewrite <-x3, <-x at 1.
              }
              { now rewrite <-x3, <-und_def0, <-x2, H3 at 1. }
            }
            {
              rewrite <-x2 in wrt_def0 at 1.
              rewrite <-x3 at 1. now apply wrt_ordn_read.
            }
            {
              intros ??. psimpl.
              dec_eq_nats i0 (exist (λ i, i < T) n pp).
              {
                rewrite <-x3, <-x in H11 at 1.
                psimpl. destruct H11.
              }
              {
                apply (resp_own0 i0).
                exists x9, x10.
                rewrite <-x2 at 1.
                rewrite <-x3 in H11 at 1.
                now rewrite <-H3.
              }
            }
          }
          split.
          {
            exists x4, x5, x6.
            split. easy.
            split. easy.
            split. easy.
            split. easy.
            split. easy.
            split. easy.
            split. easy.
            exists x7.
            split. easy.
            split.
            {
              destruct H. psimpl.
              specialize (und_def0 (exist _ n pp)).
              rewrite <-x2, <-x1 in und_def0 at 1.
              simpl in *. ddestruct und_def0.
              remember (val (und_vals x4 (exist _ n pp))).
              destruct o0. easy. intros ?.
              apply H0 in H. congruence.
            }
            split. easy.
            split. easy.
            exists x8.
            split. 2: easy.
            rewrite <-x3 at 1.
            rewrite <-x2 in H9.
            simpl in *.
            now apply wrt_res_ordn_read.
          }
          {
            intros ??.
            eapply Inv_eqv in H12.
            2: exact H. psimpl.
            exists d. split.
            constructor. easy.
          }
        }
      }
      { intros. now apply lemRet. }
    }
    {
      intros. unfold get.
      rewrite ret_lunit.
      destruct v0, r. simpl.
      destruct val0; simpl.
      {
        apply lemRet.
        intros ?????. psimpl.
        exists x, x0, x1.
        split. easy.
        split. easy.
        split. easy.
        split. easy.
        split.
        {
          intros ??.
          destruct H12, H12, H13.
          dec_eq_nats (`x4) n.
          {
            assert (exist _ (`x4) pp = x4).
            {
              destruct x4. psimpl. f_equal.
              apply proof_irrelevance.
            }
            rewrite H15 in H7.
            rewrite H7 in H14.
            psimpl. ddestruct H14.
            now left.
          }
          {
            right.
            apply H3.
            exists x4.
            split. easy.
            split. lia.
            easy.
          }
        }
        split.
        {
          intros.
          destruct H12; psimpl.
          {
            exists (exist _ n pp).
            now rewrite H7.
          }
          { now apply H4. }
        }
        {
          exists x2.
          split. easy.
          split. easy.
          split. easy.
          exists (remove n x2).
          assert (x3 = remove (S n) x2).
          {
            eapply wrt_pfx_triv.
            exact H10.
          }
          subst.
          split. now apply wrt_pfx_next.
          intros.
          dec_eq_nats v0 a.
          { now left. }
          {
            right. apply H11.
            rewrite remove_set in H12.
            rewrite remove_set.
            unfold contains in *.
            psimpl. exists x3.
            split. 2: easy.
            cut (`x3 ≠ n).
            { intros. lia. }
            intros ?. subst.
            destruct H.
            adjust H14 (In (x3, x3, v0) (wrt_ordn x)).
            {
              clear - H14 H8.
              destruct H8. rewrite H.
              apply In_app_rev; auto.
            }
            apply ordn_val0 in H14.
            destruct x3. simpl in *.
            assert (pp = l0) by
              now apply proof_irrelevance.
            subst. rewrite H7 in H14 at 1.
            now ddestruct H14.
          }
        }
      }
      {
        apply lemRet.
        intros ?????. psimpl.
        exists x, x0, x1.
        split. easy.
        split. easy.
        split. easy.
        split. easy.
        split.
        {
          intros ??.
          destruct H12, H12, H13.
          assert (`x4 ≠ n).
          {
            intros ?. subst.
            apply H7.
            assert (exist _ (`x4) pp = x4).
            {
              destruct x4. psimpl. f_equal.
              apply proof_irrelevance.
            }
            setoid_rewrite H15.
            easy.
          }
          apply H3. exists x4.
          split. easy.
          split. lia.
          easy.
        }
        split. easy.
        exists x2.
        split. easy.
        split. easy.
        split. easy.
        exists (remove n x2).
        assert (x3 = remove (S n) x2).
        {
          eapply wrt_pfx_triv.
          exact H10.
        }
        subst.
        split. now apply wrt_pfx_next.
        assert (¬∃ v, List.In (exist _ n pp, exist _ n pp, v) x2).
        {
          intros ?. psimpl.
          apply H7. eapply H6; eauto.
        }
        intros. apply H11.
        rewrite remove_set in H13.
        rewrite remove_set.
        unfold contains in *.
        psimpl. exists x3.
        split. 2: easy.
        cut (`x3 ≠ n).
        { intros. lia. }
        intros ?. subst.
        apply H12. exists v0.
        destruct x3. simpl in *.
        assert (l0 = pp) by
          now apply proof_irrelevance.
        now subst.
      }
    }
  }
Qed.

Lemma wk_write {T A} (i i' : Name T) (v : A) :
  ∀ (P : Prec T A) (Q : unit -> Relt T A),
  VerifyProg i (Rely i) (Guar i)
    (λ _ _ s ρs, P s ρs)
    (call (At i (Write (MkReg (Some v) true))))
    Q ->
  VerifyProg i (Rely i) (Guar i)
    (λ _ _ s ρs, i' = i /\ P s ρs)
    (call (At i' (Write (MkReg (Some v) true))))
    Q.
Proof.
  unfold call. intros. ddestruct H.
  specialize (H2 tt). psimpl.
  ddestruct H3.
  eapply SafeBind with
    (QI:=λ s ρs t σs, i' = i /\ QI s ρs t σs).
  {
    unfold
      Stable, stableRelt,
      sub, subRelt.
    intros. psimpl.
    split. easy.
    apply H. psplit.
    exact H6. easy.
  }
  { apply H0. }
  {
    unfold Commit.
    intros. psimpl.
    cut (
      ∃ σs,
        (∃ σ, σs σ) /\
        (∀ σ, σs σ -> ∃ ρ, ρs ρ /\ PossSteps ρ σ) /\
        QI s ρs t σs /\
        Guar i s ρs t σs
    ).
    {
      clear.
      intros. psimpl. exists x.
      split. now exists x0.
      easy.
    }
    now apply H1.
  }
  intros [].
  split.
  {
    unfold Commit.
    intros. psimpl.
    cut (
      ∃ σs,
        (∃ σ, σs σ) /\
        (∀ σ, σs σ -> ∃ ρ, ρs ρ /\ PossSteps ρ σ) /\
        QR tt s ρs t σs /\
        Guar i s ρs t σs
    ).
    {
      clear.
      intros. psimpl. exists x.
      split. now exists x0.
      easy.
    }
    eapply H2; try easy.
    now exists x1, x2, x1, x2.
  }
  constructor.
  unfold sub, subRelt.
  intros. psimpl. apply H3.
  psplit. exact H6.
  psplit. exact H8.
  easy.
Qed.

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
          ∃ lb vi new,
            r = Some new /\
            d.(rets_map) i = PRetn v (Some lb) /\
            lb ⊆ vi /\
            PossDef d.(wrt_ordn) d.(und_vals) (PRetn v (Some vi)) (PRetn v (Some new))
        ))).
Proof.
  eapply weakenPrec with
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
        (MkD d.(und_vals) (updf d.(rets_map) i (PWait v)) d.(wrt_ordn))
        x x0
    ).
    {
      clear - H H1.
      unfold TInvoke, TIdle in H1.
      assert (H' := H).
      destruct H. psimpl.
      constructor; simpl.
      { now setoid_rewrite <- H1. }
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
            apply H3.
            now exists x1.
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
          assert (d.(rets_map) i = PIdle).
          {
            assert (
              PCalls (conPoss d.(und_vals) d.(rets_map)) i = CallIdle /\
              PRets (conPoss d.(und_vals) d.(rets_map)) i = RetIdle
            ).
            {
              apply H3.
              exists d.(rets_map).
              split.
              { intros. eapply PS_refl. exact H'. }
              { easy. }
            }
            clear - H4. psimpl.
            gendep (rets_map d i). intros.
            unfold RRet' in r. now dstr_rposs.
          }
          exists (conPoss d.(und_vals) (updf x0 i None)).
          split.
          {
            eexists.
            split. 2: easy.
            intros. specialize (H2 i0).
            unfold updf in *.
            dec_eq_nats i0 i.
            {
              rewrite eqb_id in *.
              rewrite H4. constructor.
            }
            { rewrite eqb_nid in *; auto. }
          }
          assert (x0 i = PWait v).
          {
            specialize (H2 i).
            unfold updf in H2.
            rewrite eqb_id in H2.
            now ddestruct H2.
          }
          unfold conPoss, updf.
          psimpl. rewrite H5.
          split.
          {
            repeat f_equal.
            extensionality j.
            dec_eq_nats j i.
            { now rewrite eqb_id, H5. }
            { now rewrite eqb_nid. }
          }
          split. easy.
          split. easy.
          split; intros ??;
          now rewrite eqb_nid.
        }
      }
      {
        unfold updf. intros.
        dec_eq_nats i0 i.
        { now rewrite eqb_id in H2. }
        {
          rewrite eqb_nid in H2; auto.
          eapply vi_subs0. exact H2. easy.
        }
      }
      { now setoid_rewrite <-H1. }
      { easy. }
      {
        unfold updf. intros.
        dec_eq_nats i0 i.
        { now rewrite eqb_id in H2; psimpl. }
        { rewrite eqb_nid in H2; auto. }
      }
      { easy. }
      {
        unfold updf. intros.
        dec_eq_nats i0 i.
        { now rewrite eqb_id in H2. }
        {
          rewrite eqb_nid in H2; auto.
          eapply ob_write0. exact H2.
        }
      }
    }
    clear - H0 H2.
    apply H0 in H2. psimpl.
    exists x1. split. easy.
    apply Inv_pres_self in H.
    psimpl. unfold updf in H.
    now rewrite eqb_id in H.
  }
  unfold write_snapshot.
  eapply lemBind.
  {
    eapply lemCallWk with
      (Q:=λ s ρs,
        ∃ d,
          Inv d s ρs /\
          d.(rets_map) i = PWait v)
      (S:=λ i' s ρs,
        i' = i /\
        ∃ d,
          Inv d s ρs /\
          d.(rets_map) i = PWait v).
    { apply Inv_stable. }
    {
      unfold
        Stable, stablePrec,
        sub, subPrec.
      intros. psimpl.
      split. easy.
      apply Inv_stable.
      psplit. 2: exact H0.
      now exists x1.
    }
    {
      unfold Commit.
      intros. do 2 psimpl.
      exists ρs.
      split.
      {
        assert (H' := H).
        destruct H. psimpl.
        exists (conPoss x1.(und_vals) x1.(rets_map)).
        exists x1.(rets_map). split. 2: easy.
        intros. eapply PS_refl. exact H'.
      }
      split.
      {
        intros. exists σ.
        split. easy. constructor.
      }
      assert (Inv x1 t ρs).
      {
        clear - H H7.
        destruct H. psimpl.
        constructor; simpl;
        now try setoid_rewrite <-H7.
      }
      split.
      { now exists x1. }
      {
        intros ??.
        eapply Inv_eqv in H9.
        2: exact H. psimpl.
        exists d. split.
        { constructor. }
        { easy. }
      }
    }
    {
      unfold Commit.
      intros. do 2 psimpl.
      exists ρs.
      split.
      {
        assert (H' := H).
        destruct H. psimpl.
        exists (conPoss x.(und_vals) x.(rets_map)).
        exists x.(rets_map). split. 2: easy.
        intros. eapply PS_refl. exact H'.
      }
      split.
      {
        intros. exists σ.
        split. easy. constructor.
      }
      assert (Inv x t ρs).
      {
        clear - H H7.
        destruct H. psimpl.
        constructor; simpl;
        now try setoid_rewrite <-H7.
      }
      split.
      {
        ddestruct H2.
        split. easy.
        now exists x0.
      }
      {
        intros ??.
        eapply Inv_eqv in H9.
        2: exact H. psimpl.
        exists d. split.
        { constructor. }
        { easy. }
      }
    }
  }
  intros i'. psimpl.
  eapply lemBind.
  {
    eapply lemCallWk with
      (Q:=λ s ρs,
        i' = i /\
        ∃ d,
          Inv d s ρs /\
          d.(rets_map) i = PWait v)
      (S:=λ r s ρs,
        i' = i /\
        ∃ d,
          Inv d s ρs /\
          if r.(ran) then
            d.(rets_map) i =PRetn v None
          else
            d.(rets_map) i = PWait v /\
            (d.(und_vals) i).(ran) = false).
    {
      unfold
        Stable, stablePrec,
        sub, subPrec.
      intros. psimpl.
      split. easy.
      apply Inv_stable.
      psplit. 2: exact H0.
      now exists x1.
    }
    {
      unfold
        Stable, stablePrec,
        sub, subPrec.
      intros. psimpl.
      split. easy.
      destruct (ran v0).
      {
        apply Inv_stable.
        exists x, x0.
        split. 2: easy.
        now exists x1.
      }
      {
        psimpl.
        apply H0 in H1. psimpl.
        assert (H' := H1).
        apply Inv_pres_self in H1.
        apply Inv_pres_und in H'.
        exists x2. now rewrite <-H', <-H.
      }
    }
    {
      unfold Commit.
      intros. do 2 psimpl.
      exists ρs.
      split.
      {
        assert (H3' := H3).
        destruct H3. psimpl.
        exists (conPoss x1.(und_vals) x1.(rets_map)).
        exists x1.(rets_map). split. 2: easy.
        intros. eapply PS_refl. exact H3'.
      }
      split.
      {
        intros. exists σ.
        split. easy. constructor.
      }
      assert (Inv x1 t ρs).
      {
        clear - H3 H.
        destruct H3. psimpl.
        ddestruct H. simpl in *.
        ddestruct H. simpl in *.
        ddestruct H3. simpl in *.
        constructor.
        {
          intros.
          specialize (und_def0 i0).
          rewrite <-und_def0.
          dec_eq_nats i0 i.
          { now rewrite <-x3, <-x4, <-x2, <-x at 1. }
          { now rewrite <-x3, <-x4, H2 at 1. }
        }
        {
          rewrite <-x4 at 1.
          now rewrite <-x3 in wrt_def0.
        }
        { easy. }
        { easy. }
        {
          intros ??. psimpl.
          dec_eq_nats i0 i.
          {
            rewrite <-x4, <-x in H1 at 1.
            simpl in *. destruct H1.
            now ddestruct H1. easy.
          }
          {
            apply (resp_own0 i0).
            exists x5, x6.
            rewrite <-x4 in H1 at 1.
            now rewrite <-x3, <-H2 at 1.
          }
        }
        { easy. }
        { easy. }
        { easy. }
        { easy. }
        {
          unfold RegCond in H0.
          psimpl. now destruct m1.
        }
      }
      split.
      {
        split. easy.
        now exists x1.
      }
      {
        intros ??.
        eapply Inv_eqv in H9.
        2: exact H3. psimpl.
        exists d. split.
        { constructor. }
        { easy. }
      }
    }
    {
      intros [].
      simpl in *.
      {
        unfold Commit.
        intros. do 2 psimpl.
        ddestruct H; simpl in *.
        ddestruct H; simpl in *.
        ddestruct H6; simpl in *.
        2:{
          exfalso.
          destruct H3. psimpl. specialize (und_def0 i).
          now rewrite <-x3, <-x2 in und_def0 at 1.
        }
        ddestruct H1.
        2:{
          exfalso.
          destruct H3. psimpl. specialize (und_def0 i).
          now rewrite <-x3, <-x2 in und_def0 at 1.
        }
        destruct ran0.
        {
          exists (λ σ,
            ∃ ρ, ρs ρ /\
              VisPossSteps ρ (
                ((i, CallEv (WriteSnap v)) :: nil) ++
                ((i, RetEv (WriteSnap v) None) :: nil)
              ) σ
          ).
          split.
          {
            clear - x x2 x3 x4 H3 H4.
            assert (H3' := H3).
            destruct H3. psimpl.
            pose (ρ := conPoss x1.(und_vals) x1.(rets_map)).
            remember ρ. destruct p, PState.
            exists (
              comRetPoss i
                (comInvPoss i
                  ρ
                  (WriteSnap v)
                  (SnapDef vs (updf m i (Some v)) c)
                )
                (WriteSnap v)
                (SnapDef vs m c)
                None
            ).
            exists ρ.
            split.
            {
              subst ρ. eexists.
              split. 2: easy. intros.
              eapply PS_refl. exact H3'.
            }
            {
              change (
                (i, CallEv (WriteSnap v)) ::
                (i, RetEv (WriteSnap v) None) ::
                nil
              ) with (
                ((i, CallEv (WriteSnap v)) :: nil) ++
                ((i, RetEv (WriteSnap v) None) ::
                nil)
              ).
              apply retStep.
              change (
                (i, CallEv (WriteSnap v)) :: nil
              ) with (
                nil ++ (i, CallEv (WriteSnap v)) :: nil
              ).
              apply callStep.
              constructor.
              {
                subst ρ. psimpl.
                rewrite H4.
                split. easy.
                split. easy.
                replace c with (λ i, (x1.(und_vals) i).(ran)).
                2:{
                  clear - Heqp.
                  unfold conPoss in Heqp.
                  now ddestruct Heqp.
                }
                replace vs with (collect x1.(und_vals)).
                2:{
                  clear - Heqp.
                  unfold conPoss in Heqp.
                  now ddestruct Heqp.
                }
                constructor.
                {
                  specialize (und_def0 i).
                  rewrite <-x3, <-x2 in und_def0 at 1.
                  simpl in *. ddestruct und_def0.
                  now rewrite <-x.
                }
                { now rewrite H4. }
                { unfold updf. now rewrite eqb_id. }
                {
                  clear - Heqp.
                  intros ??.
                  unfold conPoss in Heqp.
                  ddestruct Heqp. unfold updf.
                  now rewrite eqb_nid.
                }
              }
              {
                psimpl.
                rewrite eqb_id, H4.
                split. easy.
                split. easy.
                constructor.
                replace c with (λ i, (x1.(und_vals) i).(ran)).
                2:{
                  clear - Heqp.
                  unfold conPoss in Heqp.
                  now ddestruct Heqp.
                }
                replace vs with (collect x1.(und_vals)).
                2:{
                  clear - Heqp.
                  unfold conPoss in Heqp.
                  now ddestruct Heqp.
                }
                {
                  specialize (und_def0 i).
                  rewrite <-x3, <-x2 in und_def0 at 1.
                  simpl in *. ddestruct und_def0.
                  now rewrite <-x.
                }
                {
                  unfold updf.
                  now rewrite eqb_id.
                }
                {
                  subst ρ.
                  unfold conPoss in Heqp.
                  ddestruct Heqp. now rewrite H4.
                }
                {
                  unfold updf. intros ??.
                  now rewrite eqb_nid.
                }
              }
            }
          }
          split.
          {
            intros. psimpl.
            exists x5.
            split. easy.
            eapply erase_vis.
            exact H10.
          }
          destruct x1. psimpl.
          assert (
            Inv (MkD und_vals0 (updf rets_map0 i (PRetn v None)) wrt_ordn0) t
              (λ σ,
                ∃ ρ, ρs ρ /\
                VisPossSteps
                  ρ
                  (((i, CallEv (WriteSnap v)) :: nil) ++ (i, RetEv (WriteSnap v) None) :: nil)
                  σ)
          ).
          {
            psimpl.
            destruct H3. psimpl.
            constructor; simpl.
            {
              intros. rewrite <-und_def0.
              dec_eq_nats i0 i.
              { now rewrite <-x3, <-x4, <-x2, <-x at 1. }
              { now rewrite <-x3, <-x4, H5 at 1. }
            }
            {
              rewrite <-x4 at 1.
              rewrite <-x3 in wrt_def0 at 1.
              now apply wrt_ordn_read.
            }
            {
              set_ext σ.
              split; intros; psimpl.
              {
                ddestruct H3. ddestruct H12.
                ddestruct H15. ddestruct H3.
                ddestruct H16. psimpl.
                ddestruct H3.
                {
                  clear - H3 und_def0 x x0 x1 x2 x3 x4.
                  specialize (und_def0 i).
                  rewrite <-x3, <-x2 in und_def0 at 1.
                  simpl in *. ddestruct und_def0.
                  now rewrite <-x in H3.
                }
                ddestruct H19.
                exists (updf x5 i (PRetn v None)).
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
                  unfold conPoss, updf in *.
                  destruct σ. psimpl.
                  repeat f_equal.
                  {
                    rewrite <-x6 in x7.
                    now ddestruct x7.
                  }
                  {
                    extensionality j.
                    dec_eq_nats j i.
                    { now rewrite eqb_id, H21. }
                    {
                      rewrite <-x6 in x7. ddestruct x7.
                      now rewrite eqb_nid, H22, H12.
                    }
                  }
                  { rewrite <-x6 in x7. now ddestruct x7. }
                  {
                    rewrite <-x6 in x7.
                    ddestruct x7.
                    extensionality j.
                    dec_eq_nats j i.
                    { now rewrite eqb_id. }
                    { now rewrite eqb_nid, H25, H17. }
                  }
                  {
                    rewrite <-x6 in x7.
                    ddestruct x7.
                    extensionality j.
                    dec_eq_nats j i.
                    { now rewrite eqb_id. }
                    { now rewrite eqb_nid, H26, H18. }
                  }
                }
              }
              {
                exists (conPoss und_vals0 (updf x1 i (PWait v))).
                split.
                {
                  eexists.
                  split. 2: easy.
                  intros. specialize (H1 i0).
                  unfold updf in *. dec_eq_nats i0 i.
                  {
                    rewrite eqb_id, H4.
                    constructor.
                  }
                  { now rewrite eqb_nid in *. }
                }
                {
                  remember (conPoss und_vals0 (updf x1 i (PWait v))).
                  destruct p, PState.
                  assert (
                    conPoss und_vals0 x1 =
                    comRetPoss i
                      (comInvPoss i
                        (conPoss und_vals0 (updf x1 i (PWait v)))
                        (WriteSnap v)
                        (SnapDef vs (updf m i (Some v)) c)
                      )
                      (WriteSnap v)
                      (SnapDef vs m c)
                      None
                  ).
                  {
                    assert (x1 i = PRetn v None).
                    {
                      specialize (H1 i).
                      unfold updf in H1.
                      rewrite eqb_id in H1.
                      now ddestruct H1.
                    }
                    unfold conPoss, comRetPoss, comInvPoss in *.
                    clear - Heqp H3. psimpl. ddestruct Heqp.
                    repeat f_equal.
                    {
                      extensionality j.
                      unfold updf. dec_eq_nats j i.
                      { now rewrite eqb_id, H3. }
                      { now rewrite eqb_nid. }
                    }
                    {
                      extensionality j.
                      dec_eq_nats j i.
                      { now rewrite eqb_id, H3. }
                      {
                        unfold updf.
                        now repeat rewrite eqb_nid.
                      }
                    }
                    {
                      extensionality j.
                      dec_eq_nats j i.
                      { now rewrite eqb_id, H3. }
                      {
                        unfold updf.
                        now repeat rewrite eqb_nid.
                      }
                    }
                  }
                  rewrite H3.
                  change (
                    (i, CallEv (WriteSnap v)) ::
                    (i, RetEv (WriteSnap v) None) ::
                    nil
                  ) with (
                    ((i, CallEv (WriteSnap v)) :: nil) ++
                    ((i, RetEv (WriteSnap v) None) ::
                    nil)
                  ).
                  apply retStep.
                  change (
                    (i, CallEv (WriteSnap v)) :: nil
                  ) with (
                    nil ++ (i, CallEv (WriteSnap v)) :: nil
                  ).
                  apply callStep.
                  {
                    rewrite Heqp.
                    constructor.
                  }
                  {
                    unfold updf. psimpl.
                    rewrite eqb_id.
                    split. easy.
                    split. easy.
                    replace c with (λ i, (und_vals0 i).(ran)).
                    2:{
                      clear - Heqp.
                      unfold conPoss in Heqp.
                      now ddestruct Heqp.
                    }
                    replace vs with (collect und_vals0).
                    2:{
                      clear - Heqp.
                      unfold conPoss in Heqp.
                      now ddestruct Heqp.
                    }
                    constructor.
                    {
                      specialize (und_def0 i).
                      rewrite <-x3, <-x2 in und_def0 at 1.
                      simpl in *. ddestruct und_def0.
                      now rewrite <-x.
                    }
                    { now rewrite eqb_id. }
                    { unfold updf. now rewrite eqb_id. }
                    {
                      clear - Heqp.
                      intros ??.
                      unfold conPoss in Heqp.
                      ddestruct Heqp. unfold updf.
                      now rewrite eqb_nid.
                    }
                  }
                  {
                    unfold updf. psimpl.
                    repeat rewrite eqb_id.
                    split. easy.
                    split. easy.
                    constructor.
                    replace c with (λ i, (und_vals0 i).(ran)).
                    2:{
                      clear - Heqp.
                      unfold conPoss in Heqp.
                      now ddestruct Heqp.
                    }
                    replace vs with (collect und_vals0).
                    2:{
                      clear - Heqp.
                      unfold conPoss in Heqp.
                      now ddestruct Heqp.
                    }
                    {
                      specialize (und_def0 i).
                      rewrite <-x3, <-x2 in und_def0 at 1.
                      simpl in *. ddestruct und_def0.
                      now rewrite <-x.
                    }
                    {
                      unfold updf.
                      now rewrite eqb_id.
                    }
                    {
                      unfold conPoss in Heqp.
                      ddestruct Heqp. unfold updf.
                      now rewrite eqb_id.
                    }
                    {
                      unfold updf. intros ??.
                      now rewrite eqb_nid.
                    }
                  }
                }
              }
            }
            {
              unfold updf. intros.
              dec_eq_nats i0 i.
              { now rewrite eqb_id in H1. }
              {
                rewrite eqb_nid in H1; auto.
                eapply vi_subs0. exact H1. easy.
              }
            }
            {
              intros ??. psimpl.
              dec_eq_nats i0 i.
              { now rewrite <-x4, <-x in H3 at 1. }
              {
                rewrite <-x4, H5 in H3 at 1; auto.
                apply (resp_own0 i0). setoid_rewrite <-x3 at 1.
                simpl. now exists x1, x5.
              }
            }
            { easy. }
            {
              unfold updf. intros.
              dec_eq_nats i0 i.
              {
                specialize (und_def0 i).
                rewrite <-x3, <-x2 in und_def0 at 1.
                simpl in *. ddestruct und_def0.
                now rewrite <-x at 1.
              }
              { rewrite eqb_nid in H1; auto. }
            }
            { easy. }
            {
              unfold updf. intros.
              dec_eq_nats i0 i.
              { now rewrite eqb_id in H1. }
              {
                rewrite eqb_nid in H1; auto.
                eapply ob_write0. exact H1.
              }
            }
          }
          split.
          {
            split. easy.
            eexists.
            split. exact H1.
            clear. simpl.
            unfold updf.
            now rewrite eqb_id.
          }
          {
            intros ??.
            eapply Inv_eqv in H10.
            2: exact H3. psimpl.
            eexists. split.
            {
              apply SnapFail.
              exact H4.
            }
            { easy. }
          }
        }
        {
          exists ρs.
          split.
          {
            clear - H3.
            assert (H3' := H3).
            destruct H3. psimpl.
            exists (conPoss x1.(und_vals) x1.(rets_map)).
            exists x1.(rets_map).
            split. 2: easy. intros.
            eapply PS_refl. exact H3'.
          }
          split.
          {
            intros. exists σ.
            split. easy. constructor.
          }
          assert (Inv x1 t ρs).
          {
            clear - H3 x x0 x1 x2 x3 x4 H5.
            destruct H3. psimpl.
            constructor; simpl.
            {
              intros.
              dec_eq_nats i0 i.
              { now rewrite <-und_def0, <-x3, <-x4, <-x, <-x2 at 1. }
              { now rewrite <-und_def0, <-x3, <-x4, H5 at 1. }
            }
            {
              rewrite <-x4 at 1.
              rewrite <-x3 in wrt_def0.
              now apply wrt_ordn_read.
            }
            { easy. }
            { easy. }
            {
              intros ??. psimpl.
              dec_eq_nats i0 i.
              { now rewrite <-x4, <-x in H0 at 1. }
              {
                rewrite <-x4, H5 in H0 at 1; auto.
                apply (resp_own0 i0). setoid_rewrite <-x3 at 1.
                now exists x5, x6.
              }
            }
            { easy. }
            { easy. }
            { easy. }
            { easy. }
          }
          split.
          {
            split. easy.
            exists x1.
            split. easy.
            split. easy.
            clear - H3 x x0 x1 x2 x3 x4.
            destruct H3. psimpl.
            specialize (und_def0 i).
            rewrite <-x3, <-x2 in und_def0 at 1.
            simpl in *. ddestruct und_def0.
            now rewrite <-x.
          }
          {
            intros ??.
            eapply Inv_eqv in H10.
            2: exact H3. psimpl.
            exists d. split.
            { constructor. }
            { easy. }
          }
        }
      }
    }
  }
  intros [val0 [|]];
  simpl in *.
  {
    apply lemRet.
    intros ?????. psimpl.
    exists x. split. easy.
    now left.
  }
  {
    eapply lemBind.
    {
      apply wk_write.
      apply write_correct.
    }
    intros [].
    eapply lemBind with
      (Q:=λ v, _).
    2:{
      intros.
      eapply lemRet.
      unfold sub, subRelt.
      intros.
      change (
        nameSpec ⊗
        arraySpec T (
          LiftSemiRacy RegCond
            (regSpec (MkReg None false)))
      ) with (
        VE T A
      ) in s, t.
      exact H.
    }
    psimpl.
    {
      eapply lemBind.
      {
        eapply weakenPrec.
        { now apply fill_new_correct with (v:=v). }
        {
          intros ?????. psimpl.
          exists x, x0, x0.
          split. easy.
          split. easy.
          split. easy.
          split. easy.
          exists nil.
          split. easy.
          split.
          { now exists x.(wrt_ordn). }
          { easy. }
        }
      }
      intros [[]]. simpl.
      eapply weakenPrec.
      eapply lemBind.
      {
        simpl.
        pose (I := λ y s ρs,
          ∃ d lb vi,
            Inv d s ρs /\
            (∀ i, vi i -> val (d.(und_vals) i) ≠ None) /\
            lb ⊆ vi /\
            d.(rets_map) i = PRetn v (Some (λ v, ∃ i, lb i /\ val (d.(und_vals) i) = Some v)) /\
            (λ v, ∃ i, vi i /\ val (d.(und_vals) i) = Some v) ⊆ y.(new) /\
            y.(new) ⊆ collect d.(und_vals) /\
            ∃ p,
              (∀ i v, List.In (i, i, v) p -> vi i) /\
              Prefix p d.(wrt_ordn) /\
              y.(old) ⊆ set_of p /\
              set_of p ⊆ y.(new)
        ).
        eapply lemWhile with
          (I:=I).
        {
          subst I.
          unfold
            Stable, stablePrec,
            sub, subPrec.
          intros.
          destruct H as [t' [σ' [[d [lb [vi [HI [HviS [Hlb [Hr [Hns [Hus [p [Hvi [Hpfx [Hold Hnew]]]]]]]]]]]]] HR]]].
          apply HR in HI.
          destruct HI as [d' [Htran HI']].
          exists d', lb, vi.
          split. easy.
          split.
          {
            intros i0 Hi0.
            apply HviS in Hi0.
            remember (und_vals d i0).
            destruct r, val1. 2: easy.
            eapply forget_othr, Inv_mono'' in Htran.
            2:{ symmetry. now rewrite <-Heqr. }
            now rewrite <-Htran, <-Heqr.
          }
          split.
          { easy. }
          split.
          {
            assert (∀ i, lb i -> (und_vals d i).(val) = (und_vals d' i).(val)).
            {
              intros i0 Hi0. apply Hlb, HviS in Hi0.
              remember (und_vals d i0).
              destruct r, val1; try easy. simpl in *.
              eapply forget_othr, one_shot in Htran.
              2: now rewrite <-Heqr.
              now rewrite <-Htran, <-Heqr.
            }
            assert (
              (λ v, ∃ i, lb i /\ val (und_vals d' i) = Some v) =
              (λ v, ∃ i, lb i /\ val (und_vals d i) = Some v)
            ).
            {
              set_ext y.
              split; intros [i' [Hi Hy]].
              exists i'. split. easy.
              apply H in Hi. congruence.
              exists i'. split. easy.
              apply H in Hi. congruence.
            }
            erewrite <-Inv_pres_self.
            2: exact Htran. rewrite Hr.
            now rewrite <-H0 at 1.
          }
          split.
          {
            intros. apply Hns.
            destruct H, H. exists x0.
            assert (und_vals d x0 = und_vals d' x0).
            {
              apply HviS in H.
              remember (val (und_vals d x0)).
              destruct o. 2: easy.
              eapply one_shot.
              eapply forget_othr.
              exact Htran. now rewrite Heqo.
            }
            now rewrite H1.
          }
          split.
          {
            intros.
            apply Hus in H. destruct H.
            assert (H' := H).
            eapply one_shot in H.
            2: eapply forget_othr, Htran.
            exists x0. now rewrite <-H.
          }
          {
            exists p.
            split. easy.
            split.
            {
              apply forget_othr, pfx_stable in Htran.
              eapply prefix_trans. exact Hpfx. easy.
            }
            { easy. }
          }
        }
        {
          unfold SilentStep. intros.
          subst I. do 2 psimpl.
          assert (Inv x0 (tht, s) ρs).
          {
            destruct H.
            now constructor.
          }
          split.
          {
            exists x0, x1, x2.
            split. easy.
            split. easy.
            split. easy.
            split. easy.
            split. easy.
            split. easy.
            now exists x3.
          }
          {
            intros ??.
            eapply Inv_eqv in H12.
            2: exact H. subst.
            exists d. split.
            constructor. easy.
          }
        }
        {
          intros.
          unfold bindM, get, put.
          do 2 rewrite ret_lunit.
          simpl.
          eapply weakenPrec.
          apply fill_new_correct.
          { easy. }
          {
            subst I.
            intros ?????. psimpl.
            exists x0, x1, (λ i, val (x0.(und_vals) i) ≠ None).
            split. easy.
            split. easy.
            split.
            {
              intros.
              apply H0.
              now apply H1.
            }
            split. exact H2.
            exists x0.(wrt_ordn).
            split.
            {
              intros.
              apply H.(ordn_val) in H9.
              now rewrite H9.
            }
            split. apply prefix_refl.
            intros. apply H4 in H9.
            destruct H9. exists x4.
            now apply H.(ordn_val).
          }
        }
      }
      {
        intros [[]].
        unfold bindM, get. rewrite ret_lunit.
        simpl. apply lemRet. unfold sub, subRelt.
        intros. psimpl. exists x. split. easy. right.
        exists (λ v, ∃ i, x0 i /\ val (und_vals x i) = Some v), (λ v, ∃ i, x1 i /\ val (und_vals x i) = Some v), l0.(new).
        split. easy. split. easy.
        split.
        {
          unfold contains.
          intros. psimpl.
          exists x3.
          split. now apply H2.
          easy.
        }
        constructor.
        all: eauto.
        {
          assert (new l0 = old l0).
          {
            unfold negb, eqb in H0.
            now destruct (classicT (new l0 = old l0)).
          }
          rewrite H10 in *.
          assert (old l0 = set_of x2).
          {
            set_ext y. split.
            { apply H8. }
            { apply H9. }
          }
          rewrite H11.
          now apply ob_help.
        }
      }
      {
        unfold sub, subRelt.
        intros. psimpl.
        exists x, x0, x1.
        split. easy.
        split. easy.
        split. easy.
        split. easy.
        split. easy.
        split. easy.
        now exists x2.
      }
    }
  }
Qed.

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
          ∃ lb vi new,
            r = Some new /\
            d.(rets_map) i = PRetn v (Some lb) /\
            lb ⊆ vi /\
            PossDef d.(wrt_ordn) d.(und_vals) (PRetn v (Some vi)) (PRetn v (Some new))
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
    exists (MkD (λ _, MkReg None false) (λ _, PIdle) nil).
    constructor; psimpl; auto.
    { constructor. }
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
    { intros ??. now psimpl. }
    { intros. now psimpl. }
    {
      split; unfold contains;
      intros; now psimpl.
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

Definition VEOriginal T A : Spec T (E T A) :=
  tensorSpec
  nameSpec
  (arraySpec T
    (LiftSemiRacy
      RegCond
      (regSpec {| val := None; ran := false |}))).

From LHL.Core Require Import
  Linearizability
  LinFacts
  RefinesFacts
  TensorFacts.

Lemma snapshotLin T A :
  VEOriginal T A ▷ snapImpl T A ↝ VF T A.
Proof.
  eapply layerRefines_trans.
  2:{
    eapply soundness with (lay:= mkLayer _ _).
    apply writeSnapshotCorrect.
  }
  {
    apply mkLayer_monotonic.
    apply tensor_monotonic.
    { easy. }
    { apply ordspec_ref. }
  }
Qed.