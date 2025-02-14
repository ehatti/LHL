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
  Unicode.Utf8.

Record reg_st {A} := {
  val : option A;
  ran : bool
}.
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

Lemma mret_lid {E A} :
  ∀ e : StateM E A unit,
    (retM tt;;' e) = e.
Proof.
Admitted.

Lemma mret_rid {E A} :
  ∀ e : StateM E A unit,
    (e;;' retM tt) = e.
Proof.
Admitted.

Lemma range_unfold {E A n} {e : Index (S n) -> StateM E A unit} :
  range (S n) e = (range n (λ i, e (wkIx i)) ;;' e zeroIx).
induction n; cbn in *.
{
  rewrite mret_lid, mret_rid.
  unfold zeroIx. do 2 f_equal.
  apply proof_irrelevance.
}
{
  admit.
}
Admitted.

Lemma ret_lunit {E A B} :
  ∀ (v : A) (k : A -> Prog E B),
    (x <- ret v; k x) = k v.
Proof.
  intros v k.
  rewrite frobProgId at 1.
  simpl. now destruct (k v).
Qed.

CoInductive coeq {A} (x : A) : A -> Prop :=
| coeq_refl : coeq x x.

Lemma coeq_eq {A} :
  ∀ x y : A,
    coeq x y <-> eq x y.
Proof.
  intros x y.
  split; now intros [].
Qed.

Lemma ret_runit {E A} :
  ∀ e : Prog E A,
    bindProg e ret = e.
Proof.
  (* assert (∀ e : Prog E A, coeq (bindProg e ret) e).
  {
    cofix rec. intros e.
    rewrite frobProgId at 1.
    destruct e; simpl.
    {
      rewrite coeq_eq. f_equal.
      extensionality x.
      rewrite <- coeq_eq.
      apply rec.
    }
    { constructor. }
    {
      rewrite coeq_eq. f_equal.
      rewrite <- coeq_eq. apply rec.
    }
  }
  now setoid_rewrite <- coeq_eq. *)
Admitted.

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

Notation collect s := (λ v, ∃ i, arr_set s i v).

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

Lemma bound_set_full {T A} :
  ∀ (vs : set A) (s : InterState (F A) (VE T A)),
    bound_set vs 0 s = (λ v, v ∈ vs /\ collect s v).
Proof.
  intros. set_ext v.
  split; intros; psimpl.
  {
    split. easy.
    now exists x.
  }
  {
    split. easy.
    exists x.
    split. lia.
    easy.
  }
Qed.

Record Inv {T A}
  {s : InterState (F A) (VE T A)} {ρs : PossSet (VF T A)}
:= {
  val_def :
    ∀ i, (arrSt s i).(racy_val) ≠ None;
  st_cons :
    ∀ ρ, ρs ρ ->
      snapSt ρ = collect s;
}.
Arguments Inv {T A} s ρs.

(* Definition AllCombs {T A} (i : Name T) (v : A) (vs : set A) (ρs : PossSet (VF T A)) :=
  ∀ j,
    i ≠ j ->
    (∃ ρ, ρs ρ /\ Done i (WriteSnap v) (Some vs) ρ) ->
  ∀ ρ', ρs ρ' ->
    ~Idling j ρ' ->
    ∃ ρ, ρs ρ /\
      Done i (WriteSnap v) (Some vs) ρ /\
      PCalls ρ j = PCalls ρ' j /\
      PRets ρ j = PRets ρ' j. *)

Definition AllCombs {T A} (ρs : PossSet (VF T A)) :=
  ∀ sel : Name T -> option (A * option (set A)),
    (∀ i v vs,
      sel i = Some (v, vs) ->
      ∃ ρ, ρs ρ /\
        match vs with
        | Some vs => Done i (WriteSnap v) (Some vs) ρ
        | None => Called i (WriteSnap v) ρ
        end) ->
  ∃ ρ, ρs ρ /\
    ∀ i v vs,
      sel i = Some (v, vs) ->
      match vs with
      | Some vs => Done i (WriteSnap v) (Some vs) ρ
      | None => Called i (WriteSnap v) ρ
      end.

Record FillNewInv {T A} {i : Name T} {vi : set A} {v : A} {n : nat} {new : set A}
  {s : InterState (F A) (VE T A)} {ρs : PossSet (VF T A)}
: Prop := {
  fn_inv :
    Inv s ρs;
  inter_ex :
    ∀ vs,
      vi ⊆ vs ->
      vs ⊆ collect s ->
      ∃ ρ, ρs ρ /\
        Done i (WriteSnap v) (Some vs) ρ;
  new_sub :
    vi ⊆ (λ v, v ∈ new \/ (∃ i, `i < n /\ arr_set s i v /\ ¬(v ∈ new)));
  new_bound :
    new ⊆ collect s;
  vi_sub :
    vi ⊆ collect s;
  call_ex :
    ∃ ρ, ρs ρ /\
      Called i (WriteSnap v) ρ;
  all_combs : AllCombs ρs
}.
Arguments FillNewInv {T A} i vi v n new s ρs.

Record Rely {T A} (i : Name T)
  (s : InterState (F A) (VE T A)) (ρs : PossSet (VF T A))
  (t : InterState (F A) (VE T A)) (σs : PossSet (VF T A))
:= {
  pres_inv :
    Inv s ρs ->
    Inv t σs;
  val_mono :
    ∀ i v,
      arr_set s i v ->
      arr_set t i v;
  fill_all :
    ∀ v,
      (∃ ρ, ρs ρ /\
        Called i (WriteSnap v) ρ) ->
      (∃ ρ, ρs ρ /\
        Done i (WriteSnap v) (Some (collect s)) ρ) ->
    ∀ vs,
      collect s ⊆ vs ->
      vs ⊆ collect t ->
      ∃ σ, σs σ /\
        Done i (WriteSnap v) (Some vs) σ;
  pres_call :
    ∀ v,
      (∃ ρ, ρs ρ /\
        Called i (WriteSnap v) ρ) ->
      (∃ σ, σs σ /\
        Called i (WriteSnap v) σ);
  pres_done :
    ∀ v vs,
      (∃ ρ, ρs ρ /\
        Done i (WriteSnap v) (Some vs) ρ) ->
      (∃ σ, σs σ /\
        Done i (WriteSnap v) (Some vs) σ);
  pres_combs :
    AllCombs ρs ->
    AllCombs σs
}.

Definition Guar {T A} (i : Name T) : Relt T A :=
  λ s ρs t σs,
    ∀ j, i ≠ j ->
      Rely j s ρs t σs.

Lemma rely_refl {T A} :
  ∀ (i : Name T) s ρs,
    Rely (A:=A) i s ρs s ρs.
Proof.
  intros.
  constructor; auto.
  intros. psimpl.
  exists x.
  split. easy.
  assert (vs = collect s).
  {
    set_ext y.
    split; intro.
    { now apply H2. }
    { now apply H1. }
  }
  now subst.
Qed.

Lemma rt_help {A} :
  ∀ s1 s2 : set A,
    ¬ s1 ⊆ s2 ->
    s2 ⊂ s1.
Proof.
  split.
  {
    unfold not.
    intro. subst.
    now apply H.
  }
  {
    admit.
  }
Admitted.

Lemma rely_trans {T A} :
  ∀ i : Name T,
    Rely (A:=A) i ->> Rely i ==> Rely i.
Proof.
  unfold sub, subRelt.
  intros. psimpl.
  destruct H, H0.
  constructor; auto.
  intros.
  decide_prop (vs ⊆ collect x).
  { now apply pres_done1, fill_all0. }
  {
    apply rt_help in H3.
    destruct H3.
    assert (collect s ⊆ collect x).
    {
      intros.
      destruct H5.
      apply val_mono0 in H5.
      now exists x1.
    }
    apply fill_all1; auto.
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

Lemma fill_new_inv_stable {T A} :
  ∀ (i : Name T) (v : A) vi n x,
    Stable (Rely i) (FillNewInv i vi v n x).
Proof.
  intros i v vi n x s ρs H.
  psimpl. destruct H, H0.
  assert (collect x0 ⊆ collect s).
  {
    intros. destruct H.
    apply val_mono0 in H.
    now exists x2.
  }
  constructor; auto.
  {
    intros.
    decide_prop (vs ⊆ collect x0).
    {
      apply pres_done0.
      apply inter_ex0; auto.
    }
    {
      apply rt_help in H2.
      destruct H2.
      apply fill_all0; auto.
    }
  }
  {
    intros.
    apply new_sub0 in H0.
    destruct H0. now left.
    right. psimpl.
    exists x2. auto.
  }
Qed.

Lemma guar_in_rely {T A} :
  ∀ i j,
    i ≠ j ->
    @Guar T A i ==> @Rely T A j.
Proof.
  unfold sub, subRelt.
  intros. now apply H0.
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

Lemma return_step {T A} :
  ∀ (i : Name T) (v : A) (r : option (set A)),
    ReturnStep i (Guar i)
      (λ s ρs,
        (
          r = None /\
          Inv s ρs /\
          (∃ ρ, ρs ρ) /\
          ∀ ρ, ρs ρ ->
            Done i (WriteSnap v) r ρ
        ) \/
        (
          ∃ vi new,
            r = Some new /\
            FillNewInv i vi v 0 new s ρs
        ))
      (WriteSnap v) r
      (λ _ _, Inv).
Proof.
  intros i v r s ρs H H0.
  destruct H; psimpl.
  {
    exists ρs.
    split.
    { now exists x. }
    split.
    {
      intros. exists σ.
      repeat (easy || constructor).
    }
    split.
    {
      intros.
      apply H3 in H.
      now destruct H.
    }
    assert (
      Inv
        (λ j, if i =? j then Idle else fst s j, snd s)
        (λ τ, ∃ σ, ρs σ ∧ mapRetPoss i (WriteSnap v) None σ τ)
    ).
    {
      destruct H1. constructor; auto.
      unfold mapRetPoss. intros. psimpl.
      rewrite H9, st_cons0; auto.
    }
    split.
    { easy. }
    {
      intros j H4.
      constructor; auto.
      {
        intros. psimpl.
        exists (retPoss i x0).
        split.
        {
          exists x0.
          split. easy.
          apply map_ret_triv.
          now apply H3.
        }
        {
          change (
            collect (λ j : Name T, if i =? j then Idle else fst s j, snd s)
          ) with (
            collect s
          ) in H8.
          assert (vs = collect s).
          {
            set_ext y;
            split; intros.
            { now apply H8. }
            { now apply H7. }
          }
          subst. destruct H9.
          constructor; simpl;
          now rewrite eqb_nid.
        }
      }
      {
        intros. psimpl.
        exists (retPoss i x0).
        split.
        {
          exists x0.
          split. easy.
          apply map_ret_triv.
          now apply H3.
        }
        {
          destruct H6.
          constructor; simpl;
          now rewrite eqb_nid.
        }
      }
      {
        intros. psimpl.
        exists (retPoss i x0).
        split.
        {
          exists x0.
          split. easy.
          apply map_ret_triv.
          now apply H3.
        }
        {
          destruct H6.
          constructor; simpl;
          now rewrite eqb_nid.
        }
      }
      {
        unfold AllCombs. intros.
        eassert _.
        {
          apply H5 with
            (sel:=sel).
          intros.
          apply H6 in H7.
          unfold mapRetPoss in H7.
          psimpl. exists x1.
          split. easy.
          dec_eq_nats i0 i.
          {
            destruct vs, H8;
            congruence.
          }
          destruct vs, H8;
          constructor;
          now rewrite <-?H13, <-?H14.
        }
        psimpl.
        exists (retPoss i x0).
        split.
        {
          exists x0.
          auto using map_ret_triv.
        }
        {
          intros.
          dec_eq_nats i0 i.
          {
            apply H8 in H9.
            apply H3 in H7.
            destruct H7, vs, H9.
            {
              rewrite ret_done in ret_done0.
              ddestruct ret_done0.
            }
            {
              rewrite ret_done in ridle0.
              congruence.
            }
          }
          apply H8 in H9.
          destruct vs.
          { now apply done_ret. }
          { now apply called_ret. }
        }
      }
    }
  }
  {
    rename x into vi.
    rename x0 into new.
    destruct H1.
    assert (
      (λ v, v ∈ new ∨ (∃ i, `i < 0 ∧ arr_set s i v ∧ ¬ v ∈ new)) =
      new
    ).
    {
      set_ext v0.
      split; intro.
      {
        destruct H.
        { easy. }
        { psimpl. lia. }
      }
      { now left. }
    }
    assert (vi ⊆ new).
    { now rewrite <- H. }
    clear new_sub0 H. 
    exists (λ ρ,
      ρs ρ /\
      Done i (WriteSnap v) (Some new) ρ).
    split.
    { now apply inter_ex0. }
    split.
    {
      intros. psimpl. exists σ.
      repeat (easy || constructor).
    }
    split.
    {
      intros. psimpl.
      now destruct H2.
    }
    assert (
      Inv
        (λ j, if i =? j then Idle else fst s j, snd s)
        (λ τ, ∃ σ,
          (ρs σ ∧ Done i (WriteSnap v) (Some new) σ) ∧
          mapRetPoss i (WriteSnap v) (Some new) σ τ)
    ).
    {
      destruct fn_inv0.
      constructor; auto.
      unfold mapRetPoss.
      intros. psimpl.
      now rewrite H8, st_cons0.
    }
    split.
    { easy. }
    {
      intros j H2.
      psimpl.
      constructor; auto.
      {
        intros. psimpl.
        assert (vs = collect s).
        {
          set_ext y.
          split; intro.
          { now apply H8. }
          { now apply H7. }
        }
        subst. clear H7 H8.
        assert (
          ∃ ρ, ρs ρ /\
            Done i (WriteSnap v) (Some new) ρ /\
            Done j (WriteSnap v0) (Some (collect s)) ρ
        ).
        {
          unfold AllCombs in all_combs0.
          eassert _.
          {
            apply all_combs0 with
              (sel:=λ k,
                if i =? k then
                  Some (v, Some new)
                else if j =? k then
                  Some (v0, Some (collect s))
                else
                  None).
            intros.
            dec_eq_nats i0 i.
            {
              rewrite eqb_id in H7.
              inversion H7. subst.
              apply inter_ex0; auto.
            }
            rewrite eqb_nid in H7; auto.
            dec_eq_nats i0 j.
            {
              rewrite eqb_id in H7.
              inversion H7. subst.
              exists x0. auto.
            }
            { now rewrite eqb_nid in H7; auto. }
          }
          psimpl. exists x2.
          split. easy. split.
          {
            apply H8 with (vs:= Some new).
            now rewrite eqb_id.
          }
          {
            apply H8 with (vs:= Some (collect s)).
            now rewrite eqb_id, eqb_nid.
          }
        }
        psimpl.
        exists (retPoss i x2).
        split.
        {
          exists x2.
          auto using map_ret_triv.
        }
        {
          destruct H11.
          constructor; simpl;
          now rewrite eqb_nid.
        }
      }
      {
        intros. psimpl.
        assert (
          ∃ ρ, ρs ρ /\
            Done i (WriteSnap v) (Some new) ρ /\
            Called j (WriteSnap v0) ρ
        ).
        {
          unfold AllCombs in all_combs0.
          eassert _.
          {
            apply all_combs0 with
              (sel:=λ k,
                if i =? k then
                  Some (v, Some new)
                else if j =? k then
                  Some (v0, None)
                else
                  None).
            intros.
            dec_eq_nats i0 i.
            {
              rewrite eqb_id in H7.
              inversion H7. subst.
              apply inter_ex0; auto.
            }
            rewrite eqb_nid in H7; auto.
            dec_eq_nats i0 j.
            {
              rewrite eqb_id in H7.
              inversion H7. subst.
              exists x0. auto.
            }
            { now rewrite eqb_nid in H7; auto. }
          }
          psimpl.
          exists x1.
          split. easy.
          split.
          {
            apply H8 with (vs:= Some new).
            now rewrite eqb_id.
          }
          {
            apply H8 with (vs:=None).
            now rewrite eqb_id, eqb_nid.
          }
        }
        psimpl.
        exists (retPoss i x1).
        split.
        {
          exists x1.
          auto using map_ret_triv.
        }
        {
          destruct H9.
          constructor; simpl;
          now rewrite eqb_nid.
        }
      }
      {
        intros. psimpl.
        assert (
          ∃ ρ, ρs ρ /\
            Done i (WriteSnap v) (Some new) ρ /\
            Done j (WriteSnap v0) (Some vs) ρ
        ).
        {
          unfold AllCombs in all_combs0.
          eassert _.
          {
            apply all_combs0 with
              (sel:=λ k,
                if i =? k then
                  Some (v, Some new)
                else if j =? k then
                  Some (v0, Some vs)
                else
                  None).
            intros.
            dec_eq_nats i0 i.
            {
              rewrite eqb_id in H7.
              inversion H7. subst.
              apply inter_ex0; auto.
            }
            rewrite eqb_nid in H7; auto.
            dec_eq_nats i0 j.
            {
              rewrite eqb_id in H7.
              inversion H7. subst.
              exists x0. auto.
            }
            { now rewrite eqb_nid in H7; auto. }
          }
          psimpl.
          exists x1.
          split. easy.
          split.
          {
            apply H8 with (vs:= Some new).
            now rewrite eqb_id.
          }
          {
            apply H8 with (vs:= Some vs).
            now rewrite eqb_id, eqb_nid.
          }
        }
        psimpl.
        exists (retPoss i x1).
        split.
        {
          exists x1.
          auto using map_ret_triv.
        }
        {
          destruct H9.
          constructor; simpl;
          now rewrite eqb_nid.
        }
      }
      {
        unfold AllCombs. intros.
        eassert _.
        {
          apply H5 with
            (sel:=λ k,
              if i =? k then
                Some (v, Some new)
              else
                sel k).
          intros. dec_eq_nats i0 i.
          {
            rewrite eqb_id in H7.
            ddestruct H7.
            apply inter_ex0; auto.
          }
          {
            rewrite eqb_nid in H7; auto.
            apply H6 in H7. psimpl.
            unfold mapRetPoss in H10. psimpl.
            exists x1.
            split. easy.
            destruct vs, H9;
            constructor;
            now rewrite <-?H15, <-?H16.
          }
        }
        clear H5 H6. psimpl.
        exists (retPoss i x0).
        split.
        {
          exists x0.
          specialize (H6 i v (Some new)).
          rewrite eqb_id in H6.
          auto using map_ret_triv.
        }
        {
          intros.
          dec_eq_nats i0 i.
        }
      }
    }
  }

Lemma fill_new_correct {T A} (i : Name T) (v : A) (x : loop_st A) :
  VerifyProg i (Rely i) (Guar i)
    (λ _ _ s ρs, ∃ vs, FillNewInv i v vs T x s ρs)
    (fill_new T x)
    (λ '(tt, y) _ _ s ρs, ∃ vs, FillNewInv i v vs 0 y s ρs).
Proof.
  unfold fill_new.
  unfold runStateM, bindM. simpl.
  eapply weakenPost.
  apply lemRange with
    (I:=λ n x _ _ s ρs,
      ∃ vs, FillNewInv i v vs n x s ρs);
  clear.
  2: now destruct v0, u.
  intros n x Hlt.
  unfold runStateM, bindM, lift.
  simpl.
  eapply lemBind with
    (Q:=λ '(_, x'') _ _ s ρs,
      ∃ vs, FillNewInv i v vs n x'' s ρs).
  {
    eapply lemBind.
    {
      apply (lemCall
        (Q:=λ _ _ s ρs,
          ∃ vs, FillNewInv i v vs (S n) x s ρs)
        (S:=λ lsp _ _ s ρs,
          ∃ vs, FillNewInv i v vs n x s ρs)).
      {
        unfold
          Stable, stableRelt,
          sub, subRelt.
        intros. psimpl. exists x2.
        apply fill_new_inv_stable.
        psplit. exact H. easy.
      }
      {
        unfold
          Stable, stablePost, stableRelt,
          sub, subRelt.
        intros. psimpl. exists x2.
        apply fill_new_inv_stable.
        psplit. exact H. easy.
      }
      {
        intros s ρs t Hinv Hdpt Hus Hss.
        simpl in *. psimpl. ddestruct H.
        cbn in *. ddestruct H3.
        clear H H0 H1 H5.
        2:{
          cbv in H0.
          now destruct m1.
        }
        assert (∀ j, (arrSt t j).(racy_val) = (arrSt s j).(racy_val)).
        {
          intros.
          dec_eq_nats j (exist (λ i, i < T) n Hlt).
          { now rewrite <- x1, <- x at 1. }
          { now rewrite H2. }
        }
        assert (Inv t ρs).
        {
          destruct H4, fn_inv0.
          constructor.
          (* { now setoid_rewrite H. } *)
          { now setoid_rewrite H. }
          { easy. }
          { easy. }
        }
        exists ρs.
        split.
        { apply H0. }
        split.
        {
          intros. exists σ.
          repeat (easy || constructor).
        }
        split.
        {
          exists x2.
          destruct H4.
          constructor; try easy.
          (* {
            intros ??.
            apply pfx_subs0 in H1.
            destruct H1. exists x3.
            now rewrite H.
          } *)
        }
        {
          constructor.
          { easy. }
          { easy. }
          { now setoid_rewrite H. }
        }
      }
      intros [val ran].
      {
        intros s ρs t Hinv Hdpt Hus Hss.
        destruct Hinv, H, H, H, H. clear H.
        psimpl. psimpl. simpl in *.
        ddestruct H0. simpl in *.
        ddestruct H4; simpl in *.
        2:{
          exfalso.
          eapply H.(fn_inv).(val_def).
          now rewrite <- x1 at 1.
        }
        2:{
          exfalso.
          eapply H.(fn_inv).(val_def).
          now rewrite <- x1 at 1.
        }
        ddestruct H1. clear - H H3 H6 x1 x.
        destruct H, fn_inv0. psimpl.
        exists (λ σ,
          ∃ ρ, ρs ρ /\
            Called i (WriteSnap v) ρ /\
            (
              σ = ρ \/
              VisPossSteps ρ ((i, RetEv (WriteSnap v) (Some (snapSt ρ))) :: nil) σ
            )
        ).
        assert (∀ j, (arrSt t j).(racy_val) = (arrSt s j).(racy_val)).
        {
          intros.
          dec_eq_nats j (exist (λ i, i < T) n Hlt).
          { now rewrite <- x1, <- x at 1. }
          { now rewrite H3. }
        }
        split.
        { admit. }
        split.
        {
          intros. psimpl.
          destruct H4; subst;
          (exists x3;
          split;[easy|idtac]).
          { constructor. }
          { eapply erase_vis. exact H4. }
        }
        split.
        {
          exists (snapSt x2).
          constructor.
          {
            constructor.
            { now setoid_rewrite H0. }
            { admit. }
            { admit. }
          }
          {
            destruct val.
            {
              intros ??. right.
              now apply old_subs0.
            }
            { easy. }
          }
          {
            
          }
        }
      }
    }
    {
      intros [val ran].
      eapply lemRet.
      unfold sub, subRelt.
      intros. psimpl.
      now exists x4.
    }
  }
  intros [[val ran] x'].
  unfold get, put. simpl.
  rewrite ret_lunit.
  destruct val; simpl.
  {
    apply lemRet.
    unfold sub, subRelt.
    intros _ _ s ρs [vs H].
    exists vs. destruct H.
    constructor; try easy.
    {
      intros. simpl.
      apply subs_new0 in H.
      now right.
    }
  }
  { now apply lemRet. }
Admitted.


Lemma ws_correct {T A} (i : Name T) (v : A) :
  VerifyProg i (Rely i) (Guar i)
    (prComp Inv (TInvoke (snapImpl T A) i _ (WriteSnap v)) ->> Rely i)
    (write_snapshot v)
    (λ r _ _, Posts i v r).
Proof.
  unfold write_snapshot.
  apply lemBindSelf.
  { admit. }
  eapply lemBind.
  {
    admit.
  }
  intros i'.
  eapply lemBind.
  {
    admit.
  }
  intros [val ran]. simpl.
  destruct ran.
  {
    admit.
  }
  {
    eapply lemBind with
      (Q:=λ _ _ _ s ρs, ∃ vs, FillNewInv i v vs T (MkSt emp emp) s ρs).
    {
      admit.
    }
    intros []. clear val.
    eapply lemBind.
    {
      unfold runStateM, bindM.
      eapply lemBind.
      { apply fill_new_correct. }
      intros [[] [val ran]].
      eapply lemBind.
      {

      }
    }
  }