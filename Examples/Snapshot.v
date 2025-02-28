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
  Logic.ClassicalChoice
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
    (S : Relt VE VF) P (Q : A -> Relt VE VF),
    Stable R S ->
    (forall x, SilentStep i G (Q x) S) ->
    (forall x, Q x ->> S ==> P) ->
    (∀ x,
      VerifyProg i R G
        P
        (e x)
        (λ '(tt, y), Q y)) ->
    ∀ x,
      VerifyProg i R G
        P
        (while b e x)
        (λ '(tt, y) s ρs t σs, Q y s ρs t σs).
Proof.
  intros b e S P Q.
  intros S_stable.
  intros S_silent.
  intros S_compose.
  intros.
  
  unfold VerifyProg in *.
  rewrite paco_eqv.
  generalize dependent x.
  generalize dependent P.
  cut (
    ∀ P P'' : Relt VE VF,
    P'' ==> P →
    (∀ x : A, Q x ->> S ==> P)
      → (∀ x : A, SafeProg i R G P (e x) (λ '(u, y), let 'tt := u in Q y))
        → ∀ x : A,
            paco_safe i R G P'' (while b e x)
              (λ '(u, y),
                let
                'tt := u in
                  λ (s : InterState F VE) (ρs : PossSet VF) (t : InterState F VE) 
                    (σs : PossSet VF), Q y s ρs t σs)
  ).
  {
    intros. eapply H with (P'':=P) (P:=P); auto.
    unfold sub, subRelt. auto.
  }
  pcofix rec.

  intros.
  unfold while.

  pose proof H2 as Hbody.

  remember e as e'.
  rewrite Heqe' in rec.
  rewrite Heqe' in Hbody.
  rewrite Heqe' at 1.
  clear Heqe'.

  remember P as P'.
  (* rewrite HeqP' in H0. *)
  rewrite HeqP' in Hbody.
  (* rewrite HeqP' in H0. *)
  rewrite HeqP' in H1.
  clear HeqP'.

  specialize (H2 x).
  generalize dependent (e' x).
  revert x.
  generalize dependent P'.
  generalize dependent P''.
  generalize dependent e'.
  pcofix rec'. intros; pfold.
  rewrite frobProgId.
  destruct p; cbn; auto.
  {
    ddestruct H2.
    econstructor;
    [exact H|exact H2|
      eapply weakenCommitPre; eauto
    |].
    intros.
    specialize (H4 v).
    psimpl. split.
    - eapply weakenCommitPre; eauto.
      clear - H0.
      unfold sub, subRelt, ReltCompose in *.
      intros. destruct_all.
      eexists. eexists. eauto.
    - right. eapply rec' with (P':=P0 ->> QI ->> QR v); auto.
      unfold sub, subRelt, ReltCompose in *.
      intros.
      destruct H6 as [? [? [? [? [? [? ?]]]]]].
      eexists. eexists. split; eauto.
  }
  {
    ddestruct H2.
    destruct p, u.
    simpl.
    destruct (b a).
    - fold (@whileAux E A b e (e a)).
      (* specialize (rec _ S_compose Inv Hbody). *)
      econstructor.
      + exact S_stable.
      + unfold SilentStep in *. intros.
        specialize (S_silent a).
        apply S_silent; auto.
        unfold ReltToPrec in *. destruct_all.
        eexists. eexists. eauto.
      + right.
        eapply rec; auto.
        unfold sub, subRelt, ReltCompose in *.
        intros.
        destruct H2 as [? [? [? ?]]].
        eapply H1. eexists. eexists. eauto.
    - econstructor.
      unfold sub, subRelt, ReltCompose in *.
      eauto.
  }
  {
    ddestruct H2.
    econstructor;
    [exact H| |].
    - clear - H0 H2.
      unfold sub, subRelt, ReltCompose in *.
      unfold SilentStep in *.
      intros.
      eapply H2; eauto.
      unfold ReltToPrec in *. destruct_all.
      eexists. eexists. eauto.
    - right. eapply rec'; eauto.
      clear - H0.
      unfold sub, subRelt, ReltCompose in *.
      intros. destruct_all.
      eexists. eexists. eauto.
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

Definition OWr T := option (Name T).

Record pdata {T A} := MkD {
  und_vals : Index T -> reg_st A;
  rets_map : Name T -> RRet' T A A
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

Record ObWr {T A}
  (wr : OWr T) (st : Name T -> reg_st A)
  (r : set A) (li : Name T) (lv : A)
:= {
  wr_some : wr = Some li;
  val_some : (st li).(val) = Some lv;
  ret_full : lv ∈ r -> r = collect st
}.

Variant PossDef {T A} {wr : OWr T} {st : Name T -> reg_st A} :
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
  (∀ li,
    wr = Some li ->
    ∃ lv,
      (st li).(val) = Some lv /\
      (lv ∈ vs -> vs = collect st)) ->
  vi ⊆ vs ->
  vs ⊆ collect st ->
  PossDef (Some (v, Some (Some (Some vi)))) (Some (v, Some (Some (Some vs))))
| PDRetnSomeCall v vi :
  PossDef (Some (v, Some (Some (Some vi)))) (Some (v, Some None)).
Arguments PossDef {T A} wr st _ _.

(* global invariant, should always hold *)
Record Inv {T A}
  {last_wrt : OWr T} {d : pdata T A}
  {s : InterState (F A) (VE T A)} {ρs : PossSet (VF T A)}
: Prop := {
  und_def :
    ∀ i, (arrSt s i).(racy_val) = Some (d.(und_vals) i);
  ovr_def :
    ρs = (λ ρ,
      ∃ dρ,
        (∀ i, PossDef last_wrt d.(und_vals) (d.(rets_map) i) (dρ i)) /\
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
  ob_write :
    match last_wrt with
    | None =>
      collect d.(und_vals) = emp
    | Some li =>
      ∃ lv,
        (d.(und_vals) li).(val) = Some lv /\
        ∀ i v vs,
          d.(rets_map) i = PRetn v (Some vs) ->
          lv ∈ vs ->
          vs = collect d.(und_vals)
    end
}.
Arguments Inv {T A} last_wrt d s ρs.

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
  x i = PWait v ->
  SnapTran
    (MkD s x)
    (MkD s (updf x i (PRetn v None)))
| SnapWrite v s x :
  s i = MkReg None false ->
  x i = PWait v ->
  SnapTran
    (MkD s x)
    (MkD
      (updf s i (MkReg (Some v) true))
      (updf x i (PRetn v (Some (insert v (collect s)))))).
Arguments SnapTran {T A} i.

Definition Guar {T A} (i : Name T) : Relt T A :=
  λ s ρs t σs,
    ∀ last_wrt d,
      Inv last_wrt d s ρs ->
      ∃ last_wrt' d',
        SnapTran i d d' /\
        Inv last_wrt' d' t σs.

Definition SnapTrans {T A} :=
  clos_refl_trans_1n (pdata T A) (λ d d', ∃ i, SnapTran i d d').

Definition OtherSnapTrans {T A} (i : Name T) :=
  clos_refl_trans_1n (pdata T A) (λ d d', ∃ j, i ≠ j /\ SnapTran j d d').

Definition Rely {T A} (i : Name T) : Relt T A :=
  λ s ρs t σs,
    ∀ last_wrt d,
      Inv last_wrt d s ρs ->
      ∃ last_wrt' d',
        OtherSnapTrans i d d' /\
        Inv last_wrt' d' t σs.

Lemma rely_refl {T A} :
  ∀ (i : Name T) s ρs,
    Rely (A:=A) i s ρs s ρs.
Proof.
  unfold Rely. intros.
  exists last_wrt, d. split.
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
  exists x3, x4. split. 2: easy.
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
  exists x, x0. split.
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
  λ s ρs, ∃ last_wrt d, Inv last_wrt d s ρs /\ P d.

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

Ltac case_match :=
  match goal with
  | |- context[classicT ?P] => destruct (classicT P)
  end.

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
  ∀ last_wrt (d : pdata T A) s ρs i,
    Inv last_wrt d s ρs ->
    PossDef last_wrt d.(und_vals) (d.(rets_map) i) (d.(rets_map) i).
Proof.
  intros. destruct H.
  remember (rets_map d i).
  unfold RRet' in r. dstr_rposs;
  try constructor.
  {
    intros.
    rewrite H in ob_write0.
    psimpl. exists x.
    split. easy. eapply H1.
    symmetry. exact Heqr.
  }
  { easy. }
  {
    eapply vi_subs0.
    symmetry. exact Heqr.
  }
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

Lemma Inv_eqv {T A} :
  ∀ l1 l2 (d1 d2 : pdata T A) s ρs,
    Inv l1 d1 s ρs ->
    Inv l2 d2 s ρs ->
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
  rename l1 into l0.
  rename l2 into l1.
  assert (
    (λ ρ, ∀ i, PossDef l0 und_vals0 (rets_map0 i) (ρ i)) =
    (λ ρ, ∀ i, PossDef l1 und_vals0 (rets_map1 i) (ρ i))
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
  rewrite set_eq in H.
  assert (H' := H).
  specialize (H rets_map0).
  specialize (H' rets_map1).
  assert (∀ i, PossDef l0 und_vals0 (rets_map0 i) (rets_map0 i)).
  {
    intros.
    eapply PS_refl with
      (d:= MkD und_vals0 rets_map0)
      (s:=s).
    now constructor.
  }
  assert (∀ i, PossDef l1 und_vals0 (rets_map1 i) (rets_map1 i)).
  {
    intros.
    eapply PS_refl with
      (d:= MkD und_vals0 rets_map1)
      (s:=s).
    now constructor.
  }
  destruct H, H'.
  extensionality i.
  apply H with (i:=i) in H0.
  apply H4 with (i:=i) in H1.
  generalize dependent (rets_map0 i).
  generalize dependent (rets_map1 i).
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
  exists last_wrt, (MkD und_vals0 (updf rets_map0 i (PWait v))).
  destruct H1. psimpl.
  assert (rets_map0 i = PIdle).
  {
    specialize (H5 (conPoss und_vals0 rets_map0)).
    eassert _.
    {
      apply H5.
      exists rets_map0.
      split. 2: easy. intros.
      eapply PS_refl with (d:=MkD _ _).
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
    { now setoid_rewrite <-H3. }
    { easy. }
    {
      unfold updf. intros.
      dec_eq_nats i0 i.
      { psimpl. now rewrite eqb_id in H4. }
      { rewrite eqb_nid in H4; auto. }
    }
    {
      clear - ob_write0.
      destruct last_wrt;
      intros; psimpl.
      {
        exists x.
        split. easy.
        unfold updf. intros.
        dec_eq_nats i0 i.
        {
          rewrite eqb_id in H1.
          ddestruct H1.
        }
        {
          rewrite eqb_nid in H1; auto.
          eapply H0. exact H1. easy.
        }
      }
      { easy. }
    }
  }
Qed.

Axiom neg_all : ∀ A (P : A -> Prop), (¬(∀ x, P x)) -> ∃ x, ¬P x.
Axiom neg_imp : ∀ (P Q : Prop), ¬(P -> Q) -> P /\ ¬Q.
Axiom neg_som : ∀ A (P : A -> Prop), (¬(∃ x, P x)) -> ∀ x, ¬P x.
Axiom neg_and : ∀ (P Q : Prop), ¬(P /\ Q) -> ¬P \/ ¬Q.

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
  exists last_wrt, (MkD und_vals0 (updf rets_map0 i PIdle)).
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
      eapply PS_refl with (d:=MkD _ _).
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
            {
              intros. subst. psimpl.
              exists x2. split. easy.
              eapply H6. exact H1.
            }
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
    {
      clear - ob_write0.
      destruct last_wrt;
      intros; psimpl.
      {
        exists x.
        split. easy.
        unfold updf. intros.
        dec_eq_nats i0 i.
        {
          rewrite eqb_id in H1.
          ddestruct H1.
        }
        {
          rewrite eqb_nid in H1; auto.
          eapply H0. exact H1. easy.
        }
      }
      { easy. }
    }
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

Lemma return_step {T A} :
  ∀ (i : Name T) (v : A) (r : option (set A)),
    ReturnStep i (Guar i)
      (λ s ρs,
        ∃ last_wrt d, Inv last_wrt d s ρs /\
          ((
            r = None /\
            d.(rets_map) i = PRetn v None
          ) \/
          (
            ∃ vi new,
              r = Some new /\
              d.(rets_map) i = PRetn v (Some vi) /\
              vi ⊆ new /\
              new ⊆ collect d.(und_vals) /\
              (∀ li,
                last_wrt = Some li ->
                ∃ lv,
                  val (d.(und_vals) li) = Some lv /\
                  (lv ∈ new → new = collect d.(und_vals)))
          )))
      (WriteSnap v) r
      (λ _ _ s ρs,
        ∃ last_wrt d, Inv last_wrt d s ρs).
Proof.
  intros i v r s ρs H _.
  psimpl. destruct H0; psimpl.
  rename x into last_wrt.
  rename x0 into x.
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
          eapply PS_refl with (d:=MkD _ _).
          now constructor.
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
        last_wrt
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
      {
        unfold updf. intros.
        dec_eq_nats i0 i.
        { psimpl. now rewrite eqb_id in H. }
        { rewrite eqb_nid in H; auto. }
      }
      {
        destruct last_wrt.
        {
          psimpl. exists x.
          split. easy. unfold updf.
          intros. dec_eq_nats i0 i.
          { now rewrite eqb_id in H2. }
          {
            rewrite eqb_nid in H2; auto.
            eapply H0. exact H2. easy.
          }
        }
        { easy. }
      }
    }
    split.
    { eexists _, _. exact H0. }
    {
      intros ???.
      eapply Inv_eqv in H2.
      2: exact H. psimpl.
      eexists _, _. split.
      {
        now apply SnapReturn with
          (v:=v) (vi:=None).
      }
      { exact H0. }
    }
  }
  {
    rename x into last_wrt.
    rename x0 into d.
    rename x1 into vi.
    rename x2 into new.
    rename H4 into rw_H.
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
          eapply PS_refl with (d:= MkD _ _).
          now constructor.
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
        last_wrt
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
      {
        unfold updf. intros.
        dec_eq_nats i0 i.
        { psimpl. now rewrite eqb_id in H. }
        { rewrite eqb_nid in H; auto. }
      }
      {
        clear - ob_write0.
        destruct last_wrt.
        {
          psimpl. exists x.
          split. easy. unfold updf.
          intros. dec_eq_nats i0 i.
          { now rewrite eqb_id in H1. }
          {
            rewrite eqb_nid in H1; auto.
            eapply H0. exact H1. easy.
          }
        }
        { easy. }
      }
    }
    split.
    { eexists _, _. exact H0. }
    {
      intros ???.
      eassert (_ = d).
      {
        eapply Inv_eqv.
        exact H. exact H4.
      }
      psimpl. eexists _, _.
      split.
      {
        now apply SnapReturn with
          (v:=v) (vi:= Some vi).
      }
      { exact H0. }
    }
  }
Qed.

Check @lemCall.
Arguments lemCall {T i E F VE VF R G A} Q S.

Lemma Inv_stable {T A} :
  ∀ i c,
    Stable (@Rely T A i) (λ s ρs,
      ∃ last_wrt d,
        Inv last_wrt d s ρs /\
        d.(rets_map) i = c).
Proof.
  unfold
    Stable, stablePrec,
    sub, subPrec.
  intros. psimpl.
  apply H0 in H. psimpl.
  exists x3, x4. split. easy.
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

Lemma write_correct {T A} (i : Name T) (v : A) :
  VerifyProg i (Rely i) (Guar i)
    (λ _ _ s ρs,
      ∃ last_wrt d,
        Inv last_wrt d s ρs /\
        d.(rets_map) i = PWait v /\
        (d.(und_vals) i).(ran) = false)
    (call (At i (Write (MkReg (Some v) true))))
    (λ 'tt _ _ s ρs,
      ∃ last_wrt d vi,
        Inv last_wrt d s ρs /\
        (∀ i, vi i -> (d.(und_vals) i).(val) ≠ None) /\
        d.(rets_map) i = PRetn v (Some (λ v, ∃ i, vi i /\ (und_vals d i).(val) = Some v))).
Proof.
  eapply weakenPost.
  eapply lemCallWk with
    (Q:=λ s ρs,
      ∃ last_wrt d,
        Inv last_wrt d s ρs /\
        d.(rets_map) i = PWait v /\
        (d.(und_vals) i).(ran) = false /\
        (d.(und_vals) i).(val) = None)
    (S:=λ _ s ρs,
      ∃ last_wrt d vi,
        Inv last_wrt d s ρs /\
        (∀ i, vi i -> (d.(und_vals) i).(val) ≠ None) /\
        d.(rets_map) i = PRetn v (Some (λ v, ∃ i, vi i /\ (und_vals d i).(val) = Some v))).
  {
    unfold
      Stable, stablePrec,
      sub, subPrec.
    intros. psimpl.
    apply H0 in H. psimpl.
    exists x3, x4. split. easy.
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
    exists x4, x5, x3.
    split. easy.
    assert (H' := H).
    apply Inv_pres_self in H.
    assert (∀ i, x3 i -> (und_vals x5 i).(val) = (und_vals x2 i).(val)).
    {
      intros. apply H1 in H4.
      remember (und_vals x2 i0).
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
        (λ v, ∃ i, x3 i /\ val (und_vals x2 i) = Some v) =
        (λ v, ∃ i, x3 i /\ val (und_vals x5 i) = Some v)
      ).
      {
        set_ext y.
        split; intros; psimpl.
        exists x6. split. easy.
        apply H4 in H5. congruence.
        exists x6. split. easy.
        apply H4 in H5. congruence.
      }
      now rewrite <-H5, <-H.
    }
  }
  {
    unfold Commit.
    intros. do 2 psimpl.
    rename x1 into last_wrt.
    rename x2 into x1.
    exists ρs.
    split.
    {
      clear - H. destruct H. psimpl.
      exists (conPoss x1.(und_vals) x1.(rets_map)), x1.(rets_map).
      split. 2: easy. intros.
      eapply PS_refl with (d:= MkD _ _).
      now constructor.
    }
    split.
    {
      intros. exists σ.
      split. easy. constructor.
    }
    assert (Inv last_wrt x1 t ρs).
    {
      destruct H. psimpl.
      ddestruct H2. psimpl.
      ddestruct H7.
      2:{
        unfold RegCond in H2. psimpl.
        destruct m1. 2: easy.
        exfalso. apply (resp_own0 i).
        exists i0, x2. split. easy.
        rewrite <-x0. simpl.
        now left.
      }
      constructor.
      {
        intros.
        rewrite <-und_def0.
        dec_eq_nats i0 i.
        { now rewrite <-x0, <-x at 1. }
        { now rewrite H6. }
      }
      { easy. }
      { easy. }
      {
        intros.
        dec_eq_nats i0 i.
        {
          setoid_rewrite <-x.
          intros ?. psimpl.
          destruct H10.
          now ddestruct H10.
          easy.
        }
        { now setoid_rewrite H6. }
      }
      { easy. }
      { easy. }
      { easy. }
    }
    split.
    {
      exists last_wrt, x1.
      split. easy.
      split. easy.
      split. easy.
      destruct H.
      now apply resp_write0.
    }
    {
      intros ???.
      eapply Inv_eqv in H10.
      2: exact H. psimpl.
      exists last_wrt, d.
      split. constructor. easy.
    }
  }
  intros [].
  {
    unfold Commit.
    intros. do 2 psimpl.
    rename x into last_wrt.
    rename x0 into x.
    ddestruct H2. psimpl.
    ddestruct H9; psimpl.
    2:{
      clear - H x1. exfalso.
      destruct H. psimpl.
      specialize (und_def0 i).
      now rewrite <-x1 in und_def0.
    }
    2:{
      clear - H x1. exfalso.
      destruct H. psimpl.
      specialize (und_def0 i).
      now rewrite <-x1 in und_def0.
    }
    ddestruct H6.
    assert (H' := H).
    destruct x0, H. psimpl.
    clear H11 H10 H9 H7 H2 H1 H0.
    pose (und_vals1 :=
      updf und_vals0 i (MkReg (Some v) true)).
    pose (rets_map1 :=
      updf rets_map0 i (PRetn v (Some (insert v (collect und_vals0))))).
    assert (Heq : collect und_vals1 = insert v (collect und_vals0)).
    {
      subst und_vals1.
      unfold updf. set_ext v0.
      split; intros; psimpl.
      {
        dec_eq_nats x0 i.
        {
          rewrite eqb_id in H.
          ddestruct H. now left.
        }
        {
          rewrite eqb_nid in H; auto.
          right. now exists x0.
        }
      }
      {
        destruct H; psimpl.
        { exists i. now rewrite eqb_id. }
        {
          dec_eq_nats x0 i.
          { now rewrite H5 in H. }
          exists x0. now rewrite eqb_nid.
        }
      }
    }
    decide_prop (v ∈ collect und_vals0).
    {
      admit.
    }
    rename H into v_nin.
    assert ( IH : 
      Inv
        (Some i)
        (MkD und_vals1 rets_map1)
        t
        (λ σ,
          ∃ dσ,
          (∀ i0, PossDef (Some i) und_vals1 (rets_map1 i0) (dσ i0)) /\
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
          { now rewrite eqb_id, <-x at 1. }
          { rewrite eqb_nid, <-und_def0, H8 at 1; auto. }
        }
        { easy. }
        {
          unfold updf. intros.
          dec_eq_nats i0 i.
          {
            rewrite eqb_id in H.
            ddestruct H.
            destruct H0.
            {
              subst. exists i.
              now rewrite eqb_id.
            }
            {
              psimpl.
              dec_eq_nats x0 i.
              { now rewrite H5 in H. }
              exists x0. now rewrite eqb_nid.
            }
          }
          {
            rewrite eqb_nid in H; auto.
            eapply vi_subs0 in H0. 2: exact H.
            destruct H0. dec_eq_nats x0 i.
            { now rewrite H5 in H0. }
            exists x0. now rewrite eqb_nid.
          }
        }
        {
          intros ??. psimpl.
          dec_eq_nats i0 i.
          { now rewrite <-x in H0 at 1. }
          {
            eapply resp_own0.
            exists x0, x2.
            split. exact H.
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
            now exists x0, x2.
          }
        }
        {
          exists v. split.
          { unfold updf. now rewrite eqb_id. }
          {
            unfold updf. intros.
            dec_eq_nats i0 i.
            {
              rewrite eqb_id in H.
              ddestruct H. now rewrite <-Heq.
            }
            {
              rewrite eqb_nid in H; auto.
              eapply vi_subs0 in H.
              2: exact H0. easy.
            }
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
        repeat f_equal. set_ext y.
        split; intros; psimpl.
        {
          destruct H; psimpl.
          { exists i. now rewrite eqb_id. }
          {
            exists x0.
            dec_eq_nats x0 i.
            { now rewrite H5 in H. }
            { now rewrite eqb_nid, H. }
          }
        }
        {
          dec_eq_nats x0 i.
          {
            rewrite eqb_id in *.
            simpl in *. ddestruct H0.
            now left.
          }
          {
            rewrite eqb_nid in *; auto.
            right. now exists x0.
          }
        }
      }
    }
    exists (λ σ,
      ∃ dσ,
        (∀ i0, PossDef (Some i) und_vals1 (rets_map1 i0) (dσ i0)) /\
        σ = conPoss und_vals1 dσ).
    split.
    {
      psimpl. eexists _, _.
      split. 2: easy. intros.
      eapply PS_refl with (d:= MkD und_vals1 rets_map1).
      exact H.
    }
    split.
    {
      lock IH.
      intros. psimpl.
      rename x0 into σ.
      cut (
        ∃ ρ,
          (∀ i0, PossDef last_wrt und_vals0 (rets_map0 i0) (ρ i0)) /\
          PossSteps (conPoss und_vals0 ρ) (conPoss und_vals1 σ)
      ).
      {
        intros. psimpl.
        eexists. split. 2: exact H1.
        eexists. split. 2: easy.
        easy.
      }
      pose (rp j :=
        match σ j with
        | PRetn w (Some ws) => 
          if classicT (PossDef last_wrt und_vals0 (rets_map0 j) (PRetn w (Some ws))) then
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
          ddestruct H; rewrite <-x2, <-x;
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
              if classicT (PossDef last_wrt und_vals0 (rets_map0 j) (PRetn w (Some ws))) then
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
        rewrite H0. clear H0 rp.
        cut (
          ∀ n,
            (∀ m, n = S m -> m < T) ->
            PossSteps
              (conPoss und_vals1 (rp' n))
              (conPoss und_vals1 σ)
        ).
        {
          intros. apply H0.
          intros. rewrite H2.
          lia.
        }
        intros.
        induction n.
        {
          rewrite H1.
          constructor.
        }
        {
          assert (n < T)
            by now apply H0.
          pose (nt := exist (λ i, i < T) n H2).
          remember (σ nt). unfold RRet' in r.
          dstr_rposs.
          {
            decide_prop (PossDef last_wrt und_vals0 (rets_map0 nt) (PRetn a (Some s1))).
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
                  apply pr1_neq in H7. subst nt.
                  destruct j. simpl in *. lia.
                }
              }
              rewrite H7. apply IHn.
              intros. lia.
            }
            {
              decide_prop (v ∈ s1).
              {
                rename H7 into v_in.
                clear H1. specialize (H nt).
                rewrite <-Heqr in H.
                ddestruct H.
                assert (s1 = insert v (collect und_vals0)).
                {
                  rewrite <-Heq.
                  specialize (H i eq_refl). psimpl.
                  unfold updf in H. rewrite eqb_id in H.
                  ddestruct H. now apply H9.
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
                  destruct j. simpl in *. rename x2 into j.
                  assert (j = n) by lia. subst. subst nt.
                  exfalso. apply H9. repeat f_equal.
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
                      try easy. subst nt. simpl in *. lia.
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
            rewrite H6. apply IHn.
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
            rewrite H6. apply IHn.
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
            rewrite H6. apply IHn.
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
            rewrite H6. apply IHn.
            intros. lia.
          }
        }
      }
    }
    split.
    { now exists (MkD und_vals1 rets_map1), (λ i, val (und_vals1 i) ≠ None). }
    {
      intros ??.
      eapply Inv_eqv in H0.
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
Admitted.

Lemma fill_new_correct {T A} (i : Name T) (v : A) (x : loop_st A) :
  x.(new) = emp ->
  VerifyProg i (Rely i) (Guar i)
    (λ _ _ s ρs,
      ∃ d vi,
        Inv d s ρs /\
        (∀ i, vi i -> (d.(und_vals) i).(val) ≠ None) /\
        d.(rets_map) i = PRetn v (Some (λ v, ∃ i, vi i /\ (und_vals d i).(val) = Some v)))
    (fill_new T x)
    (λ '(tt, y) _ _ s ρs,
      ∃ d vi,
        Inv d s ρs /\
        (∀ i, vi i -> (d.(und_vals) i).(val) ≠ None) /\
        d.(rets_map) i = PRetn v (Some (λ v, ∃ i, vi i /\ (und_vals d i).(val) = Some v)) /\
        (λ v, ∃ i, vi i /\ (und_vals d i).(val) = Some v) ⊆ y.(new) /\
        y.(new) ⊆ collect d.(und_vals)).
Proof.
  intros Heq.
  unfold fill_new, runStateM, bindM.
  simpl.
  eapply weakenPost.
  eapply weakenPrec.
  apply lemRange with
    (I:=λ n y _ _ s ρs,
      ∃ d vi,
        Inv d s ρs /\
        (∀ i, vi i -> (d.(und_vals) i).(val) ≠ None) /\
        rets_map d i = PRetn v (Some (λ v, ∃ i, vi i /\ (und_vals d i).(val) = Some v)) /\
        (λ v1, ∃ i0, vi i0 /\ `i0 ≥ n ∧ val (und_vals d i0) = Some v1) ⊆ new y /\
        new y ⊆ collect (und_vals d)).
  2:{
    unfold sub, subRelt.
    intros. psimpl.
    exists x0, x1.
    split. easy.
    split. easy.
    split. easy.
    split.
    {
      intros ??.
      destruct H2, H2, H3.
      destruct x2. psimpl.
      lia.
    }
    {
      rewrite Heq.
      now intros ??.
    }
  }
  2:{
    intros [[]].
    unfold sub, subRelt.
    intros. psimpl.
    exists x0, x1.
    split. easy.
    split. easy.
    split. easy.
    split.
    {
      intros ??.
      destruct H4, H4.
      apply H2. exists x2.
      repeat split; (easy || lia).
    }
    { easy. }
  }
  {
    clear.
    intros.
    unfold runStateM.
    unfold lift.
    eapply lemBind with
      (Q:=λ '(r, s) _ _ s0 ρs,
        ∃ d vi,
          Inv d s0 ρs /\
          (∀ i, vi i -> (d.(und_vals) i).(val) ≠ None) /\
          rets_map d i = PRetn v (Some (λ v, ∃ i, vi i /\ (und_vals d i).(val) = Some v)) /\
          (λ v1, ∃ i0, vi i0 /\ `i0 ≥ S n ∧ val (und_vals d i0) = Some v1) ⊆ new s /\
          new s ⊆ collect (und_vals d) /\
          match r.(val) with
          | Some w => (d.(und_vals) (exist _ n p)) = r
          | None => ¬vi (exist _ n p)
          end).
    {
      unfold lift.
      eapply lemBind.
      {
        eapply lemCallWk with
          (Q:=λ s0 ρs,
            ∃ d vi,
              Inv d s0 ρs /\
              (∀ i, vi i -> (d.(und_vals) i).(val) ≠ None) /\
              rets_map d i = PRetn v (Some (λ v, ∃ i, vi i /\ (und_vals d i).(val) = Some v)) /\
              (λ v1, ∃ i0, vi i0 /\ `i0 ≥ S n ∧ val (und_vals d i0) = Some v1) ⊆ new s /\
              new s ⊆ collect (und_vals d))
          (S:=λ r s0 ρs,
            ∃ d vi,
              Inv d s0 ρs /\
              (∀ i, vi i -> (d.(und_vals) i).(val) ≠ None) /\
              rets_map d i = PRetn v (Some (λ v, ∃ i, vi i /\ (und_vals d i).(val) = Some v)) /\
              (λ v1, ∃ i0, vi i0 /\ `i0 ≥ S n ∧ val (und_vals d i0) = Some v1) ⊆ new s /\
              new s ⊆ collect (und_vals d) /\
              match r.(val) with
              | Some w => (d.(und_vals) (exist _ n p)) = r
              | None => ¬vi (exist _ n p)
              end
            )
        .
        {
          unfold
            Stable, stablePrec,
            sub, subPrec.
          intros. psimpl.
          apply H0 in H. psimpl.
          exists x3, x2.
          split. easy.
          split.
          {
            intros.
            apply H1 in H6.
            remember (und_vals x1 i0).
            destruct r, val0. simpl in *.
            eapply forget_othr, one_shot in H.
            2: now rewrite <-Heqr at 1.
            now rewrite <-H, <-Heqr.
            easy.
          }
          split.
          {
            assert (
              (λ v, ∃ i, x2 i /\ val (und_vals x1 i) = Some v) =
              (λ v, ∃ i, x2 i /\ val (und_vals x3 i) = Some v)
            ).
            {
              set_ext y.
              split; intros; psimpl.
              {
                assert (H6' := H6).
                apply H1 in H6.
                remember (und_vals x1 x4).
                destruct r. simpl in *. destruct val0.
                2: easy. ddestruct H7.
                eapply forget_othr, one_shot in H.
                2: now rewrite <-Heqr.
                exists x4. rewrite <-H.
                now rewrite <-Heqr.
              }
              {
                assert (H6' := H6).
                apply H1 in H6.
                remember (und_vals x1 x4).
                destruct r. simpl in *. destruct val0.
                2: easy. ddestruct H7.
                eapply forget_othr, one_shot in H.
                2: now rewrite <-Heqr.
                exists x4.
                split. easy.
                rewrite <-H in x.
                rewrite <-Heqr in x.
                simpl in *. ddestruct x.
                now rewrite <-Heqr.
              }
            }
            erewrite <-Inv_pres_self.
            setoid_rewrite <-H6. exact H2.
            easy.
          }
          split.
          {
            intros ??.
            destruct H6, H6, H7.
            apply H3.
            exists x4.
            split. easy.
            split. easy.
            apply H1 in H6.
            remember (und_vals x1 x4).
            destruct r, val0. simpl in *.
            eapply forget_othr, one_shot in H.
            2: now rewrite <-Heqr at 1.
            rewrite <-H, <-Heqr in H8.
            now ddestruct H8.
            easy.
          }
          {
            intros.
            apply H4 in H6.
            destruct H6. exists x4.
            eapply forget_othr, one_shot in H.
            2: exact H6. now rewrite <-H.
          }
        }
        {
          unfold
            Stable, stablePrec,
            sub, subPrec.
          intros. psimpl. rename H5 into pr.
          apply H0 in H. psimpl.
          exists x3, x2.
          split. easy.
          split.
          {
            intros.
            apply H1 in H6.
            remember (und_vals x1 i0).
            destruct r, val0. simpl in *.
            eapply forget_othr, one_shot in H.
            2: now rewrite <-Heqr at 1.
            now rewrite <-H, <-Heqr.
            easy.
          }
          split.
          {
            assert (
              (λ v, ∃ i, x2 i /\ val (und_vals x1 i) = Some v) =
              (λ v, ∃ i, x2 i /\ val (und_vals x3 i) = Some v)
            ).
            {
              set_ext y.
              split; intros; psimpl.
              {
                assert (H6' := H6).
                apply H1 in H6.
                remember (und_vals x1 x4).
                destruct r. simpl in *. destruct val0.
                2: easy. ddestruct H7.
                eapply forget_othr, one_shot in H.
                2: now rewrite <-Heqr.
                exists x4. rewrite <-H.
                now rewrite <-Heqr.
              }
              {
                assert (H6' := H6).
                apply H1 in H6.
                remember (und_vals x1 x4).
                destruct r. simpl in *. destruct val0.
                2: easy. ddestruct H7.
                eapply forget_othr, one_shot in H.
                2: now rewrite <-Heqr.
                exists x4.
                split. easy.
                rewrite <-H in x.
                rewrite <-Heqr in x.
                simpl in *. ddestruct x.
                now rewrite <-Heqr.
              }
            }
            erewrite <-Inv_pres_self.
            setoid_rewrite <-H6. exact H2.
            easy.
          }
          split.
          {
            intros ??.
            destruct H6, H6, H7.
            apply H3.
            exists x4.
            split. easy.
            split. easy.
            apply H1 in H6.
            remember (und_vals x1 x4).
            destruct r, val0. simpl in *.
            eapply forget_othr, one_shot in H.
            2: now rewrite <-Heqr at 1.
            rewrite <-H, <-Heqr in H8.
            now ddestruct H8.
            easy.
          }
          split.
          {
            intros.
            apply H4 in H6.
            destruct H6. exists x4.
            eapply forget_othr, one_shot in H.
            2: exact H6. now rewrite <-H.
          }
          {
            destruct v0, val0; psimpl.
            eapply forget_othr, Inv_mono'' in H.
            2: now rewrite pr at 1. 2: easy.
            now rewrite <-H.
          }
        }
        {
          unfold Commit.
          intros. do 2 psimpl.
          ddestruct H2. psimpl.
          ddestruct H10.
          2:{
            unfold RegCond in H7.
            psimpl. now destruct m1.
          }
          clear H12 H11 H8 H7 H2 H1 H0.
          exists ρs.
          split.
          {
            destruct H. psimpl.
            exists (conPoss x1.(und_vals) x1.(rets_map)).
            exists x1.(rets_map). split. 2: easy.
            intros. apply PS_refl, vi_subs0.
          }
          split.
          {
            intros. exists σ.
            split. easy. constructor.
          }
          assert (Inv x1 t ρs).
          {
            destruct H.
            constructor; psimpl; auto.
            {
              intros.
              specialize (und_def0 i0).
              dec_eq_nats i0 (exist (λ i, i < T) n p).
              { now rewrite <-x, <-und_def0, <-x0 at 1. }
              { now rewrite H9. }
            }
            {
              intros ??. psimpl.
              dec_eq_nats i0 (exist (λ i, i < T) n p).
              {
                rewrite <-x in H0 at 1.
                psimpl. destruct H0. 2: easy.
                ddestruct H0.
              }
              {
                apply (resp_own0 i0).
                exists x3, x4.
                now rewrite <-H9.
              }
            }
          }
          split.
          { now exists x1, x2. }
          {
            intros ??.
            eapply Inv_eqv in H1.
            2: exact H. psimpl.
            exists d. split.
            constructor. easy.
          }
        }
        {
          unfold Commit.
          intros. do 2 psimpl.
          clear H10 H9 H8 H7 H1 H0.
          ddestruct H2. psimpl. ddestruct H8.
          2:{
            exfalso.
            destruct H.
            specialize (und_def0 (exist _ n p)).
            now rewrite <-x2 in und_def0 at 1.
          }
          2:{
            exfalso.
            destruct H.
            specialize (und_def0 (exist _ n p)).
            now rewrite <-x2 in und_def0 at 1.
          }
          ddestruct H1.
          exists ρs.
          split.
          {
            destruct H. psimpl.
            exists (conPoss x1.(und_vals) x1.(rets_map)).
            exists x1.(rets_map). split. 2: easy.
            intros. apply PS_refl, vi_subs0.
          }
          split.
          {
            intros. exists σ.
            split. easy. constructor.
          }
          assert (Inv x1 t ρs).
          {
            destruct H.
            constructor; psimpl; auto.
            {
              intros.
              specialize (und_def0 i0).
              dec_eq_nats i0 (exist (λ i, i < T) n p).
              { now rewrite <-x, <-und_def0, <-x2 at 1. }
              { now rewrite H7. }
            }
            {
              intros ??. psimpl.
              dec_eq_nats i0 (exist (λ i, i < T) n p).
              {
                rewrite <-x in H1 at 1.
                psimpl. destruct H1.
              }
              {
                apply (resp_own0 i0).
                exists x3, x4.
                now rewrite <-H7.
              }
            }
          }
          split.
          {
            exists x1, x0.
            split. easy.
            split. easy.
            split. easy.
            split. easy.
            split. easy.
            destruct t0, val0; psimpl.
            {
              destruct H.
              specialize (und_def0 (exist _ n p)).
              rewrite <-x2 in und_def0 at 1. psimpl.
              ddestruct und_def0. now rewrite <-x.
            }
            {
              intros ?.
              apply H3 in H2.
              destruct H.
              specialize (und_def0 (exist _ n p)).
              rewrite <-x2 in und_def0 at 1. psimpl.
              ddestruct und_def0. now rewrite <-x in H2.
            }
          }
          {
            intros ??.
            eapply Inv_eqv in H2.
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
        exists x, x0.
        split. easy.
        split. easy.
        split. easy.
        split.
        {
          intros ??.
          destruct H5, H5, H6.
          dec_eq_nats (`x1) n.
          {
            assert (exist _ (`x1) p = x1).
            {
              destruct x1. psimpl. f_equal.
              apply proof_irrelevance.
            }
            rewrite H8 in H4.
            rewrite H4 in H7.
            psimpl. ddestruct H7.
            now left.
          }
          {
            right.
            apply H2.
            exists x1.
            split. easy.
            split. lia.
            easy.
          }
        }
        {
          intros.
          destruct H5; psimpl.
          {
            exists (exist _ n p).
            now rewrite H4.
          }
          { now apply H3. }
        }
      }
      {
        apply lemRet.
        intros ?????. psimpl.
        exists x, x0.
        split. easy.
        split. easy.
        split. easy.
        split.
        {
          intros ??.
          destruct H5, H5, H6.
          assert (`x1 ≠ n).
          {
            intros ?. subst.
            apply H4.
            assert (exist _ (`x1) p = x1).
            {
              destruct x1. psimpl. f_equal.
              apply proof_irrelevance.
            }
            now rewrite H8.
          }
          apply H2. exists x1.
          split. easy.
          split. lia.
          easy.
        }
        { easy. }
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
          ∃ vi new,
            r = Some new /\
            d.(rets_map) i = PRetn v (Some vi) /\
            vi ⊆ new /\
            new ⊆ collect d.(und_vals)
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
              { intros. apply PS_refl, vi_subs0. }
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
        destruct H. psimpl.
        exists (conPoss x1.(und_vals) x1.(rets_map)).
        exists x1.(rets_map). split. 2: easy.
        intros. apply PS_refl, vi_subs0.
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
        constructor; simpl.
        { now setoid_rewrite <- H7. }
        { easy. }
        { easy. }
        { now setoid_rewrite <-H7. }
        { easy. }
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
        destruct H. psimpl.
        exists (conPoss x.(und_vals) x.(rets_map)).
        exists x.(rets_map). split. 2: easy.
        intros. apply PS_refl, vi_subs0.
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
        constructor; simpl.
        { now setoid_rewrite <- H7. }
        { easy. }
        { easy. }
        { now setoid_rewrite <-H7. }
        { easy. }
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
        destruct H3. psimpl.
        exists (conPoss x1.(und_vals) x1.(rets_map)).
        exists x1.(rets_map). split. 2: easy.
        intros. apply PS_refl, vi_subs0.
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
        ddestruct H3. simpl in *.
        constructor.
        {
          intros.
          specialize (und_def0 i0).
          rewrite <-und_def0.
          dec_eq_nats i0 i.
          { now rewrite <-x0, <-x at 1. }
          { now rewrite H2. }
        }
        { easy. }
        { easy. }
        {
          intros ??. psimpl.
          dec_eq_nats i0 i.
          {
            rewrite <-x in H1 at 1.
            simpl in *. destruct H1.
            now ddestruct H1. easy.
          }
          {
            apply (resp_own0 i0).
            exists x2, x3.
            now rewrite <-H2.
          }
        }
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
        ddestruct H6; simpl in *.
        2:{
          clear - H3 x1. exfalso.
          destruct H3. psimpl.
          specialize (und_def0 i).
          now rewrite <-x1 in und_def0.
        }
        ddestruct H1.
        2:{
          clear - H3 x1. exfalso.
          destruct H3. psimpl.
          specialize (und_def0 i).
          now rewrite <-x1 in und_def0.
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
            clear - x1 H3 H4.
            destruct H3. psimpl.
            pose (ρ := conPoss x0.(und_vals) x0.(rets_map)).
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
              apply PS_refl, vi_subs0.
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
                replace c with (λ i, (x0.(und_vals) i).(ran)).
                2:{
                  clear - Heqp.
                  unfold conPoss in Heqp.
                  now ddestruct Heqp.
                }
                replace vs with (collect x0.(und_vals)).
                2:{
                  clear - Heqp.
                  unfold conPoss in Heqp.
                  now ddestruct Heqp.
                }
                constructor.
                {
                  specialize (und_def0 i).
                  rewrite <-x1 in und_def0.
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
                replace c with (λ i, (x0.(und_vals) i).(ran)).
                2:{
                  clear - Heqp.
                  unfold conPoss in Heqp.
                  now ddestruct Heqp.
                }
                replace vs with (collect x0.(und_vals)).
                2:{
                  clear - Heqp.
                  unfold conPoss in Heqp.
                  now ddestruct Heqp.
                }
                {
                  specialize (und_def0 i).
                  rewrite <-x1 in und_def0.
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
            exists x2.
            split. easy.
            eapply erase_vis.
            exact H10.
          }
          destruct x0. psimpl.
          assert (
            Inv (MkD und_vals0 (updf rets_map0 i (PRetn v None))) t
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
              { now rewrite <-x1, <-x at 1. }
              { now rewrite H5. }
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
                  clear - H3 und_def0 x1 x0.
                  specialize (und_def0 i).
                  rewrite <-x1 in und_def0.
                  simpl in *. ddestruct und_def0.
                  now rewrite <-x in H3.
                }
                ddestruct H19.
                exists (updf x2 i (PRetn v None)).
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
                    rewrite <-x3 in x4.
                    now ddestruct x4.
                  }
                  {
                    extensionality j.
                    dec_eq_nats j i.
                    { now rewrite eqb_id, H21. }
                    {
                      rewrite <-x3 in x4. ddestruct x4.
                      now rewrite eqb_nid, H22, H12.
                    }
                  }
                  { rewrite <-x3 in x4. now ddestruct x4. }
                  {
                    rewrite <-x3 in x4.
                    ddestruct x4.
                    extensionality j.
                    dec_eq_nats j i.
                    { now rewrite eqb_id. }
                    { now rewrite eqb_nid, H25, H17. }
                  }
                  {
                    rewrite <-x3 in x4.
                    ddestruct x4.
                    extensionality j.
                    dec_eq_nats j i.
                    { now rewrite eqb_id. }
                    { now rewrite eqb_nid, H26, H18. }
                  }
                }
              }
              {
                exists (conPoss und_vals0 (updf x0 i (PWait v))).
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
                  remember (conPoss und_vals0 (updf x0 i (PWait v))).
                  destruct p, PState.
                  assert (
                    conPoss und_vals0 x0 =
                    comRetPoss i
                      (comInvPoss i
                        (conPoss und_vals0 (updf x0 i (PWait v)))
                        (WriteSnap v)
                        (SnapDef vs (updf m i (Some v)) c)
                      )
                      (WriteSnap v)
                      (SnapDef vs m c)
                      None
                  ).
                  {
                    assert (x0 i = PRetn v None).
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
                      rewrite <-x1 in und_def0.
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
                      rewrite <-x1 in und_def0.
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
              { now rewrite <-x in H3 at 1. }
              {
                rewrite H5 in H3; auto.
                apply (resp_own0 i0).
                now exists x0, x2.
              }
            }
            { easy. }
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
            destruct H3. psimpl.
            exists (conPoss x0.(und_vals) x0.(rets_map)).
            exists x0.(rets_map).
            split. 2: easy. intros.
            apply PS_refl, vi_subs0.
          }
          split.
          {
            intros. exists σ.
            split. easy. constructor.
          }
          assert (Inv x0 t ρs).
          {
            clear - H3 x x1 H5.
            destruct H3. psimpl.
            constructor; simpl.
            {
              intros.
              dec_eq_nats i0 i.
              { now rewrite <-und_def0, <-x1, <-x at 1. }
              { now rewrite H5. }
            }
            { easy. }
            { easy. }
            {
              intros ??. psimpl.
              dec_eq_nats i0 i.
              { now rewrite <-x in H0 at 1. }
              {
                rewrite H5 in H0; auto.
                apply (resp_own0 i0).
                now exists x2, x3.
              }
            }
            { easy. }
          }
          split.
          {
            split. easy.
            exists x0.
            split. easy.
            split. easy.
            clear - H3 x1.
            destruct H3. psimpl.
            specialize (und_def0 i).
            rewrite <-x1 in und_def0.
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
      { now apply fill_new_correct. }
      intros [[]].
      eapply weakenPrec with
        (P:=λ _ _ s ρs,
          ∃ d vi,
            Inv d s ρs /\
            (∀ i, vi i -> val (d.(und_vals) i) ≠ None) /\
            d.(rets_map) i = PRetn v (Some (λ v, ∃ i, vi i /\ val (d.(und_vals) i) = Some v))).
      eapply lemBind.
      {
        simpl.
        eapply lemWhile with
          (Q:=λ y _ _ s ρs,
            ∃ d vi,
              Inv d s ρs /\
              (∀ i, vi i -> val (d.(und_vals) i) ≠ None) /\
              d.(rets_map) i = PRetn v (Some (λ v, ∃ i, vi i /\ val (d.(und_vals) i) = Some v)) /\
              (λ v, ∃ i, vi i /\ val (d.(und_vals) i) = Some v) ⊆ y.(new) /\
              y.(new) ⊆ collect d.(und_vals))
          (S:=λ _ _ s ρs,
            ∃ d vi,
              Inv d s ρs /\
              (∀ i, vi i -> val (d.(und_vals) i) ≠ None) /\
              d.(rets_map) i = PRetn v (Some (λ v, ∃ i, vi i /\ val (d.(und_vals) i) = Some v))).
        {
          unfold
            Stable, stableRelt,
            sub, subRelt.
          intros. psimpl.
          apply H0 in H. psimpl.
          exists x3, x2.
          split. easy.
          split.
          {
            intros.
            apply H1 in H4.
            remember (und_vals x1 i0).
            destruct r, val1. 2: easy.
            eapply forget_othr, Inv_mono'' in H.
            2:{ symmetry. now rewrite <-Heqr. }
            now rewrite <-H, <-Heqr.
          }
          {
            assert (∀ i, x2 i -> (und_vals x3 i).(val) = (und_vals x1 i).(val)).
            {
              intros. apply H1 in H4.
              remember (und_vals x1 i0).
              destruct r, val1; try easy. simpl in *.
              eapply forget_othr, one_shot in H.
              2: now rewrite <-Heqr.
              now rewrite <-H, <-Heqr.
            }
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
            erewrite <-Inv_pres_self.
            2: exact H. rewrite H2.
            now rewrite H5.
          }
        }
        {
          unfold SilentStep.
          intros. psimpl.
          assert (Inv x2 (tht, s) ρs).
          {
            destruct H.
            now constructor.
          }
          split.
          { now exists x2, x3. }
          {
            intros ??.
            eapply Inv_eqv in H7.
            2: exact H. subst.
            exists d. split.
            constructor. easy.
          }
        }
        {
          unfold sub, subRelt.
          intros. psimpl.
          now exists x2, x3.
        }
        {
          intros.
          unfold bindM, get, put.
          do 2 rewrite ret_lunit.
          simpl.
          eapply weakenPrec.
          eapply weakenPost.
          apply fill_new_correct.
          { easy. }
          {
            intros [[]] ?????. psimpl.
            exists x0, x1.
            split. easy.
            split. exact H0.
            split. exact H1.
            easy.
          }
          {
            intros ?????. psimpl.
            now exists x0, x1.
          }
        }
      }
      {
        intros [[]].
        unfold bindM, get.
        rewrite ret_lunit.
        simpl. apply lemRet.
        unfold sub, subRelt.
        intros. psimpl. exists x.
        split. easy. right.
        now exists (λ v, ∃ i, x0 i /\ val (und_vals x i) = Some v), l0.(new).
      }
      {
        unfold sub, subRelt.
        intros. psimpl.
        now exists x, x0.
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
    { intros ??. now psimpl. }
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