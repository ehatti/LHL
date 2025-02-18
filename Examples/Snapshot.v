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
  Unicode.Utf8.

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

Definition RRet (T : nat) (A : Type) :=
  option (A * option (option (option (set A)))).

Definition RPoss (T : nat) (A : Type) :=
  Name T -> RRet T A.
Notation PIdle := (None : RRet _ _).
Notation PWait v := (Some (v, None) : RRet _ _).
Notation PCall v := (Some (v, Some None) : RRet _ _).
Notation PRetn v vs := (Some (v, Some (Some vs))).

Definition RPossSet (T : nat) (A : Type) :=
  RPoss T A -> Prop.

Record pdata {T A} := MkD {
  und_vals : Index T -> reg_st A;
  poss_set : RPossSet T A;
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

(* global invariant, should always hold *)
Record Inv {T A}
  {d : pdata T A}
  {s : InterState (F A) (VE T A)} {ρs : PossSet (VF T A)}
: Prop := {
  und_def :
    ∀ i, (arrSt s i).(racy_val) = Some (d.(und_vals) i);
  ovr_def :
    ρs = (λ ρ,
      ∃ dρ, dρ ∈ d.(poss_set) /\
        ρ = conPoss d.(und_vals) dρ
    )
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
| SnapInvoke v s (ρs : RPossSet T A) :
  (∀ ρ, ρs ρ ->
    ρ i = PIdle) ->
  SnapTran
    (MkD s ρs)
    (MkD s (λ σ, ∃ ρ, ρs ρ /\
      updt ρ σ i PIdle (PWait v)))
| SnapReturn v vs s ρs :
  SnapTran
    (MkD s ρs)
    (MkD s (λ σ, ∃ ρ, ρs ρ /\
      updt ρ σ i (PRetn v vs) None))
| SnapNoOp d :
  SnapTran d d
| SnapFail s v ρs :
  SnapTran
    (MkD s ρs)
    (MkD s (λ σ, ∃ ρ, ρs ρ /\
      updt ρ σ i (PCall v) (PRetn v None)))
| SnapWrite (s : Index T -> reg_st A) v s ρs :
  s i = MkReg None false ->
  SnapTran
    (MkD s ρs)
    (MkD
      (updf s i (MkReg (Some v) true))
      (λ σ, ∃ ρ, ρs ρ /\
        ∀ i,
          match ρ i with
          | None =>
            (* PIdle -> PIdle *)
            σ i = None
          | Some (w, None) =>
            (* PWait -> PWait *)
            σ i = Some (w, None)
          | Some (w, Some None) =>
            (* PCall -> PCall \/ PRetn *)
            σ i = PCall w \/
            σ i = PRetn w (Some (insert v (collect s)))
          | Some (w, Some (Some ws)) =>
            (* PRetn -> PRetn *)
            σ i = PRetn w ws
          end)).
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

(*
I think this works. The idea is that `vi` is the set of names that formed `collect s` at first write, and we know `vi` never changes because we prove `InvF` is stable. We then loop through all names `i`, and add the corresponding value to `new`. If `i` is in `vi`, then it will be ⊆ to the `new ∪ {v}` of course, and if `i` is not in `vi` then that is trivial.

`vi` is the state projected to the vals at the initial write.
*)
Record InvF {T A}
  {i : Name T}
  {vi : Name T -> option A} {v : A}
  {new : set A} {n : nat}
  {d : pdata T A}
:= {
  inter_ex :
    ∀ ρ,
      d.(poss_set) ρ ->
      ρ i = PCall v \/
      ∃ vs,
        (λ v, ∃ i, vi i = Some v) ⊆ vs /\
        vs ⊆ collect d.(und_vals) /\
        ρ i = PRetn v (Some vs);
  new_sup :
    (λ v, ∃ i, `i ≥ n /\ vi i = Some v) ⊆ new;
  vi_sub :
    ∀ i v, vi i = Some v -> (d.(und_vals) i).(val) = Some v
}.
Arguments InvF {T A} i vi v new n d.

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

Lemma InvF_stable {T A} :
  ∀ i vi v new n d d',
    @InvF T A i vi v new n d ->
    OtherSnapTrans i d d' ->
    InvF i vi v new n d'.
Proof.
  intros.
  induction H0. easy.
  apply IHclos_refl_trans_1n.
  clear IHclos_refl_trans_1n H1.
  psimpl. destruct H1.
  {
    destruct H. constructor;
    auto; simpl in *. intros.
    psimpl. apply inter_ex0 in H.
    destruct H2. destruct H.
    { left. now rewrite m_diff0. }
    {
      right. psimpl.
      exists x1.
      split. easy.
      split. easy.
      now rewrite m_diff0.
    }
  }
  {
    destruct H. constructor;
    auto; simpl in *. intros.
    psimpl. apply inter_ex0 in H.
    destruct H1. destruct H.
    { left. now rewrite m_diff0. }
    {
      right. psimpl.
      exists x1.
      split. easy.
      split. easy.
      now rewrite m_diff0.
    }
  }
  { easy. }
  {
    destruct H. constructor;
    auto; simpl in *. intros.
    psimpl. apply inter_ex0 in H.
    destruct H1. destruct H.
    { left. now rewrite m_diff0. }
    {
      right. psimpl.
      exists x1.
      split. easy.
      split. easy.
      now rewrite m_diff0.
    }
  }
  {
    destruct H. constructor;
    auto; simpl in *.
    {
      intros; psimpl.
      apply inter_ex0 in H.
      specialize (H2 i).
      destruct H; psimpl.
      {
        rewrite H in H2.
        destruct H2; auto.
        right. rewrite H2.
        exists (insert v0 (collect s0)).
        split.
        {
          intros ??. destruct H3.
          apply vi_sub0 in H3.
          right. now exists x1.
        }
        split.
        {
          intros ??.
          unfold updf.
          destruct H3.
          {
            subst. exists x0.
            now rewrite eqb_id.
          }
          {
            psimpl.
            exists x1.
            dec_eq_nats x0 x1.
            { now rewrite H1 in H3. }
            now rewrite eqb_nid.
          }
        }
        { easy. }
      }
      {
        rewrite H4 in H2.
        right. exists x1.
        split.
        { easy. }
        split.
        {
          intros ??.
          apply H3 in H5.
          destruct H5. exists x2.
          unfold updf. dec_eq_nats x0 x2.
          { now rewrite H1 in H5. }
          now rewrite eqb_nid.
        }
        { easy. }
      }
    }
    {
      intros. unfold updf.
      dec_eq_nats x0 i0.
      {
        apply vi_sub0 in H.
        now rewrite H1 in H.
      }
      rewrite eqb_nid; auto.
    }
  }
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
  subst. simpl in *.
  extensionality ρ.
  eapply equal_f with
    (x:= conPoss und_vals0 ρ)
    in ovr_def1.
  apply propositional_extensionality.
  split; intros.
  {
    assert (
      ∃ dρ, dρ ∈ poss_set0 /\
        conPoss und_vals0 ρ = conPoss und_vals0 dρ
    ) by now exists ρ.
    rewrite ovr_def1 in H0. psimpl.
    apply conPoss_inj in H1. now subst.
  }
  {
    assert (
      ∃ dρ, dρ ∈ poss_set1 /\
        conPoss und_vals0 ρ = conPoss und_vals0 dρ
    ) by now exists ρ.
    rewrite <-ovr_def1 in H0. psimpl.
    apply conPoss_inj in H1. now subst.
  }
Qed.

Lemma return_step {T A} :
  ∀ (i : Name T) (v : A) (r : option (set A)),
    ReturnStep i (Guar i)
      (λ s ρs,
        ∃ d, Inv d s ρs /\
        (
          r = None /\
          (∃ ρ, d.(poss_set) ρ) /\
          ∀ ρ, d.(poss_set) ρ ->
            ρ i = PRetn v r
        ) \/
        (
          ∃ vi new,
            r = Some new /\
            InvF i vi v new 0 d
        ))
      (WriteSnap v) r
      (λ _ _ s ρs,
        ∃ d, Inv d s ρs).
Proof.
  intros i v r s ρs H _.
  psimpl. destruct H; psimpl.
  {
    exists ρs.
    split.
    {
      clear - H H1.
      destruct H, x.
      subst. simpl in *.
      now eexists _, x0.
    }
    split.
    {
      intros. eexists.
      split. exact H0.
      constructor.
    }
    split.
    {
      intros. destruct H.
      clear - ovr_def0 H0 H2.
      subst. psimpl. simpl.
      apply H2 in H. now rewrite H.
    }
    split.
    {
      exists (MkD
        (und_vals x)
        (λ σ, ∃ ρ, x.(poss_set) ρ /\
          updt ρ σ i (PRetn v None) None)
      ).
      destruct H.
      constructor; simpl; auto.
      set_ext ρ. unfold mapRetPoss.
      split; intro; psimpl.
      {
        psimpl.
        exists (λ j,
          if i =? j then
            None
          else
            x2 j).
        split.
        {
          exists x2.
          split. easy.
          constructor.
          { now apply H2. }
          { now rewrite eqb_id. }
          { apply differ_pointwise_trivial. }
        }
        {
          unfold conPoss in *.
          destruct ρ. simpl in *.
          subst. repeat f_equal.
          {
            extensionality j.
            dec_eq_nats j i.
            {
              rewrite eqb_id.
              destruct (x2 i).
              {
                destruct p, o.
                { now destruct o. }
                { easy. }
              }
              { easy. }
            }
            { now rewrite eqb_nid. }
          }
          {
            extensionality j.
            dec_eq_nats j i.
            { now rewrite eqb_id. }
            { now rewrite eqb_nid, H6. }
          }
          {
            extensionality j.
            dec_eq_nats j i.
            { now rewrite eqb_id. }
            { now rewrite eqb_nid, H7. }
          }
        }
      }
      {
        unfold contains in H. psimpl.
        exists (conPoss (und_vals x) x2).
        split. { now exists x2. }
        destruct H0.
        rewrite m2_set0.
        split. { easy. }
        split. { simpl. now rewrite m1_set0. }
        split. { easy. }
        split. { simpl. now rewrite m1_set0. }
        split.
        {
          unfold differ_pointwise.
          simpl. intros. now rewrite m_diff0.
        }
        split.
        {
          unfold differ_pointwise.
          simpl. intros. now rewrite m_diff0.
        }
        {
          simpl. f_equal.
          extensionality j.
          dec_eq_nats j i.
          { now rewrite m1_set0, m2_set0. }
          { now rewrite m_diff0. }
        }
      }
    }
    {
      unfold Guar. intros.
      assert (x = d).
      {
        eapply Inv_eqv.
        { exact H. }
        { easy. }
      }
      subst. destruct d.
      eexists. split.
      apply SnapReturn with
        (v:=v) (vs:=None).
      simpl in *. clear - H0 H2.
      destruct H0. subst. simpl in *.
      constructor; simpl; auto.
      set_ext ρ. split;
      intros; psimpl.
      {
        unfold mapRetPoss in H0. psimpl.
        unfold conPoss in H1, H4.
        simpl in *. remember (x0 i).
        destruct r as [[? [[?|]|]]|];
        try easy. ddestruct H4. clear x.
        exists (λ j,
          if i =? j then
            None
          else
            x0 j).
        split.
        {
          exists x0.
          split. easy.
          constructor.
          { now apply H2. }
          { now rewrite eqb_id. }
          { apply differ_pointwise_trivial. }
        }
        {
          destruct ρ. unfold conPoss.
          simpl in *. subst. repeat f_equal.
          {
            extensionality j.
            dec_eq_nats j i.
            { now rewrite eqb_id, <- Heqr. }
            { now rewrite eqb_nid; auto. }
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
        destruct H, H, H0.
        exists (conPoss und_vals0 x0).
        split. now exists x0.
        assert (conPoss und_vals0 x = retPoss i (conPoss und_vals0 x0)).
        {
          unfold conPoss, retPoss.
          f_equal; simpl.
          {
            f_equal.
            extensionality j.
            dec_eq_nats j i.
            { now  rewrite m1_set0, m2_set0. }
            { now rewrite m_diff0. }
          }
          {
            extensionality j.
            dec_eq_nats j i.
            { now rewrite eqb_id, m2_set0. }
            { now rewrite eqb_nid, m_diff0. }
          }
          {
            extensionality j.
            dec_eq_nats j i.
            { now rewrite eqb_id, m2_set0. }
            { now rewrite eqb_nid, m_diff0. }
          }
        }
        rewrite H0. apply map_ret_triv.
        unfold conPoss. constructor;
        simpl; now rewrite m1_set0.
      }
    }
  }
  {
    destruct H0.
    exists
  }
Admitted.

Lemma switch_inv {T A} (i : Name T) (v : A) :
  ∀ vs new,
    Lift (InvF i vs v new 0) ==>
    Lift (InvF i vs v new T).
Proof.
  unfold sub, subPrec, Lift.
  intros. psimpl. destruct H0.
  exists x. split. easy.
  constructor; auto.
  intros. destruct H0, H0.
  clear - H0. destruct x0.
  simpl in *. lia.
Qed.

Lemma write_correct {T A} (i : Name T) (v : A) :
  VerifyProg i (Rely i) (Guar i)
    (λ _ _ s ρs,
      ∃ d,
        Inv d s ρs /\
        (∀ ρ, d.(poss_set) ρ ->
          ρ i = PWait v))
    (call (At i (Write {| val := Some v; ran := true |})))
    (λ 'tt _ _ s ρs, ∃ vs, Lift (InvF i vs v emp T) s ρs).
Proof.

Lemma fill_new_correct {T A} (i : Name T) (v : A) (x : loop_st A) :
  VerifyProg i (Rely i) (Guar i)
    (λ _ _ s ρs, ∃ vs, Lift (InvF i vs v x.(new) T) s ρs)
    (fill_new T x)
    (λ '(tt, y) _ _ s ρs, ∃ vs, Lift (InvF i vs v y.(new) 0) s ρs).
Proof.
  unfold fill_new, runStateM, bindM.
  simpl. eapply weakenPost.
  apply lemRange with
    (I:=λ n x _ _ s ρs,
      ∃ vs, Lift (InvF i vs v x.(new) n) s ρs).
  clear. 2: intros; now destruct v0, u.
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