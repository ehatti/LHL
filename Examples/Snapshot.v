From LHL.Core Require Import
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

From LHL.Examples Require Import
  SnapshotSpec
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

Definition VE T A : Spec T (E T A) :=
  tensorSpec
    nameSpec
    (arraySpec T (regSpec {| val := None; ran := false |})).

Definition F A := SnapSig A.
Definition VF T A := @snapSpec T A.

Notation valSt s i := (
  match RState (snd s) i with
  | RegDef s _ => s.(val)
  end
).

Notation oranSt ρ i := (
  match ρ.(PState) with
  | SnapDef _ _ c => c i
  end
).

Notation uranSt s i := (
  match RState (snd s) i with
  | RegDef s _ => s.(ran)
  end
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

Definition while s := NoOp (whileAux (e s)).

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

Record loop_st {A} := {
  old : set A;
  new : set A
}.
Arguments loop_st : clear implicits.

Definition fill_old {A} T : StateM (E T A) (loop_st A) unit :=
  range T (λ i,
    v <- lift (call (At i Read));'
    s <- get;'
    match v.(val) with
    | Some v => put {| old := insert v s.(old); new := s.(new)|}
    | None => retM tt
    end
  ).

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
      fill_old T;;'
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

Definition Relt T A := SRelt (VE T A) (VF T A).
Definition Prec T A := SPrec (VE T A) (VF T A).

Notation "x ⊆ y" :=
  (forall v, v ∈ x -> v ∈ y)
  (at level 40).

Record Inv {T A}
  (s : InterState (F A) (VE T A)) (ρs : PossSet (VF T A))
:= {
  snap_cons :
    ∀ ρ, ρs ρ ->
      ∀ v, (∃ i, valSt s i = Some v) <-> v ∈ snapSt ρ;
  rans_cons :
    ∀ ρ, ρs ρ ->
      ∀ i, uranSt s i = oranSt ρ i
}.

Record FillNewInv {T A} (i : Name T) (v : A) (vs : set A) (n : nat) (x : loop_st A)
  (s : InterState (F A) (VE T A)) (ρs : PossSet (VF T A))
:= {
  fn_inv : Inv s ρs;
  old_subs :
    x.(old) ⊆ vs;
  subs_new :
    (λ v, v ∈ vs /\ ∃ i, `i ≥ n /\ valSt s i = Some v) ⊆ x.(new);
  pfx_subs :
    vs ⊆ (λ v, ∃ i, valSt s i = Some v);
  poss_class :
    ∀ ρ, ρs ρ ->
      Waiting i (WriteSnap v) ρ \/ Done i (WriteSnap v) (Some vs) ρ;
  poss_wait :
    ∃ ρ, ρs ρ /\
      Waiting i (WriteSnap v) ρ;
  poss_done :
    ∃ ρ, ρs ρ /\
      Done i (WriteSnap v) (Some vs) ρ;
}.

Record Precs {T A} (i : Name T) (v : A)
  (s : InterState (F A) (VE T A)) (ρs : PossSet (VF T A))
:= {
  ps_inv : Inv s ρs;
  ps_wait : ∀ ρ, ρs ρ -> Waiting i (WriteSnap v) ρ
}.

Record Posts {T A} (i : Name T) (v : A) (r : option (set A))
  (s : InterState (F A) (VE T A)) (ρs : PossSet (VF T A))
:= {
  qs_precs_hold : Precs i v s ρs;
  qs_call_done : ∀ ρ, ρs ρ -> PCalls ρ i = CallDone (WriteSnap v);
  qs_ret_done : ∀ ρ, ρs ρ -> PRets ρ i = RetPoss (WriteSnap v) r
}.

Record Rely {T A} (i : Name T)
  (s : InterState (F A) (VE T A)) (ρs : PossSet (VF T A))
  (t : InterState (F A) (VE T A)) (σs : PossSet (VF T A))
:= {

}.

Record Guar {T A} (i : Name T)
  (s : InterState (F A) (VE T A)) (ρs : PossSet (VF T A))
  (t : InterState (F A) (VE T A)) (σs : PossSet (VF T A))
:= {

}.

Lemma fill_new_inv_stable {T A} {i : Name T} :
  ∀ v vs n x,
  Stable (Rely i) (FillNewInv (A:=A) i v vs n x).
Proof.
Admitted.

Lemma fill_old_correct {T A} (i : Name T) (v : A) (x : loop_st A) :
  VerifyProg i (Rely i) (Guar i)
    (λ _ _, Precs i v)
    (fill_old T x)
    (λ '(tt, y) _ _ s ρs, ∃ vs, FillNewInv i v vs T y s ρs).
Proof.
Admitted.

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
      { admit. }
      { admit. }
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
      (Q:=λ _ _ _, Precs i v).
    {
      admit.
    }
    intros [].
    eapply lemBind.
    {
      unfold runStateM, bindM.
      eapply lemBind.
      { apply fill_old_correct. }
      intros [[] [val' ran]].
      eapply lemBind.
      { apply fill_new_correct. }
      intros [[] [val'' ran']].
      eapply lemBind.
    }
  }