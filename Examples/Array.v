From LHL.Core Require Import
  Program
  Specs
  Logic
  LogicFacts
  Tensor
  Traces
  SingConds
  VisPoss
  UBLayer
  ProgramRules
  Linearizability.

From LHL.Util Require Import
  TransUtil
  Tactics
  Util.

From LHL.Examples Require Import
  ArraySpec.

Definition UnitSig : ESig :=
    fun _ => Empty_set.

Program Definition unitSpec {T} : Spec T UnitSig := {|
  State := unit;
  Step _ e _ := False;
  Init := tt
|}.

Next Obligation.
ddestruct H.
constructor.
easy.
Qed.

Fixpoint nsig (U : ESig) N :=
  match N with
  | 0 => UnitSig
  | S N => U |+| nsig U N
  end.

Fixpoint ntensor {T U} (V : Spec T U) N : Spec T (nsig U N) :=
  match N with
  | 0 => unitSpec
  | S N => tensorSpec V (ntensor V N)
  end.

Definition F U N := ArraySig U N.

Definition VF {T U} (V : Spec T U) N : Spec T (F U N) :=
  arraySpec N V.

From Equations Require Import Equations.
Require Import Lia.

Equations getIndex {U N R} (i : Index N) (m : U R) : nsig U N R :=
getIndex (N:= S N) (@exist _ _ 0 p) m := inl m;
getIndex (N:= S N) (@exist _ _ (S i) p) m := inr (getIndex (@exist _ _ i _) m);
getIndex (N:= 0) (@exist _ _ i p) m := _.

Next Obligation. lia. Qed.
Next Obligation. lia. Qed.

Section indexntensor.

Context {T U} {V : Spec T U}.

Equations indexntensor {N} (i : Index N) (s : (ntensor V N).(State))
  : V.(State) by wf (proj1_sig i) lt :=
indexntensor (N:= S N) (@exist _ _ 0 p) s := LState s;
indexntensor (N:= S N) (@exist _ _ (S i) p) s := indexntensor (@exist _ _ i _) (RState s);
indexntensor (N:= 0) (@exist _ _ i p) s := _.

Next Obligation. lia. Qed.
Next Obligation. lia. Qed.

Lemma le_triv {n} : 0 < S n.
Proof. lia. Qed.

Lemma le_wk {n m} : n < m -> n < S m.
Proof. lia. Qed.

Lemma le_cong {n m} : n < m -> S n < S m.
Proof. lia. Qed.

Definition activentensor N (s : (ntensor V N).(State)) (i : Name T)
: option {A & ArraySig U N A}.
generalize dependent i. generalize dependent s.
generalize dependent N. fix rec 1. intros.
destruct N.
{ exact None. }
{
  destruct (TActive s i).
  2:{ exact None. }
  {
    destruct s0, s0.
    {
      refine (Some (existT _ x _)).
      refine (At _ _).
      refine (exist _ 0 _).
      { apply le_triv. }
      { exact u. }
    }
    {
      destruct (rec N (RState s) i).
      2:{ exact None. }
      {
        destruct s0, a, i0.
        refine (Some (existT _ _ (At (exist _ (S x0) _) m))).
        { now apply le_cong. }
      }
    }
  }
}
Defined.

(* Equations activentensor N (s : (ntensor V N).(State)) (i : Name T)
  : option {A & ArraySig U N A} :=
activentensor 0 s i :=
  None;
activentensor (S N) s i with TActive s i => {
  activentensor (S N) s i None :=
    None;
  activentensor (S N) s i (Some (existT _ A (inl m))) =>
    (Some (existT _ A (At (exist _ 0 _) m)));
  activentensor (S N) s i (Some (existT _ A (inr m))) with activentensor N (RState s) i => {
    activentensor (S N) s i (Some (existT _ A (inr m))) None =>
      None;
    activentensor (S N) s i (Some (existT _ A (inr m))) (Some (existT _ _ (At (exist _ n _) tm))) =>
      Some (existT _ _ (At (exist _ (S n) _) tm))
  }
}.

Next Obligation. lia. Qed.
Next Obligation. lia. Qed. *)

End indexntensor.

Arguments activentensor {T U V N}.

Definition index {U N R} (i : Index N) (m : U R) : Prog (nsig U N) R :=
  Bind (getIndex i m)
  Return.

Definition arrayImpl {U N} : Impl (nsig U N) (ArraySig U N) :=
  fun _ m => match m with
  | At i m => index i m
  end.

Variant StRel {T U} {V : Spec T U} {N} :
  ThreadState (nsig U N) (F U N) -> PCall (F U N) -> PRet (F U N) -> Prop :=
| StIdle :
  StRel Idle CallIdle RetIdle
| StOCall i R (m : U R) :
  StRel (Cont (At i m) (index i m)) (CallPoss (At i m)) RetIdle
| StUCall i R (m : U R) :
  StRel (UCall (At i m) (getIndex i m) Return) (CallDone (At i m)) RetIdle
| StURet i R (m : U R) v :
  StRel (Cont (At i m) (Return v)) (CallDone (At i m)) (RetPoss (At i m) v).

Record Inv {T U} {V : Spec T U} {N}
  (s : InterState (F U N) (ntensor V N)) (ρ : Poss (VF V N))
:= {
  st_cons : PState ρ = MkArr (fun k => indexntensor k (snd s)) (activentensor (snd s));
  th_cons : forall i, StRel (V:=V) (fst s i) (PCalls ρ i) (PRets ρ i)
}.

Lemma Return_pres_single {U T N R} {V : Spec T U} :
  forall (m : F U N R) v i s ρ t σs,
  TReturn (VE:= ntensor V N) (VF:= VF V N) arrayImpl i m v s (eq ρ) t σs ->
  σs = eq (retPoss i ρ).
intros.
unfold TReturn, mapRetPoss in H. psimpl.
set_ext σ. split; intros; destruct_all; subst.
{
  unfold retPoss. destruct x, σ. cbn in *.
  f_equal. easy.
  extensionality j. dec_eq_nats i j.
  rewrite eqb_id. easy.
  rewrite eqb_nid, H7; easy.
  extensionality j. dec_eq_nats i j.
  rewrite eqb_id. easy.
  rewrite eqb_nid, H8; easy.
}
{
  cbn. rewrite eqb_id. exists ρ.
  destruct H0. ddestruct H0. cbn in *.
  symmetry in x0. apply H in x0.
  specialize (x0 ρ eq_refl).
  repeat split; (easy || apply differ_pointwise_trivial).
}
Qed.

Lemma Invoke_pres_single {U T N R} {V : Spec T U} :
  forall (m : F U N R) i s ρ t σs,
  TInvoke (VE:= ntensor V N) (VF:= VF V N) arrayImpl i R m s (eq ρ) t σs ->
  σs = eq (invPoss i ρ m).
intros.
unfold TInvoke in H. psimpl.
set_ext σ. split; intros; destruct_all; subst.
{
  unfold TIdle in H. destruct_all.
  specialize (H2 x eq_refl). destruct_all.
  destruct x, σ. unfold invPoss. cbn in *.
  f_equal; try easy.
  extensionality j. dec_eq_nats i j.
  rewrite eqb_id. easy.
  rewrite eqb_nid, H6; easy.
  extensionality j. dec_eq_nats i j.
  rewrite eqb_id. easy.
  rewrite eqb_nid, H7; easy.
}
{
  cbn. rewrite eqb_id. exists ρ.
  repeat split; (easy || apply differ_pointwise_trivial).
}
Qed.

Require Import Coq.Logic.ProofIrrelevance.

Lemma dpt_ext {A B} {f g : A -> B} :
  forall i,
  differ_pointwise f g i ->
  exists u,
    f = (fun j => if i =? j then f i else u j) /\
    g = (fun j => if i =? j then g i else u j).
Proof.
  intros.
  exists f.
  split.
  {
    extensionality j.
    dec_eq_nats i j.
    { now rewrite eqb_id. }
    { now rewrite eqb_nid, <- H. }
  }
  {
    extensionality j.
    dec_eq_nats i j.
    { now rewrite eqb_id. }
    { now rewrite eqb_nid, H. }
  }
Qed.

Definition str_active {T U N} (a : ActiveMap T (nsig U (S N)))
: ActiveMap T (nsig U N).
unfold ActiveMap in *.
intros i.
specialize (a i).
destruct a.
2: exact None.
destruct s. cbn in *.
destruct n.
exact None.
exact (Some (existT _ _ n)).
Defined.

Definition wk_active {T U N} (a : ActiveMap T (ArraySig U N))
: ActiveMap T (ArraySig U (S N)).
unfold ActiveMap in *.
intros i.
specialize (a i).
destruct a.
2: exact None.
destruct s.
refine (Some (existT _ x _)).
destruct a.
econstructor.
2: exact m.
unfold Index in *.
destruct i0.
exists x.
lia.
Defined.

Lemma conntensorrt_call {N T U} {V : Spec T U} :
  forall s i A (m : U A) t n,
  Step (ntensor V N) s (i, CallEv (getIndex n m)) t ->
  ArrayStep V
    (MkArr (fun k => indexntensor k s) (activentensor s))
    (i, CallEv (At n m))
    (MkArr (fun k => indexntensor k t) (activentensor t)).
Proof.
  intros.
  induction N; cbn in *. easy.
  destruct n, x; simp getIndex in *;
  psimpl.
  {
    econstructor; cbn.
    {
      assert (activentensor (N:= S N) s i = None).
      {
        clear - H0.
        destruct s. cbn in *.
        now rewrite H0.
      }
      assert (
        activentensor (N:= S N) t i =
        Some (existT _ _ (At (exist _ 0 l) m))).
      {
        clear - H1.
        destruct t. cbn in *.
        rewrite H1. repeat f_equal.
        apply proof_irrelevance.
      }
      assert (
        differ_pointwise
          (activentensor (N:= S N) s)
          (activentensor (N:= S N) t) i
      ).
      {
        unfold differ_pointwise in *.
        intros. apply H2 in H6.
        clear - H3 H6.
        unfold activentensor.
        repeat rewrite H6 at 1.
        destruct s. cbn in *.
        destruct (TActive j).
        {
          destruct s, s.
          { easy. }
          { now subst. }
        }
        { easy. }
      }
      assert (
        activentensor (N:= S N) s =
        (fun j =>
          if i =? j then
            None
          else
            activentensor (N:= S N) s j)
      ).
      {
        extensionality j.
        dec_eq_nats i j.
        { now rewrite eqb_id. }
        { now rewrite eqb_nid. }
      }
      assert (
        activentensor (N:= S N) t =
        (fun j =>
          if i =? j then
            Some (existT _ _ (At (exist _ 0 l) m))
          else
            activentensor (N:= S N) s j)
      ).
      {
        extensionality j.
        dec_eq_nats i j.
        { now rewrite eqb_id. }
        { now rewrite eqb_nid, H6. }
      }
      rewrite H7, H8.
      constructor.
    }
    { now simp indexntensor. }
    { now simp indexntensor. }
    {
      unfold differ_pointwise.
      intros. destruct j, x.
      {
        exfalso. apply H4.
        f_equal.
        apply proof_irrelevance.
      }
      {
        simp indexntensor.
        now rewrite H3 at 1.
      }
    }
    { easy. }
  }
  {
    apply IHN in H.
    clear IHN. ddestruct H.
    cbn in *. ddestruct H.
    assert (activentensor (N:= S N) s i = None).
    {
      clear - H0.
      destruct s. cbn in *.
      now rewrite H0.
    }
    assert (
      activentensor (N:= S N) t i =
      Some (existT _ _ (At (exist _ (S x0) l) m))).
    {
      unfold activentensor.
      rewrite H1 at 1.
      move x at bottom.
      apply equal_f with (x:=i) in x.
      rewrite eqb_id in x.
      rewrite <- x at 1.
      repeat f_equal.
      apply proof_irrelevance.
    }
    assert (
      differ_pointwise
        (activentensor (N:= S N) s)
        (activentensor (N:= S N) t) i
    ).
    {
      unfold differ_pointwise in *.
      intros. assert (H7' := H7).
      apply H4 in H7.
      unfold activentensor.
      repeat rewrite H7 at 1.
      destruct s. cbn in *.
      destruct (TActive j).
      {
        destruct s, s.
        { easy. }
        {
          subst. clear H H6.
          assert (
            activentensor (N:=N) (Tensor.RState t) j =
            activentensor (N:=N) RState j
          ).
          { now rewrite <- x1, <- x, eqb_nid. }
          now rewrite <- H at 1.
        }
      }
      { easy. }
    }
    assert (
      activentensor (N:= S N) s =
      (fun j =>
        if i =? j then
          None
        else
          activentensor (N:= S N) s j)
    ).
    {
      extensionality j.
      dec_eq_nats i j.
      { now rewrite eqb_id. }
      { now rewrite eqb_nid. }
    }
    assert (
      activentensor (N:= S N) t =
      (fun j =>
        if i =? j then
          Some (existT _ _ (At (exist _ (S x0) l) m))
        else
          activentensor (N:= S N) s j)
    ).
    {
      extensionality j.
      dec_eq_nats i j.
      { now rewrite eqb_id. }
      { now rewrite eqb_nid, H7. }
    }
    rewrite H8, H9.
    econstructor.
    { econstructor; cbn. }
    { cbn. now simp indexntensor. }
    { cbn. now simp indexntensor. }
    {
      cbn. unfold differ_pointwise.
      intros. destruct j, x2;
      simp indexntensor.
      { easy. }
      {
        rewrite H2. easy.
        unfold not. intros.
        apply H10. clear H10.
        ddestruct H11. f_equal.
        apply proof_irrelevance.
      } 
    }
    {
      clear - H3.
      replace (indexntensor_obligations_obligation_2 N x0 l)
      with (getIndex_obligations_obligation_2 N x0 l)
      by apply proof_irrelevance.
      easy.
    }
  }
Qed.

Lemma conntensorrt_ret {N T U} {V : Spec T U} :
  forall s i A (m : U A) v t n,
  Step (ntensor V N) s (i, RetEv (getIndex n m) v) t ->
  ArrayStep V
    (MkArr (fun k => indexntensor k s) (activentensor s))
    (i, RetEv (At n m) v)
    (MkArr (fun k => indexntensor k t) (activentensor t)).
Proof.
  intros.
  induction N; cbn in *. easy.
  destruct n, x; simp getIndex in *;
  psimpl.
  {
    econstructor; cbn.
    {
      eassert (
        activentensor (N:= S N) s i =
        Some (existT _ _ (At (exist _ 0 l) m))
      ).
      {
        clear - H0.
        destruct s. cbn in *.
        rewrite H0. repeat f_equal.
        apply proof_irrelevance.
      }
      assert (
        activentensor (N:= S N) t i = None
      ).
      {
        clear - H1.
        destruct t. cbn in *.
        now rewrite H1.
      }
      assert (
        differ_pointwise
          (activentensor (N:= S N) s)
          (activentensor (N:= S N) t) i
      ).
      {
        unfold differ_pointwise in *.
        intros. apply H2 in H6.
        clear - H3 H6.
        unfold activentensor.
        repeat rewrite H6 at 1.
        destruct s. cbn in *.
        destruct (TActive j).
        {
          destruct s, s.
          { easy. }
          { now subst. }
        }
        { easy. }
      }
      assert (
        activentensor (N:= S N) s =
        (fun j =>
          if i =? j then
            Some (existT _ _ (At (exist _ 0 l) m))
          else
            activentensor (N:= S N) s j)
      ).
      {
        extensionality j.
        dec_eq_nats i j.
        { now rewrite eqb_id. }
        { now rewrite eqb_nid. }
      }
      assert (
        activentensor (N:= S N) t =
        (fun j =>
          if i =? j then
            None
          else
            activentensor (N:= S N) s j)
      ).
      {
        extensionality j.
        dec_eq_nats i j.
        { now rewrite eqb_id. }
        { now rewrite eqb_nid, H6. }
      }
      rewrite H7, H8.
      constructor.
    }
    { now simp indexntensor. }
    { now simp indexntensor. }
    {
      unfold differ_pointwise.
      intros. destruct j, x.
      {
        exfalso. apply H4.
        f_equal.
        apply proof_irrelevance.
      }
      {
        simp indexntensor.
        now rewrite H3 at 1.
      }
    }
    { easy. }
  }
  {
    apply IHN in H.
    clear IHN. ddestruct H.
    cbn in *. ddestruct H.
    assert (
      activentensor (N:= S N) s i =
      Some (existT _ _ (At (exist _ (S x0) l) m))
    ).
    {
      unfold activentensor.
      rewrite H0 at 1.
      move x1 at bottom.
      apply equal_f with (x:=i) in x1.
      rewrite eqb_id in x1.
      rewrite <- x1 at 1.
      repeat f_equal.
      apply proof_irrelevance.
    }
    assert (
      activentensor (N:= S N) t i =
      None).
    {
      unfold activentensor.
      now rewrite H1 at 1.
    }
    assert (
      differ_pointwise
        (activentensor (N:= S N) s)
        (activentensor (N:= S N) t) i
    ).
    {
      unfold differ_pointwise in *.
      intros. assert (H7' := H7).
      apply H4 in H7.
      unfold activentensor.
      repeat rewrite H7 at 1.
      destruct s. cbn in *.
      destruct (TActive j).
      {
        destruct s, s.
        { easy. }
        {
          subst. clear H H6.
          assert (
            activentensor (N:=N) (Tensor.RState t) j =
            activentensor (N:=N) RState j
          ).
          { now rewrite <- x1, <- x, eqb_nid. }
          now rewrite <- H at 1.
        }
      }
      { easy. }
    }
    assert (
      activentensor (N:= S N) s =
      (fun j =>
        if i =? j then
          Some (existT _ _ (At (exist _ (S x0) l) m))
        else
          activentensor (N:= S N) s j)
    ).
    {
      extensionality j.
      dec_eq_nats i j.
      { now rewrite eqb_id. }
      { now rewrite eqb_nid. }
    }
    assert (
      activentensor (N:= S N) t =
      (fun j =>
        if i =? j then
          None
        else
          activentensor (N:= S N) s j)
    ).
    {
      extensionality j.
      dec_eq_nats i j.
      { now rewrite eqb_id. }
      { now rewrite eqb_nid, H7. }
    }
    rewrite H8, H9.
    econstructor.
    { econstructor; cbn. }
    { cbn. now simp indexntensor. }
    { cbn. now simp indexntensor. }
    {
      cbn. unfold differ_pointwise.
      intros. destruct j, x2;
      simp indexntensor.
      { easy. }
      {
        rewrite H2. easy.
        unfold not. intros.
        apply H10. clear H10.
        ddestruct H11. f_equal.
        apply proof_irrelevance.
      } 
    }
    {
      clear - H3.
      replace (indexntensor_obligations_obligation_2 N x0 l)
      with (getIndex_obligations_obligation_2 N x0 l)
      by apply proof_irrelevance.
      easy.
    }
  }
Qed.

Lemma sing_elem {A} {P : A -> Prop} :
  forall x : A,
  eq x = P ->
  P x.
Proof.
  intros. now rewrite <- H.
Qed.

Lemma getIndex_eq {U : ESig} {A : Type} {N : nat} :
  forall (i1 i2 : Index N),
  forall (m1 m2 : U A),
  getIndex i1 m1 = getIndex i2 m2 ->
  i1 = i2 /\ m1 = m2.
Proof.
  intros.
  funelim (getIndex i1 m1);
  simp getIndex in *.
  { easy. }
  {
    funelim (getIndex i2 m2);
    simp getIndex in *.
    {
      ddestruct H.
      split.
      {
        f_equal.
        apply proof_irrelevance.
      }
      { easy. }
    }
    { easy. }
  }
  {
    funelim (getIndex i2 m2);
    simp getIndex in *.
    { easy. }
    {
      ddestruct H1. apply H0 in x.
      psimpl. split. 2: easy.
      clear - H1. ddestruct H1.
      f_equal. apply proof_irrelevance.
    }
  }
Qed.

Lemma wk P : P -> P /\ P.
easy.
Qed.

Lemma eq_inj {A} :
  forall x y : A,
  eq x = eq y ->
  x = y.
intros. now rewrite H.
Qed.

Ltac eq_inj H := apply eq_inj in H; subst.

Theorem arrayCorrect T U N (V : Spec T U) :
  VerifyImpl (ntensor V N) (VF V N)
    (fun i => LiftSRelt (fun s ρ t σ =>
      fst s i = fst t i /\
      PCalls ρ i = PCalls σ i /\
      PRets ρ i = PRets σ i /\
      (Inv s ρ -> Inv t σ)))
    (fun i => LiftSRelt (fun s ρ t σ =>
      (forall j, i <> j -> fst s j = fst t j) /\
      (forall j, i <> j -> PCalls ρ j = PCalls σ j) /\
      (forall j, i <> j -> PRets ρ j = PRets σ j) /\
      Inv t σ))
    (fun _ _ _ => LiftSPrec Inv)
    arrayImpl
    (fun i _ m r _ _ => LiftSPrec (fun t σ =>
      Inv t σ /\
      Done i m r σ))
    (TReturn arrayImpl).
constructor.
{
  unfold LiftSRelt. intros. subst.
  now exists x.
}
{
  unfold LiftSRelt, sub, subRelt.
  intros. psimpl.
  specialize (H x eq_refl). psimpl.
  specialize (H1 x2 eq_refl). psimpl.
  exists x1. split. easy.
  split. congruence.
  split. congruence.
  split. congruence.
  intros. now apply H7, H4.
}
{
  unfold LiftSRelt, LiftSPrec, sub, subRelt.
  intros. psimpl. specialize (H0 x eq_refl).
  psimpl. exists x0. split. easy.
  split. now rewrite H1.
  split. now rewrite H2.
  split. now rewrite H3.
  easy.
}
{
  unfold sub, subRelt, InvokeAny, TInvoke.
  unfold LiftSRelt. intros. psimpl.
  exists (invPoss i x x1).
  split.
  {
    set_ext y. unfold invPoss.
    split; intros; psimpl.
    {
      destruct x2, y.
      cbn in *.
      f_equal. easy.
      {
        extensionality k.
        dec_eq_nats i k.
        { now rewrite eqb_id. }
        { now rewrite eqb_nid, H7. }
      }
      {
        extensionality k.
        dec_eq_nats i k.
        { now rewrite eqb_id. }
        { now rewrite eqb_nid, H8. }
      }
    }
    {
      exists x. split.
      cbn. easy. cbn.
      rewrite eqb_id.
      repeat split; try easy.
      apply differ_pointwise_trivial.
      apply differ_pointwise_trivial.
    }
  }
  {
    split.
    {
      destruct H2. cbn in *.
      now rewrite H2.
    }
    split.
    {
      cbn. now rewrite eqb_nid.
    }
    split.
    {
      cbn. now rewrite eqb_nid.
    }
    intros.
    destruct H1, H2.
    cbn in *. ddestruct H1.
    constructor.
    {
      intros.
      rewrite <- H3.
      now rewrite <- st_cons0.
    }
    {
      intros.
      cbn. dec_eq_nats i i0.
      {
        rewrite eqb_id.
        rewrite <- x.
        destruct x1.
        constructor.
      }
      {
        rewrite eqb_nid; auto.
        now rewrite <- H2.
      }
    }
  }
}
{
  unfold sub, subRelt, ReturnAny, TReturn.
  unfold mapRetPoss, LiftSRelt.
  intros. psimpl.
  exists (retPoss i x).
  split.
  {
    set_ext y. unfold retPoss.
    split; intros; psimpl.
    {
      destruct y, x3.
      cbn in *.
      f_equal. easy.
      {
        extensionality k.
        dec_eq_nats i k.
        { now rewrite eqb_id. }
        { now rewrite eqb_nid, H8. }
      }
      {
        extensionality k.
        dec_eq_nats i k.
        { now rewrite eqb_id. }
        { now rewrite eqb_nid, H9. }
      }
    }
    {
      cbn. exists x.
      rewrite eqb_id.
      destruct H2. cbn in *.
      ddestruct H1.
      symmetry in x4.
      apply H0 in x4.
      specialize (x4 x3 eq_refl). psimpl.
      repeat split; try easy.
      apply differ_pointwise_trivial.
      apply differ_pointwise_trivial.
    }
  }
  {
    intros.
    split.
    {
      destruct H2. cbn in *.
      now rewrite H2.
    }
    split.
    {
      cbn. now rewrite eqb_nid.
    }
    split.
    {
      cbn. now rewrite eqb_nid.
    }
    intros.
    destruct H1, H2.
    cbn in *. ddestruct H1.
    constructor.
    {
      intros.
      rewrite <- H3.
      now rewrite <- st_cons0.
    }
    {
      intros.
      cbn. dec_eq_nats i i0.
      {
        rewrite eqb_id.
        rewrite <- x.
        destruct x1.
        constructor.
      }
      {
        rewrite eqb_nid; auto.
        now rewrite <- H2.
      }
    }
  }
}
{
  intros.
  eexists. split. easy.
  constructor.
  {
    cbn. f_equal.
    {
      extensionality k.
      destruct k.
      clear.
      generalize dependent x.
      induction N; cbn; intros.
      { easy. }
      {
        destruct x;
        simp indexntensor; cbn.
        { easy. }
      }
    }
    {
      clear.
      extensionality i.
      destruct N; easy.
    }
  }
  {
    intros. cbn.
    constructor.
  }
}
{
  intros.
  unfold Stable, stablePrec, LiftSRelt, LiftSPrec.
  unfold sub, subPrec. intros. psimpl.
  specialize (H0 x1 eq_refl). psimpl.
  exists x0. split. easy.
  now apply H4.
}
{
  unfold sub, subPrec, LiftSRelt, LiftSPrec.
  intros. psimpl.
  assert (ρ = eq (retPoss i x3)).
  {
    eapply Return_pres_single.
    exact H0.
  }
  subst.
  unfold TReturn in H0. psimpl.
  destruct H0. cbn in *.
  ddestruct H0. symmetry in x2.
  assert (x2' := x2). apply H in x2.
  specialize (x2 x3 eq_refl). psimpl.
  eexists. split. easy.
  clear - H1 H5 H2 H0 H6 x x2'.
  destruct H2.
  constructor.
  {
    intros. cbn.
    rewrite st_cons0.
    f_equal.
    {
      extensionality k.
      now rewrite H1 at 1.
    }
    {
      extensionality k.
      now rewrite H1 at 1.
    }
  }
  {
    cbn. intros.
    dec_eq_nats i i0.
    {
      rewrite eqb_id.
      rewrite <- x at 1.
      constructor.
    }
    {
      rewrite eqb_nid; auto.
      rewrite <- H6; auto.
    }
  }
}
{
  intros. destruct m. cbn.
  unfold index.
  eapply SafeBind with
    (QI:=fun _ _ => LiftSPrec (fun t σ =>
      Inv t σ /\
      fst t i = UCall (At i0 m) (getIndex i0 m) Return))
    (QR:=fun r _ _ => LiftSPrec (fun t σ =>
      Inv t σ /\
      Done i (At i0 m) r σ)).
  {
    intros.
    unfold Stable, stableRelt, LiftSRelt, LiftSPrec.
    unfold sub, subRelt. intros. psimpl.
    specialize (H0 x1 eq_refl). psimpl.
    exists x0. split. easy.
    split. now apply H5.
    now rewrite <- H0.
  }
  {
    intros.
    unfold Stable, stablePost, stableRelt, LiftSRelt, LiftSPrec.
    unfold sub, subRelt. intros. psimpl.
    specialize (H0 x1 eq_refl). psimpl.
    exists x0. split. easy.
    split. now apply H5.
    destruct H2.
    constructor.
    now rewrite <- H3.
    now rewrite <- H4.
  }
  {
    unfold Commit, LiftSPrec, LiftSRelt.
    intros. psimpl.
    assert (x2 = eq (invPoss i x3 (At i0 m))).
    {
      eapply Invoke_pres_single.
      exact H4.
    }
    subst.
    specialize (H3 _ eq_refl). psimpl.
    rewrite eqb_id in *.
    assert (Inv s x0).
    {
      apply H8.
      unfold TInvoke in H4. psimpl.
      destruct H5.
      constructor.
      {
        intros. cbn.
        rewrite st_cons0.
        f_equal.
        {
          extensionality k.
          now rewrite H9.
        }
        {
          extensionality k.
          now rewrite H9.
        }
      }
      {
        intros. cbn.
        destruct H4. cbn in *.
        ddestruct H4.
        dec_eq_nats i i1.
        {
          rewrite eqb_id.
          rewrite <- x at 1.
          constructor.
        }
        {
          rewrite eqb_nid; auto.
          rewrite <- H5; auto.
        }
      }
    }
    clear H8.
    apply conntensorrt_call in H2.
    exists (eq (
      comInvPoss i x0
        (At i0 m)
        (MkArr
          (fun k => indexntensor k (snd t))
          (activentensor (snd t)))
    )).
    unfold TInvoke in H4. psimpl.
    apply sing_elem in H10. psimpl.
    rewrite eqb_id in *.
    (* clear H3 H6 H12 H11 H10 H9 H8. *)
    split.
    {
      repeat econstructor.
    }
    assert (PCalls x0 i = CallPoss (At i0 m) /\ PRets x0 i = RetIdle).
    {
      destruct H. specialize (th_cons0 i).
      ddestruct H1. rewrite <- x4 in th_cons0.
      cbn in th_cons0. ddestruct th_cons0.
      apply getIndex_eq in x6. psimpl.
      easy.
    } psimpl.
    split.
    {
      intros. subst.
      eexists. split. easy.
      econstructor.
      4: constructor.
      {
        econstructor.
        {
          assert (
            (MkArr (fun k => indexntensor k (snd s)) (activentensor (snd s))) =
            PState x0
          ).
          {
            destruct H.
            rewrite st_cons0.
            easy.
          }
          cbn. rewrite <- H17.
          exact H2.
        }
        {
          easy.
        }
        {
          cbn. now rewrite eqb_id.
        }
        {
          easy.
        }
        {
          easy.
        }
      }
      {
        intros. cbn. now rewrite eqb_nid.
      }
      {
        easy.
      }
    }
    assert (
      Inv t
        (comInvPoss i x0 (At i0 m)
        (MkArr
          (fun k => indexntensor k (snd t))
          (activentensor (snd t))))
    ).
    {
      destruct H.
      constructor.
      { easy. }
      {
        cbn.  intros.
        dec_eq_nats i i1.
        {
          rewrite eqb_id.
          ddestruct H1.
          rewrite <- x at 1.
          rewrite H16.
          destruct H8. cbn in *.
          ddestruct H.
          rewrite H3 in x at 1.
          rewrite <- x in x5 at 1.
          ddestruct x5.
          constructor.
        }
        {
          rewrite eqb_nid; auto.
          rewrite H0; auto.
        }
      }
    }
    split.
    {
      eexists. split. easy.
      split. easy.
      destruct H8. cbn in *.
      ddestruct H8.
      ddestruct H1.
      rewrite <- H3 in x6.
      rewrite <- x5 in x6.
      ddestruct x6.
      easy.
    }
    {
      intros. eq_inj H18.
      eexists. split. easy.
      split.
      {
        intros. now rewrite H0.
      }
      split.
      {
        intros. cbn. now rewrite eqb_nid.
      }
      split.
      {
        easy.
      }
      { easy. }
    }
  }
  intros.
  split.
  {
    unfold Commit, LiftSRelt, LiftSPrec.
    intros. psimpl.
    apply conntensorrt_ret in H2.
    exists (eq (
      comRetPoss i x4
        (At i0 m)
        (MkArr
          (fun k => indexntensor k (snd t))
          (activentensor (snd t)))
        v
    )).
    split.
    { repeat econstructor. }
    assert (PCalls x4 i = CallDone (At i0 m) /\ PRets x4 i = RetIdle).
    {
      destruct H4.
      specialize (th_cons0 i).
      rewrite H5 in th_cons0.
      ddestruct th_cons0.
      easy.
    }
    split.
    {
      intros. subst.
      eexists. split. easy.
      econstructor.
      4: constructor.
      {
        econstructor 2.
        {
          assert (
            PState x4 =
            MkArr
              (fun k => indexntensor k (snd s))
              (activentensor (snd s))
          ).
          {
            destruct H4.
            now rewrite st_cons0.
          }
          rewrite H3.
          exact H2.
        }
        { easy. }
        { easy. }
        { easy. }
        { cbn. now rewrite eqb_id. }
      }
      { easy. }
      { cbn. intros. now rewrite eqb_nid. }
    }
    assert (
      Inv t
        (comRetPoss i x4 (At i0 m)
          (MkArr
            (fun k => indexntensor k (snd t))
            (activentensor (snd t))) 
          v)
    ).
    {
      destruct H4.
      constructor.
      { easy. }
      {
        intros. cbn.
        dec_eq_nats i i1.
        {
          rewrite eqb_id.
          rewrite H5 in H1.
          ddestruct H1.
          rewrite <- x at 1.
          psimpl. rewrite H.
          constructor.
        }
        {
          rewrite eqb_nid; auto.
          rewrite H0; auto.
        }
      }
    }
    split.
    {
      eexists. split. easy.
      split. easy.
      constructor; cbn.
      easy. now rewrite eqb_id.
    }
    {
      intros. eq_inj H9. 
      eexists. split. easy.
      split.
      { intros. now rewrite H0. }
      split.
      { easy. }
      split.
      { cbn. intros. now rewrite eqb_nid. }
      { easy. }
    }
  }
  {
    econstructor.
    unfold sub, subRelt, LiftSPrec, LiftSRelt.
    intros. psimpl.
    now exists x4.
  }
}
{
  unfold ReturnStep, LiftSPrec.
  intros. psimpl. exists (eq x1).
  split.
  { repeat econstructor. }
  split.
  {
    intros. subst.
    repeat econstructor.
  }
  split.
  {
    intros. subst.
    now destruct H3.
  }
  split.
  {
    unfold TReturn.
    split.
    {
      unfold Returned. intros.
      subst. now destruct H3.
    }
    split.
    {
      split; cbn.
      {
        rewrite eqb_id, H0 at 1.
        now constructor.
      }
      { intros. now rewrite eqb_nid. }
    }
    { easy. }
  }
  {
    unfold LiftSRelt, LiftSPrec.
    intros. eq_inj H.
    exists (retPoss i x0).
    split.
    {
      unfold mapRetPoss, retPoss.
      set_ext y. split; intros; psimpl.
      {
        destruct y, x1. cbn in *.
        f_equal. easy.
        {
          extensionality j.
          dec_eq_nats i j.
          { now rewrite eqb_id. }
          { now rewrite eqb_nid, H8. }
        }
        {
          extensionality j.
          dec_eq_nats i j.
          { now rewrite eqb_id. }
          { now rewrite eqb_nid, H9. }
        }
      }
      {
        exists x0. split. easy.
        cbn. rewrite eqb_id.
        destruct H3.
        repeat split; try easy.
        apply differ_pointwise_trivial.
        apply differ_pointwise_trivial.
      }
    }
    split.
    {
      cbn. intros. now rewrite eqb_nid.
    }
    split.
    {
      cbn. intros. now rewrite eqb_nid.
    }
    split.
    {
      cbn. intros. now rewrite eqb_nid.
    }
    {
      destruct H2.
      constructor.
      {
        cbn. easy.
      }
      {
        cbn. intros.
        dec_eq_nats i i0.
        {
          rewrite eqb_id.
          constructor.
        }
        {
          rewrite eqb_nid; auto.
        }
      }
    }
  }
}
Qed.