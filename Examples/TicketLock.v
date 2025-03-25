From Paco Require Import paco.

From LHL.Core Require Import
  Program
  ProgramFacts
  ProgramRules
  Specs
  Logic
  LogicFacts
  LogicPaco
  Tensor
  Traces
  Linearizability
  VisPoss
  SingConds.

From LHL.Examples Require Import
  LockSpec
  FAISpec
  NameSpec
  ArraySpec
  Counter.CounterSig
  Counter.RacyCounterSpec.

From LHL.Util Require Import
  Tactics
  TransUtil
  Util.

From Coq Require Import
  Arith.PeanoNat
  Program.Equality
  Logic.FunctionalExtensionality
  Logic.PropExtensionality
  Logic.Classical_Prop
  Lists.List.

Require Import Unicode.Utf8.

Import ListNotations.

CoFixpoint until {E R} (m : E R) (k : R -> bool) : Prog E unit :=
  Bind m (λ x,
    if k x then
      ret tt
    else
      until m k).

Definition E (T : nat) := FAISig |+| CounterSig.
Definition F := LockSig.

CoFixpoint acq_body {T} (my_tkt : nat) : Prog (E T) unit :=
  Bind (inr Get) (λ cur_tkt,
  if cur_tkt =? my_tkt then
    ret tt
  else
    acq_body my_tkt).

Definition acq {T} : Prog (E T) unit :=
  my_tkt <- call FAI;
  acq_body my_tkt.

Definition rel {T} : Prog (E T) unit :=
  call Inc.

Definition ticketLockImpl {T} : Impl (E T) F :=
  fun _ m => match m with
  | Acq => acq
  | Rel => rel
  end.

Definition VE T : Spec T (E T) :=
  faiSpec ⊗ rcntSpec.
Definition VF T : Spec T F :=
  lockSpec.

Definition Relt T := SRelt (VE T) (VF T).
Definition Prec T := SPrec (VE T) (VF T).

Notation faiSt s := (LState (snd s)).
Notation cntSt s := (RState (snd s)).

Notation faiVal s := (fst (faiSt s)).
Notation cntVal s := (
  match (cntSt s).(rcnt_num) with
  | Some n => n
  | None => 0
  end
).

Definition Ready {T} my_tkt i (s : InterState F (VE T)) :=
  fst s i = UCall Acq (inr Get)
    (λ cur_tkt,
      if cur_tkt =? my_tkt then
        ret tt
      else
        acq_body my_tkt).

Variant PC := pc.

Record Inv {T} {i : Name T}
  {s : InterState F (VE T)} {ρ : Poss (VF T)}
: Prop
:= MkInv {
  lock_idle :
    ρ.(PState).(lock_pend) = None;
  owns_resp :
    (∃ j, i <> j /\
      ρ.(PState).(lock_owner) = Some (Some j)) ->
    ∀ my_tkt cur_tkt,
      Ready my_tkt i s ->
      Some cur_tkt = (cntSt s).(rcnt_num) ->
      my_tkt ≠ cur_tkt;
  rcnt_defn :
    ρ.(PState).(lock_owner) ≠ None ->
    (cntSt s).(rcnt_num) ≠ None;
  owns_resp2 :
    (∃ j, i <> j /\
      ρ.(PState).(lock_owner) = Some (Some j)) ->
    ∀ cur_tkt my_tkt,
      Some cur_tkt = (cntSt s).(rcnt_num) ->
      fst s i = Cont Acq (acq_body my_tkt) ->
      my_tkt ≠ cur_tkt;
  owns_wait :
    (* ∀ nret : fst s i ≠ Cont Acq (Return tt), *)
    (* ∀ nret : True, *)
    (* ∀ nrel :
      ¬((∃ p, fst s i = Cont Rel p) \/
        (∃ A (m : E T A) k, fst s i = UCall Rel m k)), *)
    ∀ own,
    ∀ nret : own ≠ Some i,
    ∀ nrel :
      ¬(False \/
        (∃ A (m : E T A) k, fst s i = UCall Rel m k)),
      ρ.(PState).(lock_owner) = Some own ->
      ∀ cur_tkt,
        Some cur_tkt = (cntSt s).(rcnt_num) ->
        cur_tkt = faiVal s ->
        own = None;
  tkts_less :
    (* ∀ nrel :
      ¬((∃ p, fst s i = Cont Rel p) \/
        (∃ A (m : E T A) k, fst s i = UCall Rel m k)), *)
    ∀ nrel :
      ¬(False \/
        (∃ A (m : E T A) k, fst s i = UCall Rel m k)),
    ρ.(PState).(lock_owner) ≠ None ->
    (* ∀ nnone : ρ.(PState).(lock_owner) ≠ Some None, *)
    ∀ cur_tkt,
      Some cur_tkt = (cntSt s).(rcnt_num) ->
      cur_tkt ≤ faiVal s;
  tkts_uniq :
    ρ.(PState).(lock_owner) ≠ None ->
    (* ∀ nnone : ρ.(PState).(lock_owner) ≠ Some None, *)
    ∀ cur_tkt j,
      i ≠ j ->
      (* Some cur_tkt = (cntSt s).(rcnt_num) -> *)
      (Ready cur_tkt i s \/ fst s i = Cont Acq (acq_body cur_tkt)) ->
      (Ready cur_tkt j s \/ fst s j = Cont Acq (acq_body cur_tkt)) ->
      False;
  tkts_boun :
    ρ.(PState).(lock_owner) ≠ None ->
    ∀ j my_tkt,
      (* i ≠ j -> *)
      True ->
      (Ready my_tkt j s \/ fst s j = Cont Acq (acq_body my_tkt)) ->
      my_tkt < faiVal s;
  rcnt_wait :
    ¬(ρ.(PState).(lock_owner) = Some (Some i) /\
      ∃ j, i ≠ j /\
        (cntSt s).(rcnt_pend) = Some (MetPend j Inc));
  wait_less :
    ∀ i,
      ρ.(PState).(lock_owner) = Some (Some i) ->
      ∀ cur_tkt,
        Some cur_tkt = rcnt_num (cntSt s) ->
        cur_tkt < faiVal s
}.
Arguments Inv {T} i s ρ.

Definition Precs {T A} (i : Name T) (m : LockSig A) : Prec T :=
  Inv i.

Definition Posts {T A} (i : Name T) (m : LockSig A) (v : A) : Relt T :=
  fun _ _ s ρ =>
    Inv i s ρ /\
    PCalls ρ i = CallDone m /\
    PRets ρ i = RetPoss m v.

Notation UStep s i e t := (
  InterStep ticketLockImpl s (i, UEvent (Some e)) t
).

Record Rely {T} {i : Name T}
  {s : InterState F (VE T)} {ρ : Poss (VF T)}
  {t : InterState F (VE T)} {σ  : Poss (VF T)}
:= {
  pres_inv :
    Inv i s ρ -> Inv i t σ;
  pres_call :
    PCalls ρ i = PCalls σ i;
  pres_ret :
    PRets ρ i = PRets σ i;
  pres_ths :
    fst s i = fst t i;
  pres_undef :
    ρ.(PState).(lock_owner) = None ->
    σ.(PState).(lock_owner) = None;
  (*pres_owns :
    σ.(PState).(lock_owner) ≠ None ->
    ρ.(PState).(lock_owner) = Some (Some i) ->
    σ.(PState).(lock_owner) = Some (Some i) *)
}.
Arguments Rely {T} i s ρ t σ.

Definition Guar {T} (i : Name T) : Relt T :=
  λ s ρ t σ,
    ∀ j, i ≠ j ->
      Rely j s ρ t σ.

(* Record Guar {T} {i : Name T}
  {s : InterState F (VE T)} {ρ : Poss (VF T)}
  {t : InterState F (VE T)} {σ  : Poss (VF T)}
:= {
  gpres_inv :
    ∀ j, i ≠ j -> Inv j s ρ -> Inv j t σ;
  gpres_call :
    ∀ j, i ≠ j -> PCalls ρ j = PCalls σ j;
  gpres_ret :
    ∀ j, i ≠ j -> PRets ρ j = PRets σ j;
  gpres_ths :
    ∀ j, i ≠ j -> fst s j = fst t j;
  gresp_othr :
    ∀ j,
      i ≠ j ->
      σ.(PState).(lock_owner) ≠ Some (Some j)
}.
Arguments Guar {T} i s ρ t σ.

Lemma tollens P Q :
  (P -> Q) ->
  ¬Q -> ¬P.
Proof.
  unfold not. intros.
  now apply H0, H.
Qed.

Lemma PPNN P : P -> ¬¬P.
Proof.
  unfold not. intros.
  now apply H0.
Qed.

Lemma Guar_in_Rely {T} :
  ∀ i j : Name T,
    i ≠ j ->
    Guar i S=> Rely j.
Proof.
  unfold ssub, subSRelt.
  intros. destruct H0.
  constructor.
  { intros. now apply gpres_inv0. }
  { intros. now apply gpres_call0. }
  { intros. now apply gpres_ret0. }
  { intros. now apply gpres_ths0. }
  {
    
  }
  {
    intros.
    specialize (gresp_othr0 j).
    apply tollens with
      (P:= i ≠ j)
      (Q:= lock_owner (PState σ) ≠ Some (Some j))
      in gresp_othr0.
    exfalso. now apply gresp_othr0.
    now apply PPNN.
  } *)

Lemma Invoke_pres_single {A R} :
  forall (m : F R) i s ρ t σs,
  TInvoke (VE:= VE A) (VF:= VF A) ticketLockImpl i R m s (eq ρ) t σs ->
  exists σ, σs = eq σ.
intros.
unfold TInvoke in H. psimpl.
exists (invPoss i ρ m).
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

Lemma eq_sing {A} :
  forall (x : A) (P : A -> Prop),
  eq x = P ->
  P x.
Proof.
  intros. now subst.
Qed.

Lemma eq_inj {A} :
  forall x y : A,
  eq x = eq y ->
  x = y.
Proof.
  intros.
  now rewrite H.
Qed.

Inductive lock {P : Prop} : Prop :=
| Lock (p : P).
Arguments lock : clear implicits.

Ltac lock H :=
  match type of H with
  | ?P =>
    assert (Hlock : lock P)
      by exact (Lock H);
    clear H
  end.

Lemma acq_inv_stable {T} {i : Name T} :
  forall e c r,
  Stable (LiftSRelt (Rely i))
    (λ _ _, LiftSPrec (λ s ρ,
    (Inv i s ρ /\
     fst s i = e) /\
    PCalls ρ i = c /\
    PRets ρ i = r)).
Proof.
  unfold Stable, stableRelt, sub, subRelt.
  unfold LiftSRelt, LiftSPrec. intros. psimpl.
  specialize (H0 x1 eq_refl). psimpl.
  exists x0. split. easy. destruct H0.
  split. split.
  { now apply pres_inv0. }
  easy. easy.
Qed.

Require Import Lia.

Lemma tkts_eql2 {T} v w :
  UCall Acq (inr Get)
    (λ cur_tkt,
      if cur_tkt =? v then
        ret tt
      else
        acq_body (T:=T) v) =
  UCall Acq (inr Get)
    (λ cur_tkt,
      if cur_tkt =? w then
        ret tt
      else
        acq_body w) ->
  v = w.
Proof.
  intros. ddestruct H.
  apply equal_f with
    (x:=v) in x.
  rewrite eqb_id in x.
  dec_eq_nats v w.
  { easy. }
  {
    rewrite eqb_nid in x; auto.
    symmetry in x.
    now rewrite frobProgId in x at 1.
  }
Qed.

Lemma tkts_eql {T} v w :
  Cont Acq (acq_body (T:=T) v) = Cont Acq (acq_body w) ->
  v = w.
Proof.
  rewrite frobProgId with
    (p := acq_body v).
  rewrite frobProgId with
    (p := acq_body w).
  cbn. intros. ddestruct H.
  apply equal_f with
    (x:=v) in x.
  rewrite eqb_id in x.
  dec_eq_nats v w.
  { easy. }
  {
    rewrite eqb_nid in x; auto.
    symmetry in x.
    now rewrite frobProgId in x at 1.
  }
Qed.

Lemma acq_correct {T} (i : Name T) :
  VerifyProg i
    (LiftSRelt (Rely i))
    (LiftSRelt (Guar i))
    (prComp
      (LiftSPrec (Precs i Acq))
      (TInvoke ticketLockImpl i unit Acq) ->>
      LiftSRelt (Rely i))
    acq
    (λ v, LiftSRelt (Posts i Acq v)).
Proof.
  unfold acq.
  eapply weakenPrec with
    (P:=λ _ _, LiftSPrec (λ s ρ,
      Inv i s ρ /\
      PCalls ρ i = CallPoss Acq /\
      PRets ρ i = RetIdle /\
      fst s i = Cont Acq acq)).
  2:{
    unfold sub, subRelt, Precs, LiftSPrec, LiftSRelt.
    intros. psimpl.
    assert (exists x, x0 = eq x).
    {
      eapply Invoke_pres_single.
      exact H1.
    }
    psimpl.
    specialize (H0 x2 eq_refl). psimpl.
    eexists. split. easy.
    unfold TInvoke in H1. psimpl.
    apply eq_sing in H4. psimpl.
    destruct H0.
    cut (
      (Inv i t x0 /\ fst t i = Cont Acq acq) /\
      PCalls x0 i = CallPoss Acq /\
      PRets x0 i = RetIdle
    ).
    { easy. }
    split. 2: now rewrite <- pres_call0, <- pres_ret0.
    split.
    {
      apply pres_inv0. destruct H2.
      constructor.
      { now rewrite H5 at 1. }
      {
        intros.
        unfold Ready in H2.
        destruct H1. ddestruct H1.
        now rewrite <- x in H2 at 1.
      }
      { now rewrite H5, <- H3 at 1. }
      (* constructor. *)
      {
        intros.
        destruct H1. ddestruct H1.
        rewrite <- x in H4 at 1.
        ddestruct H4.
        rewrite frobProgId with
          (p:=acq)
          in x.
        rewrite frobProgId with
          (p:= acq_body _)
          in x.
        easy.
      }
      {
        intros.
        eapply owns_wait0.
        {
          destruct H1. cbn in *.
          easy.
          (* ddestruct H1. now rewrite <- x4. *)
        }
        {
          unfold not. intros. psimpl.
          unfold TIdle in H. psimpl.
          setoid_rewrite H in H10.
          now destruct H10; psimpl.
        }
        { now rewrite <- H5 at 1. }
        { rewrite H3 at 1. exact H2. }
        { now rewrite H3 at 1. }
      }
      {
        intros.
        rewrite <- H3 at 1.
        apply tkts_less0.
        {
          unfold not. intros. psimpl.
          destruct H1. ddestruct H1. cbn in *.
          setoid_rewrite <- x4 in H4.
          now destruct H4; psimpl.
        }
        { now rewrite <- H5 at 1. }
        { now rewrite H3 at 1. }
      }
      {
        intros. destruct H1.
        cbn in *. ddestruct H1.
        unfold Ready in H4.
        destruct H4 as [H4 | H4];
        rewrite <- x in H4 at 1.
        { easy. }
        {
          rewrite frobProgId with
            (p:=ticketLockImpl _ _)
            in H4.
          rewrite frobProgId with
            (p:=acq_body _)
            in H4.
          easy.
        }
      }
      {
        unfold Ready. intros.
        destruct H1. cbn in *.
        rewrite <- H3 at 1.
        eapply tkts_boun0 with
          (j:=j).
        { now rewrite <- H5 at 1. }
        { exact H2. }
        {
          dec_eq_nats j i.
          {
            ddestruct H1.
            setoid_rewrite <- x in H4.
            destruct H4. easy.
            rewrite frobProgId with
              (p:= ticketLockImpl _ _)
              in H1.
            rewrite frobProgId with
              (p:= acq_body _)
              in H1.
            easy.
          }
          unfold Ready.
          now repeat rewrite H10 at 1.
        }
      }
      {
        setoid_rewrite H5.
        setoid_rewrite <- H3 at 1.
        easy.
      }
      {
        setoid_rewrite H5.
        setoid_rewrite <- H3.
        easy.
      }
    }
    {
      destruct H1. ddestruct H0.
      cbn in *. now rewrite <- pres_ths0 at 1.
    }
  }
  eapply lemBind.
  {
    eapply (lemCall
      (Q:= λ _ _,
        LiftSPrec (fun s ρ =>
          (Inv i s ρ /\
           fst s i = UCall Acq (inl FAI) acq_body) /\
          PCalls ρ i = CallPoss Acq /\
          PRets ρ i = RetIdle))
      (S:= λ my_tkt _ _,
        LiftSPrec (fun s ρ =>
          (Inv i s ρ /\
             fst s i = Cont Acq (acq_body my_tkt)) /\
          PCalls ρ i = CallPoss Acq /\
          PRets ρ i = RetIdle))).
    { apply acq_inv_stable. }
    {
      unfold Stable, stablePost.
      intros. apply acq_inv_stable.
    }
    {
      unfold Commit, Precs, LiftSPrec, LiftSRelt.
      intros. do 2 psimpl.
      exists (eq x1).
      split.
      { repeat eexists. }
      split.
      {
        intros. subst.
        repeat econstructor.
      }
      unfold acq in *.
      rewrite H6 in H1. ddestruct H1.
      rewrite frobProgId with
        (p:= bindProg _ _)
        in x2. cbn in x2.
      ddestruct x2.
      split.
      {
        exists x1.
        split. easy.
        split. 2: easy.
        split.
        {
          destruct H3.
          constructor.
          { easy. }
          {
            unfold Ready. intros.
            now rewrite <- x in H3 at 1.
          }
          { now rewrite <- H9 at 1. }
          (* constructor. *)
          {
            intros.
            rewrite <- x in H10 at 1.
            easy.
          }
          {
            intros. ddestruct H.
            eapply owns_wait0.
            {
              easy.
              (* rewrite H6 at 1.
              rewrite frobProgId at 1.
              easy. *)
            }
            {
              unfold not. intros. psimpl.
              setoid_rewrite H6 in H.
              now destruct H; psimpl.
            }
            { easy. }
            { rewrite H9 at 1. exact H3. }
            { subst. now rewrite <- x3, <- x at 1. }
          }
          {
            setoid_rewrite <- H9 at 1.
            assert (faiVal t = faiVal s).
            {
              ddestruct H.
              now rewrite <- x3, <- x at 1.
            }
            setoid_rewrite H1.
            intro. apply tkts_less0.
            {
              unfold not. intros. psimpl.
              setoid_rewrite H6 in H3.
              now destruct H3; psimpl.
            }
          }
          {
            intros.
            unfold Ready in H10.
            destruct H10 as [H10 | H10];
            now rewrite <- x in H10 at 1.
          }
          {
            assert (faiVal t = faiVal s).
            {
              ddestruct H.
              now rewrite <- x3, <- x at 1.
            }
            setoid_rewrite H1.
            intros. eapply tkts_boun0 with
              (j:=j).
            { easy. }
            { exact H10. }
            {
              dec_eq_nats j i.
              {
                unfold Ready in H11.
                setoid_rewrite <- x in H11.
                now destruct H11.
              }
              unfold Ready.
              now rewrite <- H0.
            }
          }
          { now setoid_rewrite <- H9 at 1. }
          {
            assert (faiVal t = faiVal s).
            {
              ddestruct H.
              now rewrite <- x3, <- x at 1.
            }
            setoid_rewrite H1.
            setoid_rewrite <- H9.
            easy.
          }
        }
        {
          rewrite <- x at 1.
          f_equal. extensionality my_tkt.
          rewrite frobProgId with (p:=bindProg _ _).
          rewrite frobProgId with (p:=acq_body my_tkt).
          easy.
        }
      }
      {
        intros. apply eq_inj in H1.
        subst. eexists. split. easy.
        constructor.
        2: easy.
        2: easy.
        2: now rewrite H0.
        (* 2: easy. *)
        intros.
        destruct H10. constructor.
        { easy. }
        {
          intros. apply owns_resp0.
          { easy. }
          {
            unfold Ready in *.
            now rewrite <- H0.
          }
          { now rewrite H9 at 1. }
        }
        { now rewrite <- H9 at 1. }
        (* constructor. *)
        {
          setoid_rewrite <- H9.
          now rewrite H0.
        }
        {
          intros. subst.
          eapply owns_wait0.
          easy.
          (* { now rewrite <- H0. } *)
          { now setoid_rewrite <- H0. }
          { easy. }
          { rewrite H9 at 1. exact H11. }
          {
            ddestruct H.
            now rewrite <- x3, <- x at 1.
          }
        }
        {
          setoid_rewrite <- H9 at 1.
          assert (faiVal t = faiVal s).
          {
            ddestruct H.
            now rewrite <- x3, <- x at 1.
          }
          setoid_rewrite H10.
          intro. apply tkts_less0.
          now setoid_rewrite <- H0.
        }
        {
          intros.
          eapply tkts_uniq0.
          { easy. }
          { exact H11. }
          {
            unfold Ready.
            rewrite <- H0; auto.
            exact H12.
          }
          {
            assert (i ≠ j0).
            {
              unfold not. intros.
              subst. unfold Ready in H13.
              destruct H13;
              now rewrite <- x in H13 at 1.
            }
            unfold Ready.
            now rewrite <- H0.
          }
        }
        {
          ddestruct H.
          assert (faiVal t = faiVal s).
          { now rewrite <- x3, <- x at 1. }
          setoid_rewrite H. intros.
          eapply tkts_boun0 with
            (j:=j0).
          { easy. }
          { exact H11. }
          {
            assert (j0 ≠ i).
            {
              unfold not. intros.
              subst. unfold Ready in H12.
              repeat rewrite <- x1 in H12 at 1.
              now destruct H12.
            }
            unfold Ready.
            rewrite <- H0; auto.
          }
        }
        { now setoid_rewrite <- H9 at 1. }
        {
          assert (faiVal t = faiVal s).
          {
            ddestruct H.
            now rewrite <- x3, <- x at 1.
          }
          setoid_rewrite H10.
          setoid_rewrite <- H9.
          easy.
        }
        { easy. }
      }
    }
    {
      intros.
      unfold Commit, Precs, LiftSPrec, LiftSRelt.
      intros. do 2 psimpl.
      exists (eq x3).
      split.
      { repeat econstructor. }
      split.
      {
        intros. subst.
        repeat econstructor.
      }
      split.
      {
        intros. exists x3.
        split. easy.
        split. 2: easy.
        rewrite H7 in H1.
        ddestruct H1.
        split. 2: easy.
        destruct H4.
        constructor.
        { easy. }
        {
          unfold Ready. intros.
          now rewrite <- x in H4 at 1.
        }
        { now rewrite <- H13 at 1. }
        (* constructor. *)
        {
          intros.
          assert (v = my_tkt).
          {
            eapply tkts_eql.
            now transitivity (fst t i).
          }
          unfold not. intros. subst.
          ddestruct H. psimpl.
          assert (Some x7 = None).
          {
            apply owns_wait0 with
              (cur_tkt:=cur_tkt).
              congruence.
            (* { now rewrite H7 at 1. } *)
            {
              unfold not. intros. psimpl.
              setoid_rewrite H7 in H15.
              now destruct H15; psimpl.
            }
            { easy. }
            { now rewrite H13 at 1. }
            { now rewrite <- x6 at 1. }
          }
          easy.
        }
        {
          intros.
          ddestruct H.
          rewrite <- x in H14 at 1.
          cbn in *. subst. exfalso.
          assert (S v ≤ faiVal s).
          {
            apply tkts_less0.
            {
              setoid_rewrite H7.
              unfold not. intros.
              now destruct H; psimpl.
            }
            { now rewrite H1 at 1. }
            { now rewrite H13 at 1. }
          }
          rewrite <- x6 in H at 1.
          cbn in *. lia.
        }
        {
          intros.
          rewrite <- H13 in H4 at 1.
          eapply tkts_less0 in H4; auto.
          2:{
            setoid_rewrite H7.
            unfold not. intros.
            now destruct H14; psimpl.
          }
          assert (faiVal s ≤ faiVal t).
          {
            ddestruct H.
            rewrite <- x6, <- x at 1.
            cbn. lia.
          }
          now transitivity (faiVal s).
        }
        {
          intros. destruct H14;
          unfold Ready in H14, H15.
          { now rewrite <- x in H14 at 1. }
          assert (v = cur_tkt).
          {
            eapply tkts_eql.
            now transitivity (fst t i).
          }
          subst. ddestruct H.
          rewrite H0 in H15; auto.
          apply tkts_boun0 in H15; auto.
          rewrite <- x5 in H15 at 1.
          cbn in *. lia.
        }
        {
          ddestruct H. intros.
          dec_eq_nats j i.
          {
            unfold Ready in H4.
            setoid_rewrite <- x5 in H4.
            destruct H4. easy.
            apply tkts_eql in H4. subst.
            rewrite <- x at 1. cbn. lia.
          }
          assert (faiVal s < faiVal t).
          {
            rewrite <- x6, <- x at 1.
            cbn. lia.
          }
          unfold Ready in H4.
          rewrite H0 in H4; auto.
          apply tkts_boun0 in H4; auto.
          now transitivity (faiVal s).
        }
        { now setoid_rewrite <- H13 at 1. }
        {
          assert (faiVal s < faiVal t).
          {
            ddestruct H.
            rewrite <- x6, <- x at 1.
            cbn. lia.
          }
          intros.
          transitivity (faiVal s).
          2: easy.
          eapply wait_less0.
          { exact H4. }
          { now rewrite H13 at 1. }
        }
      }
      {
        intros. apply eq_inj in H14.
        subst. exists x2. split. easy.
        constructor.
        2: easy.
        2: easy.
        2: now rewrite H0.
        (* 2: easy. *)
        intros.
        destruct H15. constructor.
        { easy. }
        {
          intros.
          apply owns_resp0.
          { easy. }
          {
            unfold Ready.
            now rewrite <- H0.
          }
          { now rewrite H13 at 1. }
        }
        { now rewrite <- H13 at 1. }
        (* constructor. *)
        {
          setoid_rewrite <- H13 at 1.
          setoid_rewrite H0; auto.
        }
        {
          intros.
          ddestruct H.
          rewrite <- x in H17 at 1.
          cbn in *. subst. exfalso.
          assert (S v ≤ faiVal s).
          {
            apply tkts_less0.
            { now setoid_rewrite <- H0. }
            { now rewrite H15 at 1. }
            { now rewrite H13 at 1. }
          }
          rewrite <- x5 in H at 1.
          cbn in *. lia.
        }
        {
          intros.
          rewrite <- H13 in H16 at 1.
          eapply tkts_less0 in H16; auto.
          2: now setoid_rewrite <- H0.
          assert (faiVal s ≤ faiVal t).
          {
            ddestruct H.
            rewrite <- x5, <- x at 1.
            cbn. lia.
          }
          now transitivity (faiVal s).
        }
        {
          intros.
          rewrite H7 in H1. ddestruct H1.
          assert (j0 ≠ i).
          {
            unfold Ready in H18.
            unfold not. intro. subst.
            repeat rewrite <- x in H18 at 1.
            destruct H18.
            { easy. }
            {
              apply tkts_eql in H1. subst.
              unfold Ready in H17.
              do 2 rewrite H0 in H17; auto.
              eapply H4.(tkts_boun) in H17.
              2: easy. 2: easy.
              ddestruct H.
              rewrite <- x5 in H17 at 1.
              cbn in *. lia.
            }
          }
          eapply tkts_uniq0.
          { easy. }
          { exact H16. }
          (* { rewrite H13 at 1. exact H17. } *)
          {
            unfold Ready.
            rewrite <- H0 at 1; auto.
            rewrite <- H0 at 1; auto.
            exact H17.
          }
          {
            unfold Ready.
            now repeat rewrite <- H0.
          }
        }
        {
          ddestruct H. intros.
          dec_eq_nats j0 i.
          {
            unfold Ready in H16.
            rewrite H7 in H1. ddestruct H1.
            setoid_rewrite <- x in H16.
            destruct H16. easy.
            apply tkts_eql in H1. subst.
            rewrite <- x6 at 1. cbn. lia.
          }
          assert (faiVal s < faiVal t).
          {
            rewrite <- x5, <- x at 1.
            cbn. lia.
          }
          destruct H16 as [H16 | H16].
          {
            unfold Ready in H16.
            rewrite H0 in H16; auto.
            assert (my_tkt < faiVal s).
            {
              eapply tkts_boun0 with
                (j:=j0).
              { easy. }
              { exact H15. }
              { now left. }
            }
            now transitivity (faiVal s).
          }
          {
            rewrite H7 in H1 at 1.
            ddestruct H1.
            dec_eq_nats j0 i.
            {
              rewrite <- x in H16 at 1.
              apply tkts_eql in H16. subst.
              rewrite <- x6 at 1. cbn. lia.
            }
            {
              rewrite H0 in H16; auto.
              assert (my_tkt < faiVal s).
              {
                eapply tkts_boun0 with
                  (j:=j0).
                { easy. }
                { exact H15. }
                { now right. }
              }
              now transitivity (faiVal s).
            }
          }
        }
        { now setoid_rewrite <- H13 at 1. }
        {
          assert (faiVal s < faiVal t).
          {
            ddestruct H.
            rewrite <- x5, <- x at 1.
            cbn. lia.
          }
          intros.
          transitivity (faiVal s).
          2: easy.
          eapply wait_less0.
          { exact H16. }
          { now rewrite H13 at 1. }
        }
        { easy. }
      }
    }
  }
  intros my_tkt.
  eapply weakenPrec with
    (P:=λ _ _,
      LiftSPrec (fun s ρ =>
        (Inv i s ρ /\
          fst s i = Cont Acq (acq_body my_tkt)) /\
        PCalls ρ i = CallPoss Acq /\
        PRets ρ i = RetIdle)).
  2:{
    unfold sub, subRelt.
    intros. now psimpl.
  }
  cut (
    forall P,
    P ==> (λ _ _,
      LiftSPrec (fun s ρ =>
        (Inv i s ρ /\
          fst s i = Cont Acq (acq_body my_tkt)) /\
        PCalls ρ i = CallPoss Acq /\
        PRets ρ i = RetIdle)) ->
    VerifyProg i
      (LiftSRelt (Rely i)) (LiftSRelt (Guar i))
      P
      (acq_body my_tkt)
      (λ v, LiftSRelt (Posts i Acq v))
  ).
  {
    intros.
    now apply H.
  }
  unfold VerifyProg.
  setoid_rewrite paco_eqv.
  pcofix rec. intros. pfold.
  rename H0 into H.
  rewrite frobProgId at 1.
  eapply SafeBind with
    (QI:=λ _ _,
      LiftSPrec (fun s ρ =>
        (Inv i s ρ /\
         fst s i = UCall Acq (inr Get) (
           λ cur_tkt,
           if cur_tkt =? my_tkt then
             ret tt
           else
             acq_body (my_tkt))) /\
        PCalls ρ i = CallPoss Acq /\
        PRets ρ i = RetIdle))
    (QR:=λ cur_tkt _ _,
      LiftSPrec (fun s ρ =>
        if cur_tkt =? my_tkt then
          (Inv i s ρ /\
              fst s i = Cont Acq (ret tt)) /\
          PCalls ρ i = CallDone Acq /\
          PRets ρ i = RetPoss Acq tt
        else
          (Inv i s ρ /\
            fst s i = Cont Acq (acq_body my_tkt)) /\
          PCalls ρ i = CallPoss Acq /\
          PRets ρ i = RetIdle)).
  { apply acq_inv_stable. }
  {
    unfold Stable, stablePost.
    intros. destruct (v =? my_tkt);
    apply acq_inv_stable.
  }
  {
    unfold Commit, Precs, LiftSPrec, LiftSRelt.
    intros. do 2 psimpl. apply H in H0. clear H.
    unfold LiftSPrec in H0. psimpl.
    exists (eq x1).
    split.
    { repeat econstructor. }
    split.
    {
      intros. subst.
      repeat econstructor.
    }
    rewrite H10 in H2. ddestruct H2.
    rewrite frobProgId with
      (p:=acq_body _)
      in x2. cbn in *.
    ddestruct x2.
    split.
    {
      exists x1. split. easy.
      split. 2: easy.
      split. 2: easy.
      destruct H0.
      constructor.
      { easy. }
      {
        unfold Ready. intros.
        rewrite <- x in H0 at 1.
        ddestruct H0.
        apply equal_f with
          (x:=cur_tkt)
          in x.
        unfold not. intros.
        subst. rewrite eqb_id in *.
        assert (cur_tkt = my_tkt).
        {
          apply NNPP. unfold not at 1.
          intros. rewrite eqb_nid in *; auto.
          now rewrite frobProgId in x at 1.
        }
        subst. clear x.
        eapply owns_resp3 with
          (cur_tkt:=my_tkt)
          (my_tkt:=my_tkt).
        { easy. }
        {
          rewrite H2.
          ddestruct H3.
          now rewrite <- x3, <- x at 1.
        }
        { easy. }
        { easy. }
      }
      {
        intros. ddestruct H3.
        rewrite <- x at 1.
        apply rcnt_defn0 in H.
        now rewrite <- x3 in H at 1.
      }
      (* constructor. *)
      {
        intros.
        now rewrite <- x in H2 at 1.
      }
      {
        assert ((cntSt t).(rcnt_num) = (cntSt s).(rcnt_num)).
        {
          ddestruct H3.
          now rewrite <- x3, <- x at 1.
        }
        setoid_rewrite H.
        setoid_rewrite <- H7.
        intros own nown _. apply owns_wait0.
        easy.
        (* now rewrite H10, frobProgId at 1. *)
        {
          unfold not. intros. psimpl.
          setoid_rewrite H10 in H0.
          now destruct H0; psimpl.
        }
      }
      {
        assert ((cntSt t).(rcnt_num) = (cntSt s).(rcnt_num)).
        {
          ddestruct H3.
          now rewrite <- x3, <- x at 1.
        }
        setoid_rewrite H.
        setoid_rewrite <- H7.
        intro. apply tkts_less0.
        {
          setoid_rewrite H10.
          unfold not. intros.
          now destruct H0; psimpl.
        }
      }
      {
        unfold Ready. intros. destruct H2.
        2:now rewrite <- x in H2 at 1.
        assert (my_tkt = cur_tkt).
        {
          clear - x H2.
          rewrite <- x in H2 at 1.
          clear - H2. ddestruct H2.
          apply equal_f with
            (x:=cur_tkt)
            in x.
          rewrite eqb_id in x.
          dec_eq_nats cur_tkt my_tkt.
          { easy. }
          rewrite eqb_nid in *; auto.
          now rewrite frobProgId in x at 1.
        }
        subst.
        eapply tkts_uniq0.
        { easy. }
        { exact H0. }
        (* {
          assert ((cntSt s).(rcnt_num) = (cntSt t).(rcnt_num)).
          {
            ddestruct H3.
            now rewrite <- x3, <- x at 1.
          }
          rewrite H2.
          exact H2.
        } *)
        { right. exact H10. }
        { now rewrite H1 in H11. }
      }
      {
        setoid_rewrite <- H7.
        intros.
        eapply tkts_boun0 with
          (j:=j).
        { easy. }
        { exact H0. }
        {
          unfold Ready.
          dec_eq_nats j i.
          {
            unfold Ready in H2.
            setoid_rewrite <- x in H2.
            destruct H2. 2: easy.
            apply tkts_eql2 in H2. subst.
            setoid_rewrite H10.
            now right.
          }
          rewrite <- H1; auto.
        }
      }
      {
        unfold not. intros.
        psimpl. ddestruct H3;
        now rewrite <- x in H2 at 1.
      }
      {
        assert (rcnt_num (cntSt t) = rcnt_num (cntSt s)).
        {
          ddestruct H3;
          now rewrite <- x3, <- x at 1.
        }
        setoid_rewrite H.
        setoid_rewrite <- H7.
        easy.
      }
    }
    {
      intros. apply eq_inj in H.
      subst. exists x2. split. easy.
      constructor.
      2: easy.
      2: easy.
      2: now rewrite H1.
      (* 2: easy. *)
      intros. destruct H2.
      constructor.
      { easy. }
      {
        intros. apply owns_resp0.
        { easy. }
        {
          unfold Ready.
          now rewrite <- H1.
        }
        {
          ddestruct H3.
          rewrite <- x3 at 1.
          rewrite <- x in H12 at 1.
          easy.
        }
      }
      (* constructor. *)
      {
        intros.
        apply rcnt_defn0 in H2.
        ddestruct H3.
        rewrite <- x3 in H2 at 1.
        rewrite <- x at 1.
        easy.
      }
      {
        intros.
        apply owns_resp3.
        { easy. }
        {
          rewrite H11. ddestruct H3.
          now rewrite <- x3, <- x at 1.
        }
        { now rewrite <- H1. }
      }
      {
        assert ((cntSt t).(rcnt_num) = (cntSt s).(rcnt_num)).
        {
          ddestruct H3.
          now rewrite <- x3, <- x at 1.
        }
        setoid_rewrite H2.
        setoid_rewrite <- H7.
        intros own Heq1 Heq2. apply owns_wait0.
        easy.
        (* { now rewrite <- H1. } *)
        { now rewrite <- H1. }
      }
      {
        assert ((cntSt t).(rcnt_num) = (cntSt s).(rcnt_num)).
        {
          ddestruct H3.
          now rewrite <- x3, <- x at 1.
        }
        setoid_rewrite H2.
        setoid_rewrite <- H7.
        intro. apply tkts_less0.
        now setoid_rewrite <- H1.
      }
      {
        intros.
        dec_eq_nats j0 i.
        {
          assert (my_tkt = cur_tkt).
          {
            clear - x H13.
            destruct H13 as [H13|H13].
            2: now rewrite <- x in H13 at 1.
            unfold Ready in H13.
            rewrite <- x in H13 at 1.
            clear - H13. ddestruct H13.
            apply equal_f with
              (x:=cur_tkt)
              in x.
            rewrite eqb_id in x.
            dec_eq_nats cur_tkt my_tkt.
            { easy. }
            rewrite eqb_nid in *; auto.
            now rewrite frobProgId in x at 1.
          }
          subst.
          eapply tkts_uniq0.
          { easy. }
          { exact H11. }
          (* {
            assert ((cntSt t).(rcnt_num) = (cntSt s).(rcnt_num)).
            {
              ddestruct H3.
              now rewrite <- x3, <- x at 1.
            }
            rewrite <- H14. exact H12.
          } *)
          {
            unfold Ready.
            rewrite <- H1; auto.
            exact H12.
          }
          { now right. }
        }
        {
          unfold Ready in H12, H13.
          rewrite H1 in H12; auto.
          rewrite H1 in H13; auto.
          assert ((cntSt s).(rcnt_num) = (cntSt t).(rcnt_num)).
          {
            ddestruct H3.
            now rewrite <- x, <- x3 at 1.
          }
          eapply tkts_uniq0.
          { easy. }
          { exact H11. }
          (* { rewrite H15 at 1. exact H12. } *)
          { exact H12. }
          { easy. }
        }
      }
      {
        intros.
        dec_eq_nats j0 i.
        {
          unfold Ready in H12.
          destruct H12 as [H12|H12];
          rewrite <- x in H12 at 1.
          2: easy. apply tkts_eql2 in H12.
          subst. rename my_tkt0 into my_tkt.
          rewrite <- H7 at 1. eapply tkts_boun0
            with (j:=i).
          { easy. }
          { exact H11. }
          { now right. }
        }
        {
          setoid_rewrite <- H7.
          eapply tkts_boun0 with
            (j:=j0).
          { easy. }
          { exact H11. }
          {
            unfold Ready.
            rewrite <- H1; auto.
          }
        }
      }
      {
        unfold not. intros.
        psimpl. ddestruct H3;
        now rewrite <- x in H12 at 1.
      }
      {
        assert (rcnt_num (cntSt t) = rcnt_num (cntSt s)).
        {
          ddestruct H3;
          now rewrite <- x3, <- x at 1.
        }
        setoid_rewrite H2.
        setoid_rewrite <- H7.
        easy.
      }
      { easy. }
    }
  }
  intros cur_tkt.
  split.
  {
    unfold Commit, Precs, LiftSPrec, LiftSRelt.
    intros. do 2 psimpl. rewrite H8 in H2.
    ddestruct H2. destruct H5.
    dec_eq_nats cur_tkt my_tkt.
    {
      rewrite eqb_id in *.
      remember x3.(PState).(lock_owner).
      move Heqo at bottom.
      destruct o. destruct o.
      rename n into j.
      dec_eq_nats j i.
      {
        pose (p' :=
          comRetPoss i
            (comInvPoss i
              x3
              Acq
              (LockUB (Some (i, Acq))))
            Acq
            (LockUB None)
            tt
        ).
        assert (
          VisPossSteps
            x3
            (([] ++ [(i, CallEv Acq)]) ++ [(i, RetEv Acq tt)])
            p'
        ).
        {
          apply retStep.
          apply callStep.
          constructor.
          {
            assert (PState x3 = LockOwned i).
            {
              destruct x3, PState.
              cbn in *. now f_equal.
            }
            rewrite H2.
            split. easy.
            split. easy.
            constructor.
          }
          {
            cbn. rewrite eqb_id.
            split. easy.
            split. easy.
            constructor.
          }
        }
        exists (eq p').
        split.
        { repeat econstructor. }
        split.
        {
          intros. subst.
          eexists. split. easy.
          eapply erase_vis. exact H2.
        }
        split.
        {
          eexists.
          split. easy.
          split. 2:{ cbn. now rewrite eqb_id. }
          split. 2: easy.
          constructor.
          { easy. }
          {
            unfold Ready. intros.
            now rewrite <- x in H12 at 1.
          }
          { easy. }
          {
            intros.
            rewrite <- x in H13 at 1.
            rewrite frobProgId with
              (p:=acq_body _)
              in H13.
            easy.
          }
          { easy. }
          { easy. }
          {
            unfold Ready. intros.
            repeat rewrite <- x in H14 at 1.
            rewrite frobProgId with
              (p:= acq_body cur_tkt)
              in H14.
            now destruct H14.
          }
          {
            intros.
            rewrite <- H11 at 1.
            eapply tkts_boun0 with
              (j:=i).
            { easy. }
            { exact H12. }
            {
              unfold Ready.
              now rewrite <- H1.
            }
          }
          {
            unfold not. intros.
            psimpl. ddestruct H3;
            now rewrite <- x in H13 at 1.
          }
          {
            assert (rcnt_num (cntSt t) = rcnt_num (cntSt s)).
            {
              ddestruct H3;
              now rewrite <- x5, <- x at 1.
            }
            setoid_rewrite H5.
            setoid_rewrite <- H11.
            easy.
          }
        }
        {
          intros. apply eq_inj in H5.
          subst. eexists. split. easy.
          constructor.
          2:{ cbn. now rewrite eqb_nid. }
          2:{ cbn. now rewrite eqb_nid. }
          2: now rewrite H1.
          {
            intros.
            constructor; intros;
            now psimpl.
          }
          { now rewrite <- Heqo at 1. }
        }
      }
      {
        exfalso.
        apply owns_resp0 with
          (my_tkt:=my_tkt)
          (cur_tkt:=my_tkt).
        { now exists j. }
        { easy. }
        {
          ddestruct H3.
          { now rewrite <- x5 at 1. }
          {
            exfalso.
            apply rcnt_defn0.
            { easy. }
            { now rewrite <- x5 at 1. }
          }
        }
        { easy. }
      }
      {
        pose (p' :=
          comRetPoss i
            (comInvPoss i
              x3
              Acq
              (LockAcqRan i))
            Acq
            (LockOwned i)
            tt
        ).
        assert (
          VisPossSteps
            x3
            (([] ++ [(i, CallEv Acq)]) ++ [(i, RetEv Acq tt)])
            p'
        ).
        {
          apply retStep.
          apply callStep.
          constructor.
          {
            assert (PState x3 = LockUnowned).
            {
              destruct x3, PState.
              cbn in *. now f_equal.
            }
            rewrite H2.
            split. easy.
            split. easy.
            constructor.
          }
          {
            cbn. rewrite eqb_id.
            split. easy.
            split. easy.
            constructor.
          }
        }
        exists (eq p').
        split.
        { repeat econstructor. }
        split.
        {
          intros. subst.
          eexists. split. easy.
          eapply erase_vis.
          exact H2.
        }
        split.
        {
          eexists. split. easy.
          split. 2:{ cbn. now rewrite eqb_id. }
          split. 2: easy.
          {
            intros.
            constructor; intros;
            psimpl; cbn in *;
            rewrite ?eqb_id in *;
            try (easy || congruence).
            {
              ddestruct H3.
              { now rewrite <- x at 1. }
              {
                assert (rcnt_num (cntSt s) ≠ None).
                { now apply rcnt_defn0. }
                now rewrite <- x5 in H3 at 1.
              }
            }
            {
              rewrite <- H11 at 1.
              eapply tkts_less0.
              {
                unfold not. intros.
                destruct H13. easy. psimpl.
                now rewrite H8 in H13 at 1.
              }
              { easy. }
              {
                ddestruct H3;
                rewrite <- x5 at 1;
                rewrite <- x in H12 at 1;
                easy.
              }
            }
            (* {
              rewrite <- H11 at 1.
              apply tkts_less0.
              {
                setoid_rewrite H8.
                unfold not. intros.
                now destruct H13; psimpl.
              }
              { easy. }
              {
                assert (rcnt_num (cntSt s) = rcnt_num (cntSt t)).
                {
                  ddestruct H3;
                  now rewrite <- x5, <- x at 1.
                }
                now rewrite H13 at 1.
              }
            } *)
            {
              unfold Ready in H13.
              repeat rewrite <- x in H13 at 1.
              rewrite frobProgId with
                (p:= acq_body cur_tkt)
                in H13.
              now destruct H13.
            }
            {
              rewrite <- H11 at 1.
              eapply tkts_boun0 with
                (j:=j).
              { easy. }
              { exact H12. }
              {
                dec_eq_nats j i.
                {
                  unfold Ready in H13.
                  setoid_rewrite <- x in H13.
                  destruct H13. easy. symmetry in H13.
                  now rewrite frobProgId in H13 at 1.
                }
                unfold Ready.
                now repeat rewrite <- H1.
              }
            }
            {
              unfold not. intros.
              psimpl. ddestruct H3;
              now rewrite <- x in H13 at 1.
            }
            {
              ddestruct H3;
              rewrite <- x in H12 at 1.
              2: easy. cbn in *. ddestruct H12.
              rewrite <- H11 at 1.
              eapply tkts_boun0 with
                (j:=i).
              { easy. }
              { easy. }
              { now left. }
            }
          }
        }
        {
          intros. apply eq_inj in H5.
          subst. eexists. split. easy.
          constructor.
          2:{ cbn. now rewrite eqb_nid. }
          2:{ cbn. now rewrite eqb_nid. }
          2: now rewrite H1.
          (* 2:{
            rewrite <- Heqo at 1.
            intros. now ddestruct H12.
          }
          2: now rewrite <- Heqo at 1. *)
          {
            intros. destruct H12.
            constructor.
            { easy. }
            {
              intros. psimpl. ddestruct H15.
              rename x3 into i. unfold not.
              assert (rcnt_num (cntSt t) = rcnt_num (cntSt s)).
              {
                ddestruct H3.
                now rewrite <- x3, <- x at 1.
                now rewrite <- x in H14 at 1.
              }
              intros. subst. eapply tkts_uniq1.
              { now rewrite <- Heqo at 1. }
              { exact H12. }
              (* { rewrite <- H15 at 1. exact H14. } *)
              {
                left. unfold Ready.
                rewrite <- H1; auto.
                exact H13.
              }
              {
                assert (cur_tkt = my_tkt).
                {
                  clear - H3 H14.
                  ddestruct H3.
                  {
                    rewrite <- x in H14 at 1.
                    cbn in *. now ddestruct H14.
                  }
                  {
                    now rewrite <- x in H14 at 1.
                  }
                }
                left.
                now subst.
              }
            }
            {
              intros.
              ddestruct H3.
              { now rewrite <- x at 1. }
              {
                exfalso.
                assert (rcnt_num (cntSt s) ≠ None).
                {
                  apply rcnt_defn1.
                  { now rewrite <- Heqo. }
                }
                now rewrite <- x3 in H3 at 1.
              }
            }
            {
              intros. unfold not.
              intros. subst. psimpl.
              ddestruct H15. rename x3 into i.
              assert (my_tkt = cur_tkt).
              {
                ddestruct H3;
                rewrite <- x in H13 at 1.
                { cbn in *. now ddestruct H13. }
                { easy. }
              }
              subst.
              eapply tkts_uniq1.
              { now rewrite <- Heqo. }
              { exact H12. }
              (* {
                assert (rcnt_num (cntSt s) = rcnt_num (cntSt t)).
                {
                  ddestruct H3;
                  now rewrite <- x, <- x3 at 1.
                }
                rewrite H15 at 1. exact H13.
              } *)
              {
                right.
                rewrite <- H1; auto.
                exact H14.
              }
              { now left. }
            }
            {
              cbn. intros. ddestruct H12.
              exfalso. ddestruct H3.
              2: now rewrite <- x in H13 at 1.
              rewrite <- x in H13 at 1. cbn in *.
              ddestruct H13. rename my_tkt into cur_tkt.
              assert (cur_tkt < faiVal s).
              {
                eapply tkts_boun1 with
                  (j:=i).
                { now rewrite <- Heqo at 1. }
                { easy. }
                { now left. }
              }
              subst.
              rewrite H11 in H3 at 1.
              destruct t, t0, LState.
              cbn in *. lia.
            }
            {
              assert ((cntSt t).(rcnt_num) = (cntSt s).(rcnt_num)).
              {
                ddestruct H3.
                { now rewrite <- x3, <- x at 1. }
                {
                  assert (rcnt_num (cntSt s) ≠ None).
                  {
                    apply rcnt_defn1.
                    { now rewrite <- Heqo. }
                  }
                  now rewrite <- x3 in H3 at 1.
                }
              }
              setoid_rewrite H12.
              setoid_rewrite <- H11.
              intros Heq1 Heq2. apply tkts_less1.
              { now setoid_rewrite <- H1. }
              { now rewrite <- Heqo at 1. }
            }
            {
              intros.
              assert (j0 ≠ i).
              {
                unfold not.
                intro. subst.
                unfold Ready in H15.
                repeat rewrite <- x in H15 at 1.
                rewrite frobProgId with
                  (p:= acq_body _)
                  in H15.
                now destruct H15.
              }
              (* assert (rcnt_num (cntSt s) = rcnt_num (cntSt t)).
              {
                ddestruct H3.
                { now rewrite <- x3, <- x at 1. }
                { now rewrite <- x in H14 at 1. }
              } *)
              eapply tkts_uniq1.
              { now rewrite <- Heqo. }
              { exact H13. }
              (* { rewrite H18. exact H14. } *)
              {
                unfold Ready.
                rewrite <- H1; auto.
                exact H14.
              }
              {
                unfold Ready.
                now rewrite <- H1.
              }
            }
            {
              intros.
              assert (j0 ≠ i).
              {
                unfold not.
                intro. subst.
                unfold Ready in H14.
                repeat rewrite <- x in H14 at 1.
                rewrite frobProgId with
                  (p:= acq_body _)
                  in H14.
                now destruct H14.
              }
              rewrite <- H11 at 1.
              eapply tkts_boun1 with
                (j:=j0).
              { now rewrite <- Heqo. }
              { exact H13. }
              {
                unfold Ready.
                now rewrite <- H1.
              }
            }
            {
              unfold not. intros.
              psimpl. ddestruct H3;
              now rewrite <- x in H14 at 1.
            }
            {
              move H3 at bottom.
              intros. ddestruct H3;
              rewrite <- x in H13 at 1;
              cbn in *; ddestruct H13.
              setoid_rewrite <- H11.
              eapply tkts_boun1 with
                (j:=i).
              { now rewrite <- Heqo at 1. }
              { easy. }
              { now left. }
            }
          }
          { now rewrite <- Heqo at 1. }
        }
      }
      {
        pose (p' :=
          comRetPoss i
            (comInvPoss i
              x3
              Acq
              (LockUB (Some (i, Acq))))
            Acq
            (LockUB None)
            tt
        ).
        assert (
          VisPossSteps
            x3
            (([] ++ [(i, CallEv Acq)]) ++ [(i, RetEv Acq tt)])
            p'
        ).
        {
          apply retStep.
          apply callStep.
          constructor.
          {
            assert (PState x3 = LockUB None).
            {
              destruct x3, PState.
              cbn in *. now f_equal.
            }
            rewrite H2.
            split. easy.
            split. easy.
            constructor.
          }
          {
            cbn. rewrite eqb_id.
            split. easy.
            split. easy.
            constructor.
          }
        }
        exists (eq p').
        split.
        { repeat econstructor. }
        split.
        {
          intros. subst.
          eexists. split. easy.
          eapply erase_vis. exact H2.
        }
        split.
        {
          eexists.
          split. easy.
          split. 2:{ cbn. now rewrite eqb_id. }
          split. 2: easy.
          constructor.
          { easy. }
          {
            unfold Ready. intros.
            now rewrite <- x in H12 at 1.
          }
          { easy. }
          {
            intros.
            rewrite <- x in H13 at 1.
            rewrite frobProgId with
              (p:=acq_body _)
              in H13.
            easy.
          }
          { easy. }
          { easy. }
          { easy. }
          { easy. }
          {
            unfold not. intros.
            psimpl. ddestruct H3;
            now rewrite <- x in H13 at 1.
          }
          { easy. }
        }
        {
          intros. apply eq_inj in H5.
          subst. eexists. split. easy.
          constructor.
          2:{ cbn. now rewrite eqb_nid. }
          2:{ cbn. now rewrite eqb_nid. }
          2: now rewrite H1.
          (* 2:{ now rewrite <- Heqo at 1. }
          2:{ now rewrite <- Heqo. } *)
          {
            intros.
            constructor; intros;
            now psimpl.
          }
          { easy. }
        }
      }
    }
    {
      rewrite eqb_nid in *; auto.
      exists (eq x3).
      split.
      { repeat econstructor. }
      split.
      {
        intros. subst.
        repeat econstructor.
      }
      split.
      {
        exists x3.
        split. easy.
        split. 2: easy.
        split. 2: easy.
        constructor.
        { easy. }
        {
          unfold Ready. intros.
          rewrite <- x in H12 at 1.
          easy.
        }
        {
          intros.
          apply rcnt_defn0 in H5.
          ddestruct H3.
          { now rewrite <- x at 1. }
          { now rewrite <- x6 in H5 at 1. }
        }
        {
          intros.
          rewrite <- x in H13 at 1.
          apply tkts_eql in H13. subst.
          ddestruct H3;
          rewrite <- x in H12 at 1.
          { now ddestruct H12. }
          { easy. }
        }
        {
          intros.
          ddestruct H3;
          rewrite <- x in H12 at 1.
          2: easy. eapply owns_wait0.
          easy.
          (* { now rewrite H8 at 1. } *)
          {
            unfold not. intros. psimpl.
            setoid_rewrite H8 in H3.
            now destruct H3; psimpl.
          }
          { easy. }
          { now rewrite <- x6 at 1. }
          { rewrite H11 at 1. now ddestruct H12. }
        }
        {
          intros.
          ddestruct H3;
          rewrite <- x in H12 at 1.
          2: easy. rewrite <- H11 at 1.
          eapply tkts_less0.
          {
            setoid_rewrite H8.
            unfold not. intros.
            now destruct H3; psimpl.
          }
          { easy. }
          { ddestruct H12. now rewrite <- x6 at 1. }
        }
        {
          intros.
          (* ddestruct H3. *)
          (* rewrite <- x in H13 at 1. *)
          (* 2: easy. ddestruct H13. *)
          eapply tkts_uniq0.
          { easy. }
          { exact H12. }
          {
            unfold Ready in H13.
            repeat rewrite <- x in H13 at 1.
            destruct H13. easy.
            apply tkts_eql in H13. subst.
            left. exact H8.
          }
          {
            unfold Ready in H14.
            now rewrite H1 in H14.
          }
        }
        {
          intros.
          rewrite <- H11 at 1.
          dec_eq_nats j i.
          {
            unfold Ready in H13.
            setoid_rewrite <- x in H13.
            destruct H13. easy.
            apply tkts_eql in H13. subst.
            eapply tkts_boun0 with
              (j:=i).
            { easy. }
            { easy. }
            { now left. }
          }
          eapply tkts_boun0 with
            (j:=j).
          { easy. }
          { exact H12. }
          {
            unfold Ready.
            now rewrite <- H1.
          }
        }
        {
          unfold not. intros.
          psimpl. ddestruct H3;
          now rewrite <- x in H13 at 1.
        }
        {
          assert (rcnt_num (cntSt t) = rcnt_num (cntSt s)).
          {
            ddestruct H3;
            now rewrite <- x6, <- x at 1.
          }
          setoid_rewrite H5.
          setoid_rewrite <- H11.
          easy.
        }
      }
      {
        intros. apply eq_inj in H5.
        subst. eexists. split. easy.
        constructor.
        2: easy.
        2: easy.
        (* 2: now rewrite H1.
        2: easy. *)
        intros. destruct H12.
        assert (
          ∀ tkt,
            Some tkt = rcnt_num (cntSt t) ->
            cur_tkt = tkt /\
            rcnt_num (cntSt s) = Some cur_tkt
        ).
        {
          intros.
          ddestruct H3;
          rewrite <- x in H12 at 1;
          ddestruct H12.
          now rewrite <- x6 at 1.
        }
        constructor.
        { easy. }
        {
          intros.
          eapply owns_resp1.
          { easy. }
          {
            unfold Ready.
            now rewrite <- H1.
          }
          apply H12 in H15.
          now psimpl.
        }
        {
          intros.
          apply rcnt_defn1 in H13.
          ddestruct H3;
          rewrite <- x6 in H13 at 1;
          auto.
          now rewrite <- x at 1.
        }
        {
          intros.
          eapply owns_resp4.
          { easy. }
          {
            apply H12 in H14.
            now psimpl.
          }
          { now rewrite <- H1. }
        }
        {
          intros.
          eapply owns_wait1 with
            (cur_tkt:=cur_tkt0).
          easy.
          (* { now rewrite <- H1. } *)
          { now setoid_rewrite <- H1. }
          { easy. }
          {
            apply H12 in H14.
            now psimpl.
          }
          { now rewrite H11 at 1. }
        }
        {
          intros.
          rewrite <- H11 at 1.
          eapply tkts_less1.
          { now setoid_rewrite <- H1. }
          { easy. }
          {
            apply H12 in H14.
            now psimpl.
          }
        }
        {
          intros.
          (* apply H12 in H15. psimpl. *)
          eapply tkts_uniq1.
          { easy. }
          { exact H14. }
          {
            unfold Ready.
            repeat rewrite <- H1 at 1; auto.
            exact H15.
          }
          {
            unfold Ready in H16.
            dec_eq_nats j0 i.
            {
              repeat rewrite <- x in H16 at 1.
              destruct H16. easy.
              apply tkts_eql in H16.
              subst. now left.
            }
            {
              unfold Ready.
              repeat rewrite <- H1 at 1.
              all: easy.
            }
          }
        }
        {
          intros.
          rewrite <- H11 at 1.
          eapply tkts_boun1 with
            (j:=j0).
          { easy. }
          { exact H14. }
          {
            unfold Ready in H15.
            dec_eq_nats j0 i.
            {
              repeat rewrite <- x in H15 at 1.
              destruct H15. easy.
              apply tkts_eql in H15.
              subst. now left.
            }
            {
              unfold Ready.
              repeat rewrite <- H1 at 1.
              all: easy.
            }
          }
        }
        {
          unfold not. intros.
          psimpl. ddestruct H3;
          now rewrite <- x in H15 at 1.
        }
        {
          move H3 at bottom.
          assert (rcnt_num (cntSt t) = rcnt_num (cntSt s)).
          {
            ddestruct H3;
            now rewrite <- x6, <- x at 1.
          }
          setoid_rewrite H13.
          setoid_rewrite <- H11.
          easy.
        }
        { now rewrite H1. }
        { easy. }
      }
    }
  }
  destruct (cur_tkt =? my_tkt).
  {
    left. pfold.
    econstructor.
    unfold sub, subRelt, Posts, LiftSPrec, LiftSRelt.
    intros. psimpl. now exists x4.
  }
  {
    right.
    apply rec.
    {
      unfold sub, subRelt.
      intros. now psimpl.
    }
  }
Qed.

Lemma classicT_left {P : Prop} :
  ∀ p : P,
    classicT P = left _ p.
Proof.
  intros.
  destruct (classicT P).
  {
    f_equal.
    apply proof_irrelevance.
  }
  { easy. }
Qed.

Lemma classicT_right {P : Prop} :
  ∀ p : ¬P,
    classicT P = right _ p.
Proof.
  intros.
  destruct (classicT P).
  2:{
    f_equal.
    apply proof_irrelevance.
  }
  { easy. }
Qed.

Lemma rel_correct {T} (i : Name T) :
  VerifyProg i
    (LiftSRelt (Rely i))
    (LiftSRelt (Guar i))
    (prComp
      (LiftSPrec (Precs i Rel))
      (TInvoke ticketLockImpl i unit Rel) ->>
      LiftSRelt (Rely i))
    rel
    (λ v, LiftSRelt (Posts i Rel v)).
Proof.
  unfold rel.
  eapply weakenPrec with
    (P:=λ _ _, LiftSPrec (λ s ρ,
      (Inv i s ρ /\ fst s i = Cont Rel rel) /\
      PCalls ρ i = CallPoss Rel /\
      PRets ρ i = RetIdle)).
  2:{
    unfold sub, subRelt, Precs, LiftSPrec, LiftSRelt.
    intros. psimpl.
    assert (exists x, x0 = eq x).
    {
      eapply Invoke_pres_single.
      exact H1.
    }
    psimpl.
    specialize (H0 x2 eq_refl). psimpl.
    eexists. split. easy.
    unfold TInvoke in H1. psimpl.
    apply eq_sing in H4. psimpl.
    destruct H0.
    cut (
      (Inv i t x0 /\ fst t i = Cont Rel rel) /\
      PCalls x0 i = CallPoss Rel /\
      PRets x0 i = RetIdle
    ).
    { easy. }
    split. 2: now rewrite <- pres_call0, <- pres_ret0.
    split.
    {
      apply pres_inv0. destruct H2.
      constructor.
      { now rewrite H5 at 1. }
      {
        intros.
        unfold Ready in H2.
        destruct H1. ddestruct H1.
        now rewrite <- x in H2 at 1.
      }
      { now rewrite H5, <- H3 at 1. }
      (* constructor. *)
      {
        intros.
        destruct H1. ddestruct H1.
        rewrite <- x in H4 at 1.
        ddestruct H4.
      }
      {
        intros.
        eapply owns_wait0.
        {
          destruct H1. cbn in *.
          ddestruct H1. easy.
          (* now rewrite <- x4. *)
        }
        {
          unfold not. intros. psimpl.
          unfold TIdle in H. psimpl.
          setoid_rewrite H in H10.
          now destruct H10; psimpl.
        }
        { now rewrite <- H5 at 1. }
        { rewrite H3 at 1. exact H2. }
        { now rewrite H3 at 1. }
      }
      {
        intros.
        rewrite <- H3 at 1.
        apply tkts_less0.
        {
          unfold not. intros. psimpl.
          destruct H1. ddestruct H1. cbn in *.
          setoid_rewrite <- x4 in H4.
          now destruct H4; psimpl.
        }
        { now rewrite <- H5 at 1. }
        { now rewrite H3 at 1. }
      }
      {
        intros. destruct H1.
        cbn in *. ddestruct H1.
        unfold Ready in H4.
        destruct H4 as [H4 | H4];
        rewrite <- x in H4 at 1.
        { easy. }
        {
          rewrite frobProgId with
            (p:=ticketLockImpl _ _)
            in H4.
          rewrite frobProgId with
            (p:=acq_body _)
            in H4.
          easy.
        }
      }
      {
        unfold Ready. intros.
        destruct H1. cbn in *.
        rewrite <- H3 at 1.
        eapply tkts_boun0 with
          (j:=j).
        { now rewrite <- H5 at 1. }
        { exact H2. }
        {
          dec_eq_nats j i.
          {
            ddestruct H1.
            rewrite frobProgId in x at 1.
            setoid_rewrite <- x in H4.
            now destruct H4.
          }
          unfold Ready.
          now repeat rewrite H10 at 1.
        }
      }
      {
        setoid_rewrite H5.
        setoid_rewrite <- H3 at 1.
        easy.
      }
      {
        setoid_rewrite H5.
        setoid_rewrite <- H3.
        easy.
      }
    }
    {
      destruct H1. ddestruct H0.
      cbn in *. now rewrite <- pres_ths0 at 1.
    }
  }
  eapply weakenPost.
  eapply (lemCall
    (Q:=λ _ _, LiftSPrec (λ (s : InterState _ (VE _)) (ρ : Poss (VF _)),
      (
        (Inv i s ρ /\
          fst s i = UCall Rel (inr Inc) Return) /\
        PCalls ρ i = CallPoss Rel /\
        PRets ρ i = RetIdle)
      \/
      (ρ.(PState).(lock_owner) = None /\
        (Inv i s ρ /\
          fst s i = UCall Rel (inr Inc) Return) /\
        PCalls ρ i = CallDone Rel /\
        PRets ρ i = RetPoss Rel tt)))
    (S:=λ _ _ _, LiftSPrec (λ s ρ,
      (Inv i s ρ /\
        fst s i = Cont Rel (Return tt)) /\
      PCalls ρ i = CallDone Rel /\
      PRets ρ i = RetPoss Rel tt))).
  {
    unfold
      Stable, stableRelt,
      sub, subRelt,
      LiftSPrec, LiftSRelt.
    intros. psimpl.
    specialize (H0 x1 eq_refl).
    psimpl. eexists. split. easy.
    destruct H1; psimpl.
    {
      left.
      split. split.
      { now apply H0. }
      { now rewrite <- H0.(pres_ths) at 1. }
      split.
      { now rewrite <- H0.(pres_call) at 1. }
      { now rewrite <- H0.(pres_ret) at 1. }
    }
    {
      right.
      split. now apply H0.
      split. split.
      { now apply H0. }
      { now rewrite <- H0.(pres_ths) at 1. }
      split.
      { now rewrite <- H0.(pres_call) at 1. }
      { now rewrite <- H0.(pres_ret) at 1. }
    }
  }
  {
    unfold Stable, stablePost.
    intros []. apply acq_inv_stable.
  }
  {
    unfold Commit, Precs, LiftSPrec, LiftSRelt.
    intros. do 2 psimpl.
    decide_prop (x1.(PState).(lock_owner) = Some (Some i)).
    {
      ddestruct H.
      2:{
        destruct H3.
        exfalso. apply rcnt_wait0.
        split. easy.
        exists i0.
        now rewrite <- x2 at 1.
      }
      assert (rcnt_num (cntSt s) = rcnt_num (cntSt t)).
      { now rewrite <- x2, <- x at 1. }
      exists (eq x1).
      split.
      { repeat econstructor. }
      split.
      {
        intros. subst.
        repeat econstructor.
      }
      rewrite H6 in H1.
      ddestruct H1.
      split.
      {
        eexists. split. easy.
        left.
        split. 2: easy.
        split.
        {
          destruct H3.
          constructor.
          { easy. }
          {
            unfold Ready. intros.
            now rewrite <- x in H3 at 1.
          }
          { now setoid_rewrite <- H. }
          { now setoid_rewrite <- x. }
          {
            setoid_rewrite <- x.
            intros. exfalso.
            apply nrel. right.
            repeat eexists.
          }
          {
            setoid_rewrite <- x.
            intros. exfalso.
            apply nrel. right.
            repeat eexists.
          }
          {
            unfold Ready.
            setoid_rewrite <- x.
            intros. now destruct H11.
          }
          {
            intros.
            rewrite <- H9 at 1.
            eapply tkts_boun0 with
              (j:=j).
            { easy. }
            { exact H3. }
            {
              dec_eq_nats j i.
              {
                unfold Ready in H11.
                setoid_rewrite <- x in H11.
                now destruct H11.
              }
              unfold Ready.
              now setoid_rewrite <- H0.
            }
          }
          {
            unfold not at 1. intros.
            psimpl. rewrite <- x4 in H11 at 1.
            cbn in *. now ddestruct H11.
          }
          {
            setoid_rewrite <- H.
            setoid_rewrite <- H9.
            easy.
          }
        }
        { easy. }
      }
      {
        intros. apply eq_inj in H1.
        subst. eexists. split. easy.
        constructor.
        {
          intros. destruct H11.
          constructor.
          { easy. }
          {
            unfold Ready.
            setoid_rewrite H0; auto.
            setoid_rewrite <- H.
            easy.
          }
          { now setoid_rewrite <- H. }
          {
            unfold Ready.
            setoid_rewrite H0; auto.
            setoid_rewrite <- H.
            easy.
          }
          {
            setoid_rewrite <- H9.
            setoid_rewrite H0; auto.
            setoid_rewrite <- H.
            easy.
          }
          {
            setoid_rewrite <- H9.
            setoid_rewrite H0; auto.
            setoid_rewrite <- H.
            easy.
          }
          {
            unfold Ready. intros.
            assert (j0 ≠ i).
            {
              unfold not. intros. subst.
              setoid_rewrite <- x in H14.
              now destruct H14.
            }
            eapply tkts_uniq0 with
              (cur_tkt:=cur_tkt).
            { easy. }
            { exact H12. }
            (* { rewrite H at 1. exact H13. } *)
            { now setoid_rewrite H0 in H13. }
            { now setoid_rewrite H0 in H14. }
          }
          {
            unfold Ready. intros.
            setoid_rewrite <- H9.
            eapply tkts_boun0.
            { easy. }
            { exact H12. }
            {
              assert (j0 ≠ i).
              {
                unfold not. intros. subst.
                setoid_rewrite <- x in H13.
                now destruct H13.
              }
              setoid_rewrite H0 in H13; auto.
              exact H13.
            }
          }
          {
            unfold not. intros. psimpl.
            rewrite H10 in H11 at 1.
            now ddestruct H11.
          }
          {
            setoid_rewrite <- H.
            setoid_rewrite <- H9.
            easy.
          }
        }
        { easy. }
        { easy. }
        { now rewrite H0 at 1. }
        { easy. }
      }
    }
    {
      pose (p' :=
        comRetPoss i
          (comInvPoss i
            x1
            Rel
            (LockUB (Some (i, Rel))))
          Rel
          (LockUB None)
          tt
      ).
      assert (
        VisPossSteps
          x1
          (([] ++ [(i, CallEv Rel)]) ++ [(i, RetEv Rel tt)])
          p'
      ).
      {
        apply retStep.
        apply callStep.
        constructor.
        {
          destruct x1, PState. cbn in *.
          assert (lock_pend = None) by apply H3.
          subst. destruct lock_owner. destruct o.
          rename n into j. dec_eq_nats j i.
          { easy. }
          { repeat (easy || constructor). }
          { repeat (easy || constructor). }
          { repeat (easy || constructor). }
        }
        {
          cbn. rewrite eqb_id.
          repeat (easy || constructor).
        }
      }
      exists (eq p').
      split.
      { repeat econstructor. }
      split.
      {
        intros. subst. eexists.
        split. easy. eapply erase_vis.
        exact H11.
      }
      split.
      {
        eexists. split. easy. cbn.
        right. split. easy.
        rewrite eqb_id.
        split. split.
        { constructor; intros; now psimpl. }
        { rewrite H6 in H1. now ddestruct H1. }
        { easy. }
      }
      {
        intros. apply eq_inj in H12. subst.
        eexists. split. easy. constructor.
        {
          intros.
          constructor; intros; now psimpl.
        }
        { cbn. now rewrite eqb_nid. }
        { cbn. now rewrite eqb_nid. }
        { now rewrite H0 at 1. }
        { easy. }
      }
    }
  }
  intros [].
  {
    
    unfold Commit, Precs, LiftSRelt.
    intros. do 2 psimpl. clear H.
    unfold LiftSPrec in *. psimpl.
    destruct H3; psimpl.
    {
      remember (x3.(PState).(lock_owner)).
      destruct o. destruct o.
      rename n into j.
      dec_eq_nats j i.
      {
        pose (p' :=
          comRetPoss i
            (comInvPoss i
              x3
              Rel
              (LockRelRan i))
            Rel
            LockUnowned
            tt
        ).
        assert (
          VisPossSteps
            x3
            (([] ++ [(i, CallEv Rel)]) ++ [(i, RetEv Rel tt)])
            p'
        ).
        {
          apply retStep.
          apply callStep.
          constructor.
          {
            assert (PState x3 = LockOwned i).
            {
              destruct x3, PState, H.
              cbn in *. now subst.
            }
            rewrite H10.
            repeat (easy || constructor).
          }
          {
            cbn. rewrite eqb_id.
            repeat (easy || constructor).
          }
        }
        exists (eq p').
        split.
        { repeat econstructor. }
        split.
        {
          intros. subst. eexists.
          split. easy. eapply erase_vis.
          exact H10.
        }
        rewrite H9 in H1.
        ddestruct H1.
        split.
        {
          eexists. split. easy.
          split. 2:{ cbn. now rewrite eqb_id. }
          split. 2: easy.
          constructor; cbn;
          unfold Ready;
          try setoid_rewrite <- x;
          try setoid_rewrite <- Heqo;
          intros; try now psimpl.
          {
            assert (lock_owner (PState x3) ≠ None).
            { now rewrite <- Heqo at 1. }
            apply H in H11.
            ddestruct H2;
            rewrite <- x2 in H11 at 1;
            rewrite <- x at 1;
            easy.
          }
          { now ddestruct H1. }
          {
            rewrite <- H7 at 1.
            move H at bottom.
            ddestruct H2;
            rewrite <- x in H11 at 1;
            try easy. cbn in *.
            ddestruct H11.
            assert (n < faiVal s).
            {
              eapply H.(wait_less).
              { symmetry. exact Heqo. }
              { now rewrite <- x2 at 1. }
            }
            easy.
          }
          { now destruct H12. }
          {
            rewrite <- H7 at 1.
            destruct H. eapply tkts_boun0.
            { now rewrite <- Heqo at 1. }
            { exact H11. }
            {
              unfold Ready.
              rewrite <- H0.
              exact H12.
              {
                unfold not. intros. subst.
                setoid_rewrite <- x in H12.
                now destruct H12.
              }
            }
          }
        }
        {
          intros. apply eq_inj in H1.
          subst. eexists. split. easy.
          constructor.
          {
            intros. destruct H11.
            constructor; cbn;
            unfold Ready;
            try setoid_rewrite <- x;
            try setoid_rewrite <- Heqo;
            intros; try now psimpl.
            {
              assert (lock_owner (PState x1) ≠ None).
              { now rewrite <- Heqo at 1. }
              apply H in H12.
              ddestruct H2;
              rewrite <- x3 in H12 at 1;
              rewrite <- x at 1;
              easy.
            }
            { now ddestruct H11. }
            {
              assert (
                ∀ i,
                  x1.(PState).(lock_owner) = Some (Some i) ->
                  ∀ cur_tkt,
                    Some cur_tkt = rcnt_num (cntSt s) ->
                    cur_tkt < faiVal s
              ) by easy.
              move Heqo at bottom.
              assert (rcnt_num (cntSt s) ≠ None).
              {
                apply rcnt_defn0.
                now rewrite <- Heqo at 1.
              }
              move H2 at bottom.
              ddestruct H2;
              try now rewrite <- x3 in H14 at 1.
              symmetry in Heqo.
              rewrite <- x in H12 at 1.
              cbn in *. ddestruct H12.
              apply H13 with
                (cur_tkt:=n)
                in Heqo.
              2: now rewrite <- x3 at 1.
              rewrite <- H7 at 1.
              easy.
            }
            {
              eapply tkts_uniq0 with
                (cur_tkt:=cur_tkt).
              { now rewrite <- Heqo at 1. }
              { exact H12. }
              {
                unfold Ready.
                now rewrite <- H0.
              }
              {
                unfold Ready.
                rewrite <- H0; auto.
                unfold not. intro. subst.
                setoid_rewrite <- x in H14.
                now destruct H14.
              }
            }
            {
              rewrite <- H7 at 1.
              destruct H. eapply tkts_boun0
                with (j:=j0).
              { now rewrite <- Heqo at 1. }
              { exact H12. }
              {
                unfold Ready.
                rewrite <- H0; auto.
                unfold not. intros. subst.
                setoid_rewrite <- x in H13.
                now destruct H13.
              }
            }
          }
          { cbn. now rewrite eqb_nid. }
          { cbn. now rewrite eqb_nid. }
          { now rewrite H0. }
          { now rewrite <- Heqo at 1. }
        }
      }
      {
        pose (p' :=
          comRetPoss i
            (comInvPoss i
              x3
              Rel
              (LockUB (Some (i, Rel))))
            Rel
            (LockUB None)
            tt
        ).
        assert (
          VisPossSteps
            x3
            (([] ++ [(i, CallEv Rel)]) ++ [(i, RetEv Rel tt)])
            p'
        ).
        {
          apply retStep.
          apply callStep.
          constructor.
          {
            assert (PState x3 = LockOwned j).
            {
              destruct x3, PState, H.
              cbn in *. now subst.
            }
            rewrite H11.
            repeat (easy || constructor).
          }
          {
            cbn. rewrite eqb_id.
            repeat (easy || constructor).
          }
        }
        exists (eq p').
        split.
        { repeat econstructor. }
        split.
        {
          intros. subst. eexists.
          split. easy. eapply erase_vis.
          exact H11.
        }
        rewrite H9 in H1.
        ddestruct H1.
        split.
        {
          eexists. split. easy.
          split. 2:{ cbn. now rewrite eqb_id. }
          split. 2: easy.
          constructor; cbn;
          unfold Ready;
          try setoid_rewrite <- x;
          try setoid_rewrite <- Heqo;
          intros; try now psimpl.
        }
        {
          intros. apply eq_inj in H1.
          subst. eexists. split. easy.
          constructor.
          {
            intros. destruct H12.
            constructor; cbn;
            intros; now psimpl.
          }
          { cbn. now rewrite eqb_nid. }
          { cbn. now rewrite eqb_nid. }
          { now rewrite H0. }
          { now rewrite <- Heqo at 1. }
        }
      }
      {
        pose (p' :=
          comRetPoss i
            (comInvPoss i
              x3
              Rel
              (LockUB (Some (i, Rel))))
            Rel
            (LockUB None)
            tt
        ).
        assert (
          VisPossSteps
            x3
            (([] ++ [(i, CallEv Rel)]) ++ [(i, RetEv Rel tt)])
            p'
        ).
        {
          apply retStep.
          apply callStep.
          constructor.
          {
            assert (PState x3 = LockUnowned).
            {
              destruct x3, PState, H.
              cbn in *. now subst.
            }
            rewrite H10.
            repeat (easy || constructor).
          }
          {
            cbn. rewrite eqb_id.
            repeat (easy || constructor).
          }
        }
        exists (eq p').
        split.
        { repeat econstructor. }
        split.
        {
          intros. subst. eexists.
          split. easy. eapply erase_vis.
          exact H10.
        }
        rewrite H9 in H1.
        ddestruct H1.
        split.
        {
          eexists. split. easy.
          split. 2:{ cbn. now rewrite eqb_id. }
          split. 2: easy.
          constructor; cbn;
          unfold Ready;
          try setoid_rewrite <- x;
          try setoid_rewrite <- Heqo;
          intros; try now psimpl.
        }
        {
          intros. apply eq_inj in H1.
          subst. eexists. split. easy.
          constructor.
          {
            intros. destruct H11.
            constructor; cbn;
            intros; now psimpl.
          }
          { cbn. now rewrite eqb_nid. }
          { cbn. now rewrite eqb_nid. }
          { now rewrite H0. }
          { now rewrite <- Heqo at 1. }
        }
      }
      {
        pose (p' :=
          comRetPoss i
            (comInvPoss i
              x3
              Rel
              (LockUB (Some (i, Rel))))
            Rel
            (LockUB None)
            tt
        ).
        assert (
          VisPossSteps
            x3
            (([] ++ [(i, CallEv Rel)]) ++ [(i, RetEv Rel tt)])
            p'
        ).
        {
          apply retStep.
          apply callStep.
          constructor.
          {
            assert (PState x3 = LockUB None).
            {
              destruct x3, PState, H.
              cbn in *. now subst.
            }
            rewrite H10.
            repeat (easy || constructor).
          }
          {
            cbn. rewrite eqb_id.
            repeat (easy || constructor).
          }
        }
        exists (eq p').
        split.
        { repeat econstructor. }
        split.
        {
          intros. subst. eexists.
          split. easy. eapply erase_vis.
          exact H10.
        }
        rewrite H9 in H1.
        ddestruct H1.
        split.
        {
          eexists. split. easy.
          split. 2:{ cbn. now rewrite eqb_id. }
          split. 2: easy.
          constructor; cbn;
          unfold Ready;
          try setoid_rewrite <- x;
          try setoid_rewrite <- Heqo;
          intros; try now psimpl.
        }
        {
          intros. apply eq_inj in H1.
          subst. eexists. split. easy.
          constructor.
          {
            intros. destruct H11.
            constructor; cbn;
            intros; now psimpl.
          }
          { cbn. now rewrite eqb_nid. }
          { cbn. now rewrite eqb_nid. }
          { now rewrite H0. }
          { now rewrite <- Heqo at 1. }
        }
      }
    }
    {
      exists (eq x3).
      split.
      { repeat econstructor. }
      split.
      {
        intros. subst.
        repeat econstructor.
      }
      rewrite H10 in H1.
      ddestruct H1.
      split.
      {
        destruct H3.
        eexists. split. easy.
        split. 2: easy.
        split. 2: easy.
        constructor.
        { easy. }
        {
          unfold Ready.
          now setoid_rewrite <- x.
        }
        {
          intros.
          ddestruct H2.
          { now rewrite <- x at 1. }
          {
            apply rcnt_defn0 in H2.
            now rewrite <- x2 in H2 at 1.
          }
          {
            apply rcnt_defn0 in H1.
            now rewrite <- x2 in H1 at 1.
          }
          {
            apply rcnt_defn0 in H1.
            now rewrite <- x2 in H1 at 1.
          }
        }
        { now setoid_rewrite <- x. }
        { now setoid_rewrite H. }
        { now setoid_rewrite H. }
        {
          unfold Ready.
          setoid_rewrite <- x.
          intros. now destruct H11.
        }
        {
          intros.
          rewrite <- H7 at 1.
          eapply tkts_boun0 with
            (j:=j).
          { easy. }
          { exact H3. }
          {
            unfold Ready.
            now setoid_rewrite <- H0.
          }
        }
        {
          unfold not at 1.
          intros. psimpl.
          ddestruct H2;
          now rewrite <- x in H11 at 1.
        }
        { now setoid_rewrite H. }
      }
      {
        intros. apply eq_inj in H1.
        subst. eexists. split. easy.
        constructor.
        {
          intros. destruct H11.
          constructor;
          try setoid_rewrite H;
          intros; now psimpl.
        }
        { easy. }
        { easy. }
        { now rewrite H0. }
        { easy. }
      }
    }
  }
  {
    unfold
      sub, subRelt, Posts,
      LiftSPrec, LiftSRelt.
    intros. psimpl.
    eexists. split. easy.
    now destruct v.
  }
Qed.

Theorem ticketLockCorrect {T} :
  VerifyImpl (VE T) (VF T)
    (fun i => LiftSRelt (Rely i))
    (fun i => LiftSRelt (Guar i))
    (fun i _ m => LiftSPrec (Precs i m))
    ticketLockImpl
    (fun i _ m v => LiftSRelt (Posts i m v))
    (fun i _ m _ _ _ => LiftSPrec (Precs i m)).
Proof.
  constructor.
  {
    unfold LiftSRelt. intros.
    psimpl. eexists. split. easy.
    now constructor.
  }
  {
    unfold
      LiftSRelt,
      sub, subRelt.
    intros. psimpl.
    specialize (H x eq_refl). psimpl.
    specialize (H1 x2 eq_refl). psimpl.
    eexists. split. easy.
    destruct H0, H1.
    constructor; try tauto.
    { now rewrite pres_call0 at 1. }
    { now rewrite pres_ret0 at 1. }
    { now rewrite pres_ths0 at 1. }
  }
  {
    unfold
      Guar, sub,
      subRelt, LiftSRelt.
    intros. psimpl.
    specialize (H0 x eq_refl). psimpl.
    eexists. split. easy.
    now apply H1.
  }
  {
    unfold sub, subRelt, LiftSRelt.
    unfold InvokeAny, TInvoke.
    intros. psimpl. exists (invPoss i x x1).
    split.
    {
      set_ext y. split; intros; psimpl.
      {
        destruct x2, y. cbn in *.
        subst. unfold invPoss. cbn.
        f_equal; extensionality k;
        dec_eq_nats i k.
        now rewrite eqb_id.
        now rewrite eqb_nid, H7.
        now rewrite eqb_id.
        now rewrite eqb_nid, H8.
      }
      {
        eexists. split. easy.
        cbn. rewrite eqb_id.
        repeat split; try easy.
        apply differ_pointwise_trivial.
        apply differ_pointwise_trivial.
      }
    }
    {
      destruct H2. cbn in *.
      constructor.
      {
        intros. destruct H4.
        unfold invPoss.
        move H3 at bottom.
        move H2 at bottom.
        constructor; cbn.
        { easy. }
        {
          intros.
          eapply owns_resp0.
          { easy. }
          {
            unfold Ready.
            now rewrite H2.
          }
          { now rewrite H3 at 1. }
        }
        { now rewrite <- H3 at 1. }
        {
          setoid_rewrite <- H3.
          setoid_rewrite <- H2.
          all: easy.
        }
        {
          setoid_rewrite <- H3.
          setoid_rewrite <- H2.
          all: easy.
        }
        {
          setoid_rewrite <- H3.
          setoid_rewrite <- H2.
          all: easy.
        }
        {
          intros.
          eapply tkts_uniq0.
          { easy. }
          { exact H5. }
          {
            unfold Ready.
            rewrite H2; auto.
            exact H6.
          }
          {
            dec_eq_nats j0 i.
            {
              unfold Ready in H7.
              ddestruct H1.
              setoid_rewrite <- x in H7.
              destruct H7. easy.
              destruct x1;
              rewrite frobProgId with
                (p:= ticketLockImpl _ _)
                in H1;
              rewrite frobProgId with
                (p:= acq_body _)
                in H1;
              easy.
            }
            unfold Ready.
            rewrite H2; auto.
          }
        }
        {
          setoid_rewrite <- H3.
          intros. eapply tkts_boun0
            with (j:=j0).
          { easy. }
          { easy. }
          {
            dec_eq_nats j0 i.
            {
              unfold Ready in H6. ddestruct H1.
              setoid_rewrite <- x in H6.
              destruct H6. easy.
              destruct x1;
              rewrite frobProgId with
                (p:= ticketLockImpl _ _)
                in H1;
              rewrite frobProgId with
                (p:= acq_body _)
                in H1;
              easy.
            }
            unfold Ready.
            now rewrite H2.
          }
        }
        { now setoid_rewrite <- H3. }
        { now setoid_rewrite <- H3. }
      }
      { cbn. now rewrite eqb_nid. }
      { cbn. now rewrite eqb_nid. }
      { now rewrite H2. }
      { easy. }
    }
  }
  {
    unfold sub, subRelt, LiftSRelt.
    unfold ReturnAny, TReturn.
    intros. psimpl. exists (retPoss i x).
    split.
    {
      set_ext y. split; intros; psimpl.
      {
        unfold mapRetPoss in H4.
        psimpl. destruct x3, y. cbn in *.
        subst. unfold retPoss. cbn.
        f_equal; extensionality k;
        dec_eq_nats i k.
        now rewrite eqb_id.
        now rewrite eqb_nid, H7.
        now rewrite eqb_id.
        now rewrite eqb_nid, H8.
      }
      {
        unfold mapRetPoss.
        destruct H2. cbn in *.
        ddestruct H1. symmetry in x4.
        unfold Returned in H0.
        eapply H0 in x4. 2: easy.
        eexists. split. easy.
        cbn. rewrite eqb_id.
        repeat split; try easy.
        apply differ_pointwise_trivial.
        apply differ_pointwise_trivial.
      }
    }
    {
      destruct H2. cbn in *.
      constructor.
      {
        intros. destruct H4.
        unfold invPoss.
        move H3 at bottom.
        move H2 at bottom.
        constructor; cbn.
        { easy. }
        {
          intros.
          eapply owns_resp0.
          { easy. }
          {
            unfold Ready.
            now rewrite H2.
          }
          { now rewrite H3 at 1. }
        }
        { now rewrite <- H3 at 1. }
        {
          setoid_rewrite <- H3.
          setoid_rewrite <- H2.
          all: easy.
        }
        {
          setoid_rewrite <- H3.
          setoid_rewrite <- H2.
          all: easy.
        }
        {
          setoid_rewrite <- H3.
          setoid_rewrite <- H2.
          all: easy.
        }
        {
          intros.
          eapply tkts_uniq0.
          { easy. }
          { exact H5. }
          {
            unfold Ready.
            rewrite H2; auto.
            exact H6.
          }
          {
            dec_eq_nats j0 i.
            {
              unfold Ready in H7.
              ddestruct H1.
              setoid_rewrite <- x in H7.
              destruct H7; easy.
            }
            unfold Ready.
            rewrite H2; auto.
          }
        }
        {
          setoid_rewrite <- H3.
          intros. eapply tkts_boun0
            with (j:=j0).
          { easy. }
          { easy. }
          {
            dec_eq_nats j0 i.
            {
              unfold Ready in H6. ddestruct H1.
              setoid_rewrite <- x in H6.
              destruct H6. easy.
              now destruct x1.
            }
            unfold Ready.
            now rewrite H2.
          }
        }
        { now setoid_rewrite <- H3. }
        { now setoid_rewrite <- H3. }
      }
      { cbn. now rewrite eqb_nid. }
      { cbn. now rewrite eqb_nid. }
      { now rewrite H2. }
      { easy. }
    }
  }
  {
    unfold Precs, LiftSPrec.
    intros. eexists.
    split. easy.
    constructor;
    cbn; intros; try now psimpl.
    { now ddestruct H. }
    { now ddestruct H0. }
    {
      unfold Ready in *. cbn in *.
      now destruct H1.
    }
    {
      unfold Ready in *. cbn in *.
      now destruct H1.
    }
  }
  {
    unfold
      Stable, stablePrec,
      sub, subPrec,
      LiftSPrec, LiftSRelt.
    intros. psimpl.
    specialize (H0 x1 eq_refl). psimpl.
    eexists. split. easy.
    unfold Precs in *.
    now apply H0.
  }
  {
    unfold sub, subPrec.
    intros. now psimpl.
  }
  {
    intros. destruct m; cbn.
    apply acq_correct.
    apply rel_correct.
  }
  {
    unfold
      ReturnStep, Posts,
      LiftSPrec, LiftSRelt.
    intros. psimpl.
    specialize (H1 x1 eq_refl). psimpl.
    exists (eq x0).
    split.
    { repeat econstructor. }
    split.
    {
      intros. subst.
      repeat econstructor.
    }
    split.
    {
      intros. now subst.
    }
    split.
    {
      exists (retPoss i x0).
      split.
      {
        set_ext y. split; intros; psimpl.
        {
          unfold mapRetPoss in H5.
          psimpl. destruct x2, y. cbn in *.
          subst. unfold retPoss. cbn.
          f_equal; extensionality k;
          dec_eq_nats i k.
          now rewrite eqb_id.
          now rewrite eqb_nid, H8.
          now rewrite eqb_id.
          now rewrite eqb_nid, H9.
        }
        {
          unfold mapRetPoss.
          destruct H2. cbn in *.
          eexists. split. easy.
          rewrite eqb_id.
          repeat split; try easy.
          apply differ_pointwise_trivial.
          apply differ_pointwise_trivial.
        }
      }
      {
        unfold retPoss.
        destruct H1.
        constructor; cbn;
        unfold Ready; cbn;
        try setoid_rewrite eqb_id;
        try easy.
        {
          intros.
          eapply owns_wait0.
          { easy. }
          {
            setoid_rewrite H0.
            unfold not. intros.
            destruct H6; now psimpl.
          }
          { easy. }
          { exact H1. }
          { easy. } 
        }
        {
          intros.
          eapply tkts_less0.
          {
            setoid_rewrite H0.
            unfold not. intros.
            destruct H5; now psimpl.
          }
          { easy. }
          { easy. }
        }
        {
          intros.
          now destruct H5.
        }
        {
          intros.
          dec_eq_nats i j.
          {
            rewrite eqb_id in H5.
            now destruct H5.
          }
          {
            rewrite eqb_nid in *; auto.
            eapply tkts_boun0.
            { easy. }
            { easy. }
            { exact H5. }
          }
        }
      }
    }
    {
      intros. apply eq_inj in H. subst.
      exists (retPoss i x2).
      split.
      {
        set_ext y. split; intros; psimpl.
        {
          unfold mapRetPoss in H5.
          psimpl. destruct x0, y. cbn in *.
          subst. unfold retPoss. cbn.
          f_equal; extensionality k;
          dec_eq_nats i k.
          now rewrite eqb_id.
          now rewrite eqb_nid, H8.
          now rewrite eqb_id.
          now rewrite eqb_nid, H9.
        }
        {
          unfold mapRetPoss.
          destruct H2. cbn in *.
          eexists. split. easy.
          rewrite eqb_id.
          repeat split; try easy.
          apply differ_pointwise_trivial.
          apply differ_pointwise_trivial.
        }
      }
      {
        constructor.
        {
          intros. destruct H5.
          constructor; cbn;
          unfold Ready; cbn;
          try (setoid_rewrite eqb_nid; auto);
          try easy.
          {
            intros.
            rewrite eqb_nid in *; auto.
          }
          {
            intros.
            rewrite eqb_nid with
              (n:=i) (m:=j)
              in *; auto.
            dec_eq_nats j0 i.
            {
              rewrite eqb_id in *.
              now destruct H8.
            }
            rewrite eqb_nid in *; auto.
            eapply tkts_uniq0.
            { easy. }
            { exact H6. }
            { exact H7. }
            { exact H8. }
          }
          {
            intros.
            dec_eq_nats j0 i.
            {
              rewrite eqb_id in *.
              now destruct H7.
            }
            rewrite eqb_nid in *; auto.
            eapply tkts_boun0.
            { easy. }
            { easy. }
            { exact H7. }
          }
        }
        { cbn. now rewrite eqb_nid. }
        { cbn. now rewrite eqb_nid. }
        { cbn. now rewrite eqb_nid. }
        { easy. }
      }
    }
  }
Qed.