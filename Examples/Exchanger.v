From LHL.Core Require Import
  ProgramRules
  LogicFacts
  SingConds
  Program
  Traces
  Tensor
  Logic
  Specs.

From LHL.Util Require Import
  Tactics
  Util.

From LHL.Examples Require Import
  ExchangerSpec
  ThreadLocal
  CASSpec.

From Coq Require Import
  Logic.FunctionalExtensionality
  Logic.PropExtensionality
  Program.Equality
  Relations.Relation_Operators.

From Paco Require Import
  paco.

(* Signature *)

Variant Flag := Offered | Accepted.

Definition Offer A : Type := Flag * A.

Notation OFFERED v := (Some (Offered, v)).
Notation ACCEPTED v := (Some (Accepted, v)).

Definition E A :=
  CASSig (Offer A).

Definition VE T A : Spec T (E A) :=
  casSpec.

Definition F A := ExchSig A.

Definition VF T A : Spec T (F A) :=
  exchSpec.

(* Code *)

Definition exch {A} (v : A) : Prog (E A) (option A) :=
  my_offer_placed <- call (CAS None (OFFERED v));
  if my_offer_placed : bool then
    no_change <- call (CAS (OFFERED v) None);
    if no_change : bool then
      ret None
    else
      w <- call Get;
      match w : option (Offer A) with
      | Some (_, w) =>
          call (CAS (ACCEPTED w) None);;
          ret (Some w)
      | None =>
          ret None (* impossible *)
      end
  else
    w <- call Get;
    match w : option (Offer A) with
    | Some (_, w) =>
        my_offer_accepted <- call (CAS (OFFERED w) (ACCEPTED v));
        if my_offer_accepted : bool then
          ret (Some w)
        else
          ret None
    | None =>
        ret None
    end.

Definition exchImpl A : Impl (E A) (F A) :=
  fun i m => match m with
  | Exch v => exch v
  end.

(* Conditions *)

Definition SRelt T A := SRelt (VE T A) (VF T A).
Definition SPrec T A := SPrec (VE T A) (VF T A).

Variant AtomicStatePrec {T A} :=
| SCleared
| SOffered (i : Name T) (v : A)
| SAcceptd (i j : Name T) (v w : A).
Arguments AtomicStatePrec : clear implicits.

Variant AtomicStateTran {T A} i : AtomicStatePrec T A -> AtomicStatePrec T A -> Prop :=
| STOffer v :
  AtomicStateTran i
    (SCleared)
    (SOffered i v)
| STRevoke v :
  AtomicStateTran i
    (SOffered i v)
    (SCleared)
| STAccept v j w :
  i <> j ->
  AtomicStateTran i
    (SOffered j w)
    (SAcceptd j i w v)
| STFinish j v w :
  i <> j ->
  AtomicStateTran i
    (SAcceptd j i w v)
    (SCleared).

Record RealStatePrec {T A} := MkRSP {
  RSCurr : AtomicStatePrec T A;
  RSNext : option (AtomicStatePrec T A)
}.
Arguments RealStatePrec : clear implicits.
Arguments MkRSP {T A}.

Variant RealStateTran {T A} i : RealStatePrec T A -> RealStatePrec T A -> Prop :=
| CallTran s t :
  AtomicStateTran i s t ->
  RealStateTran i (MkRSP s None) (MkRSP s (Some t))
| RetTran s t :
  RealStateTran i (MkRSP s (Some t)) (MkRSP t None).

Definition CCleared {A T} m : SPrec T A :=
  fun s ρ =>
    snd s = CASDef None m /\
    PState ρ = ExchDef {} {}.

Definition COffered {A T} m (i : Name T) (v : A) : SPrec T A :=
  fun s ρ =>
    snd s = CASDef (OFFERED v) m /\
    PState ρ = ExchDef {i => v} {}.

Definition CAcceptd {A T} m (i j : Name T) (v w : A) : SPrec T A :=
  fun s ρ =>
    snd s = CASDef (ACCEPTED v) m /\
    PState ρ = ExchDef {j => w} {i => v}.

Definition atomicPrecSem {T A} (P : AtomicStatePrec T A) m : SPrec T A :=
  match P with
  | SCleared => CCleared m
  | SOffered i v => COffered m i v
  | SAcceptd i j v w => CAcceptd m i j v w
  end.

Definition realPrecSem {T A} (P : RealStatePrec T A) : SPrec T A :=
  atomicPrecSem P.(RSCurr) match P.(RSNext) with
  | None | Some SCleared =>
      None
  | Some (SOffered i v) =>
      Some (MkCASPend i (CAS None (OFFERED v)))
  | Some (SAcceptd i j v w) =>
      Some (MkCASPend i (CAS (OFFERED v) (ACCEPTED w)))
  end.

Notation "[[ P ]]" := (realPrecSem P).

Definition Precs {A T} R (m : ExchSig A R) : SPrec T A :=
  fun s x => exists P, [[P]] s x.

Definition Posts {A T} R (m : ExchSig A R) : R -> SRelt T A :=
  fun _ _ _ => Precs R m.

Definition Guar {T A} (i : Name T) : SRelt T A :=
  fun s x t y =>
    (forall j, i <> j ->
      PCalls x j = PCalls y j /\
      PRets x j = PRets y j) /\
    (exists P, [[P]] s x /\
      exists Q, [[Q]] t y /\
        RealStateTran i P Q) \/
    (ReturnAny (exchImpl A) i s (eq x) t (eq y)).

Definition Rely {T A} (i : Name T) : SRelt T A :=
  SRTC (fun s x t y =>
    exists j, i <> j /\
      (InvokeAny (exchImpl A) j s (eq x) t (eq y) \/
       ReturnAny (exchImpl A) j s (eq x) t (eq y) \/
       Guar j s x t y)).

(* Tactics *)

Ltac ddestruct H := dependent destruction H.

Ltac elim_disj :=
repeat match goal with
| [ H : ?P \/ ?Q |- _] => destruct H
end.

Ltac decide_prop P :=
  let H := fresh in
  assert (H : P \/ ~P) by apply excluded_middle;
  destruct H.

Ltac set_ext x := extensionality x; apply propositional_extensionality.

(* Helper lemmas *)

Lemma pres_state {T A R} :
  forall (m : F A R) i s ρ t σ,
  TInvoke (VE:= VE T A) (VF:= VF T A) (exchImpl A) i R m s (eq ρ) t (eq σ) ->
  PState ρ = PState σ /\
  snd s = snd t.
unfold TInvoke. intros. destruct_all.
assert (σ = invPoss i ρ m).
{
  rewrite H2. exists ρ.
  cbn. rewrite eqb_id.
  repeat split; (easy || apply differ_pointwise_trivial).
}
subst. easy.
Qed.

Lemma refl_triv {A} {x : A} : (x = x) = True.
apply propositional_extensionality.
easy.
Qed.

Lemma eq_triv {P : Prop} :
  True = P ->
  P.
intros.
decide_prop P. easy.
exfalso. apply H0.
rewrite <- H in H0.
contradiction.
Qed.

Lemma TReturn_pres_state {T A R} :
  forall (m : F A R) v i s ρ t σ,
  TReturn (VE:= VE T A) (VF:= VF T A) (exchImpl A) i m v s (eq ρ) t (eq σ) ->
  PState ρ = PState σ /\
  snd s = snd t.
unfold TReturn. intros. destruct_all.
split. 2: easy.
apply equal_f with (x:=σ) in H2.
rewrite refl_triv in H2. apply eq_triv in H2.
unfold mapRetPoss in H2. psimpl.
easy.
Qed.

Lemma Invoke_pres_single {T A R} :
  forall (m : F A R) i s ρ t σs,
  TInvoke (VE:= VE T A) (VF:= VF T A) (exchImpl A) i R m s (eq ρ) t σs ->
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

Lemma Return_pres_single {T A R} :
  forall (m : F A R) v i s ρ t σs,
  TReturn (VE:= VE T A) (VF:= VF T A) (exchImpl A) i m v s (eq ρ) t σs ->
  exists σ, σs = eq σ.
intros.
unfold TReturn, mapRetPoss in H. psimpl.
exists (retPoss i ρ).
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

Lemma eq_inj {A} :
  forall x y : A, eq x = eq y -> x = y.
intros.
assert (forall z, eq x z = eq z y).
{
  intros. apply propositional_extensionality.
  split; intros.
  rewrite H in H0. easy.
  rewrite H. easy.
}
specialize (H0 x).
rewrite <- H0. easy.
Qed.

Lemma pres_sem {T A} :
  forall s x t y,
  snd s = snd t ->
  PState x = PState y ->
  forall P : RealStatePrec T A,
  [[P]] s x -> [[P]] t y.
unfold realPrecSem. intros.
destruct P, RSCurr0; psimpl;
unfold CCleared, COffered, CAcceptd in *;
psimpl.
rewrite <- H, <- H0. easy.
rewrite <- H, <- H0. easy.
rewrite <- H, <- H0. easy.
Qed.

(* Lemma Rely_pres_self {T A} :
  forall i s x t y,
  Rely (T:=T) (A:=A) i s x t y ->
  PCalls x i = PCalls y i /\
  PRets x i = PRets y i.
unfold Rely. intros.
induction H. easy.
clear H0. psimpl.
rewrite <- H0, <- H1.
clear H0 H1.
unfold
  InvokeAny, TInvoke,
  ReturnAny, TReturn
in *.
elim_disj; psimpl.
{
  apply equal_f with (x:=σ) in H3.
  rewrite refl_triv in H3.
  apply eq_triv in H3. psimpl.
  rewrite H7, H8; easy.
}
{
  apply equal_f with (x:=σ) in H3.
  rewrite refl_triv in H3.
  apply eq_triv in H3.
  unfold mapRetPoss in *. psimpl.
  rewrite H8, H9; easy.
}
{
  unfold Guar in H0.
  easy.
}
Qed. *)

(* Subsidiary proofs *)

Lemma semStableInvoke {T A R} {i} {m : F A R} :
  forall P : RealStatePrec T A,
  SStable
    (fun s x t y => TInvoke (exchImpl A) i _ m s (eq x) t (eq y))
    [[P]].
unfold SStable, stableSPrec, ssub, subSPrec.
unfold TInvoke. intros. psimpl.
destruct H1. cbn in *. ddestruct H1.
eapply pres_sem with (x:=x0). exact H2.
apply equal_f with (x:=ρ) in H3.
rewrite refl_triv in H3.
apply eq_triv in H3. psimpl.
easy. easy.
Qed.

Lemma semStableReturn {T A R} {i} {m : F A R} {v} :
  forall P : RealStatePrec T A,
  SStable
    (fun s x t y => TReturn (exchImpl A) i m v s (eq x) t (eq y))
    [[P]].
unfold SStable, stableSPrec, ssub, subSPrec.
unfold TReturn. intros. psimpl.
destruct H1. cbn in *. ddestruct H1.
eapply pres_sem with (x:=x0). exact H2.
apply equal_f with (x:=ρ) in H3.
rewrite refl_triv in H3.
apply eq_triv in H3.
unfold mapRetPoss in *. psimpl.
easy. easy.
Qed.

Lemma srtcTrans_inv {T A} {R} :
  forall s x r z,
  SRTC R s x r z ->
  (exists t y,
    SRTC (VE:= VE T A) (VF:= VF T A) R s x t y /\
    R t y r z) \/
  (s = r /\ x = z).
intros. induction H.
right. easy.
destruct IHSRTC; psimpl.
{
  left. exists x, x0.
  split. 2: easy.
  apply srtcTrans.
  psplit.
  {
    eapply SRTCStep.
    exact H. constructor.
  }
  {
    easy.
  }
}
{
  left. repeat eexists.
  constructor. easy.
}
Qed.

(* Lemma semGuarTran {T A} : *)

Lemma Precs_stable {T A} :
  forall (i : Name T) R (m : F A R),
  SStable (Rely i) (Precs R m).
unfold SStable, stableSPrec, ssub, subSPrec.
unfold Precs, Rely. intros. psimpl.
generalize dependent x1.
induction H0; intros. exists x1. easy.
clear H0. psimpl.
unfold InvokeAny, ReturnAny in *.
elim_disj; psimpl.
{
  apply IHSRTC with (x1:=x1).
  eapply semStableInvoke.
  psplit. exact H1. exact H0.
}
{
  apply IHSRTC with (x1:=x1).
  eapply semStableReturn.
  psplit. exact H1. exact H0.
}
{
  unfold Guar in *. destruct H0; psimpl.
  {
    apply IHSRTC with (x1:=x2).
    easy.
  }
  {
    apply IHSRTC with (x1:=x1).
    unfold ReturnAny in *. psimpl.
    apply TReturn_pres_state in H0. psimpl.
    eapply pres_sem. exact H2. exact H0. easy.
  }
}
Qed.

Lemma Precs_stable_Invoke {T A} :
  forall (i : Name T) R (m : F A R),
  SStable
    (fun s x t y => InvokeAny (exchImpl A) i s (eq x) t (eq y))
    (Precs R m).
unfold SStable, stableSPrec, ssub, subSPrec.
unfold Precs in *. intros. psimpl.
unfold InvokeAny in *. psimpl.
exists x1. eapply semStableInvoke.
psplit. exact H. exact H0.
Qed.

Lemma exch_correct {T A} {i : Name T} :
  forall v,
  VerifyProg i (LiftSRelt (Rely i)) (LiftSRelt (Guar i))
    (prComp (LiftSPrec (Precs (option A) (Exch v))) (TInvoke (exchImpl A) i _ (Exch v)) ->> LiftSRelt (Rely i))
    (exch v)
    (fun v' => LiftSRelt (Posts _ (Exch v) v') ->> PrecToRelt (Returned i (Exch v) v')).
unfold exch. intros.
eapply weakenPrec with
  (P:=fun _ _ =>
    LiftSPrec (Precs (option A) (Exch v)) <<-
    TInvoke (exchImpl A) i _ (Exch v)).
2:{
  unfold sub, subRelt. intros. psimpl.
  unfold LiftSRelt, LiftSPrec in *. psimpl.
  assert (exists x, x0 = eq x).
  {
    eapply Invoke_pres_single.
    exact H1.
  } psimpl.
  specialize (H0 x2 eq_refl). psimpl.
  move H1 after H0. move x2 at top. move x0 at top.
  apply srtcTrans_inv in H0. destruct H0; psimpl.
  {
    fold (Rely (T:=T) (A:=A) i x x2 x3 x4) in H.
    exists x3, (eq x4). split.
    {
      exists x4. split. easy.
      apply Precs_stable with (i:=i).
      psplit. 2: exact H.
      apply pres_state in H1. psimpl.
      unfold Precs in *. psimpl.
      exists x6. eapply pres_sem.
      exact H4. exact H1. easy.
    }
    {
      
    }
  }
  {
    do 2 eexists. split.
    eexists. split. easy.
    exact H2.
    easy.
  }
}
eapply lemBind.
{
  admit.
}
Admitted.

(* Result *)

Theorem oneCellExchCorrect T A :
  VerifyImpl (VE T A) (VF T A)
    (fun i => LiftSRelt (Rely i))
    (fun i => LiftSRelt (Guar i))
    (fun _ _ m => LiftSPrec (Precs _ m))
    (exchImpl A)
    (fun i _ m v' => LiftSRelt (Posts _ m v')  ->> PrecToRelt (Returned i m v'))
    (TReturn (exchImpl A)).
constructor.
{
  unfold LiftSRelt. intros. psimpl.
  exists x. split. easy.
  constructor.
}
{
  unfold Rely, sub, subRelt. intros. psimpl.
  unfold LiftSRelt in *. intros. psimpl.
  specialize (H x1 eq_refl). psimpl.
  specialize (H0 x2 eq_refl). psimpl.
  exists x0. split. easy.
  apply srtcTrans. psplit. exact H1. easy.
}
{
  unfold Rely, sub, subRelt. intros.
  unfold LiftSRelt in *. intros. psimpl.
  specialize (H0 x eq_refl). psimpl.
  exists x0. split. easy.
  econstructor. 2: constructor.
  exists i. split. easy.
  do 2 right. easy.
}
{
  unfold Rely, sub, subRelt. intros.
  unfold LiftSRelt in *. intros. psimpl.
  assert (exists x, σ = eq x).
  {
    unfold InvokeAny in *. psimpl.
    eapply Invoke_pres_single.
    exact H0.
  } psimpl.
  exists x0. split. easy.
  econstructor. 2: constructor.
  exists i. split. easy. left. easy.
}
{
  unfold Rely, sub, subRelt. intros.
  unfold LiftSRelt in *. intros. psimpl.
  assert (exists x, σ = eq x).
  {
    unfold ReturnAny in *. psimpl.
    eapply Return_pres_single.
    exact H0.
  } psimpl.
  exists x0. split. easy.
  econstructor. 2: constructor.
  exists i. split. easy. right. left. easy.
}
{
  exists initPoss. split. easy.
  exists (MkRSP SCleared None).
  unfold realPrecSem, atomicPrecSem.
  cbn. easy.
}
{
  intros.
  apply liftSPrecStable.
  apply Precs_stable.
}
{
  unfold Posts, sub, subPrec. intros. psimpl.
  unfold LiftSPrec, LiftSRelt in *. psimpl.
  specialize (H1 x3 eq_refl). psimpl.
  assert (exists x1, ρ = eq x1).
  {
    eapply Return_pres_single.
    exact H0.
  } psimpl.
  apply TReturn_pres_state in H0. psimpl.
  exists x0. split. easy.
  clear - H1 H H0.
  unfold Precs in *. psimpl.
  exists x1. eapply pres_sem.
  exact H0. exact H. easy.
}
{
  intros. destruct m. cbn.
  apply exch_correct.
}
{
  unfold ReturnStep. intros. psimpl.
  unfold LiftSRelt, LiftSPrec in *. psimpl.
  specialize (H1 x1 eq_refl). psimpl.
  exists (eq x0).
  split.
  {
    exists x0. easy.
  }
  split.
  {
    intros. subst.
    exists σ.
    repeat (easy || constructor).
  }
  split.
  {
    intros. subst.
    apply H2; easy.
  }
  split.
  {
    unfold TReturn.
    split. easy.
    split.
    {
      split.
      {
        constructor; cbn.
        easy. rewrite eqb_id. easy.
      }
      {
        cbn. intros. rewrite eqb_nid; easy.
      }
    }
    easy.
  }
  {
    intros. apply eq_inj in H. psimpl.
    exists (retPoss i x2). split.
    {
      set_ext y. unfold mapRetPoss, retPoss.
      split; intros; psimpl.
      {
        destruct x, y. cbn in *.
        f_equal. easy.
        {
          extensionality j.
          dec_eq_nats i j.
          rewrite eqb_id. easy.
          rewrite eqb_nid, H8; easy.
        }
        {
          extensionality j.
          dec_eq_nats i j.
          rewrite eqb_id. easy.
          rewrite eqb_nid, H9; easy.
        }
      }
      {
        exists x2. split. easy.
        cbn. rewrite eqb_id.
        apply H2 in H0.
        specialize (H0 x2 eq_refl). psimpl.
        repeat split; (easy || apply differ_pointwise_trivial).
      }
    }
    {
      right.
      exists _, m, v.
      split. easy.
      split.
      {
        split.
        {
          constructor; cbn.
          easy. rewrite eqb_id. easy.
        }
        {
          cbn. intros. rewrite eqb_nid; easy.
        }
      }
      split. easy.
      {
        set_ext y.
        unfold retPoss, mapRetPoss.
        split; intros; psimpl.
        {
          exists x2. split. easy.
          cbn. rewrite eqb_id.
          apply H2 in H0.
          specialize (H0 x2 eq_refl). psimpl.
          repeat split; (easy || apply differ_pointwise_trivial).
        }
        {
          destruct y, x0. cbn in *.
          f_equal. easy.
          {
            extensionality j.
            dec_eq_nats i j.
            rewrite eqb_id. easy.
            rewrite eqb_nid, H8; easy.
          }
          {
            extensionality j.
            dec_eq_nats i j.
            rewrite eqb_id. easy.
            rewrite eqb_nid, H9; easy.
          }
        }
      }
    }
  }
}
Qed.