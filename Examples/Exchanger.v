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
    forall P, [[P]] s x ->
      exists Q, [[Q]] t y /\
        RealStateTran i P Q.

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

Lemma TInvoke_pres_state {T A R} :
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
  unfold Guar in *.
  apply H0 in H1. clear H0.
  psimpl. eapply IHSRTC. exact H0.
}
Qed.

Lemma exch_correct {T A} {i : Name T} :
  forall v,
  VerifyProg i (LiftSRelt (Rely i)) (LiftSRelt (Guar i))
    (prComp (LiftSPrec (Precs (option A) (Exch v))) (TInvoke (exchImpl A) i _ (Exch v)) ->> LiftSRelt (Rely i))
    (exch v)
    (fun v' => LiftSRelt (Posts _ (Exch v) v') ->> PrecToRelt (Returned i (Exch v) v')).
unfold exch. intros.
eapply lemBind.
{
  
}

(* Result *)

Theorem ticketLockCorrect T A :
  VerifyImpl (VE T A) (VF T A) Rely Guar (fun _ => Precs) (exchImpl A) (fun _ => Posts).
constructor.
{
  constructor.
}
{
  unfold Rely, sub, subRelt. intros. psimpl.
  apply rtcTrans. psplit. exact H. easy.
}
{
  unfold Rely, sub, subRelt. intros.
  econstructor. 2: constructor.
  exists i. split. easy. left. easy.
}
{
  unfold Rely, sub, subRelt. intros.
  econstructor. 2: constructor.
  exists i. split. easy. right. left. easy.
}
{
  unfold Rely, sub, subRelt. intros.
  econstructor. 2: constructor.
  exists i. split. easy. right. right. easy.
}
{
  exists initPoss. split. easy. left. exists None. easy.
}
{
  apply Precs_stable.
}
{
  unfold Stable, stableRelt, Posts, sub, subRelt. intros. psimpl.
  eapply Precs_stable. psplit.
  exact H. exact H0.
}
{
  unfold sub, subPrec. intros. psimpl.
  unfold Posts, Precs, CCleared, COffered, CAccepted in *.
  psimpl.
  assert (exists τ, ρ = eq τ).
  eapply Return_pres_single. exact H0. psimpl.
  exists x0. split. easy.
  apply TReturn_pres_state in H0. destruct_all.
  rewrite <- H. clear H4.
  elim_disj.
  {
    left. psimpl. exists x4.
    rewrite <- H0 at 1. easy.
  }
  {
    right. left. destruct_all.
    rewrite H0 in H2 at 1.
    exists x4, x5, x6. easy.
  }
  {
    right. right. destruct_all.
    rewrite H0 in H3 at 1.
    exists x4, x5, x6, x7, x8. easy.
  }
}
{
  intros. destruct m. cbn.
  apply exch_correct.
}
Qed.