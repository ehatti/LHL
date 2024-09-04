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
  Relations.Relation_Operators
  Lists.List.

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

Variant AtomicStateTran {T A} : Name T -> AtomicStatePrec T A -> AtomicStatePrec T A -> Prop :=
| STOffer i v :
  AtomicStateTran i
    (SCleared)
    (SOffered i v)
| STRevoke i v :
  AtomicStateTran i
    (SOffered i v)
    (SCleared)
| STAccept i j v w :
  i <> j ->
  AtomicStateTran j
    (SOffered i v)
    (SAcceptd i j v w)
| STFinish i j v w :
  i <> j ->
  AtomicStateTran i
    (SAcceptd i j v w)
    (SCleared).

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

Notation "[[ P ]]" := (atomicPrecSem P).

Definition Precs {A T} (i : Name T) : SPrec T A :=
  fun s x =>
    exists m,
    [[SCleared]] m s x \/
    (exists j v,
      i <> j /\
      [[SOffered j v]] m s x) \/
    (exists j k v w,
      i <> j /\ i <> k /\ j <> k /\
      [[SAcceptd j k v w]] m s x).

Definition Posts {A T} (i : Name T) : SRelt T A :=
  fun _ _ => Precs i.

Definition Guar {T A} (i : Name T) : SRelt T A :=
  fun s x t y =>
    ((forall j, i <> j ->
       PCalls x j = PCalls y j /\
       PRets x j = PRets y j) /\
     (exists P Q e n,
       [[P]] (Some (MkCASPend i (CAS e n))) s x /\
       [[Q]] None t y /\
       AtomicStateTran i P Q)) \/
    ((forall j, i <> j ->
        PCalls x j = PCalls y j /\
        PRets x j = PRets y j) /\
     (exists a e n,
        snd s = CASDef a None /\
        snd t = CASDef a (Some (MkCASPend i (CAS e n))) /\
        PState x = PState y)) \/
    (exists a e n,
      x = y /\
      snd s = CASDef a (Some (MkCASPend i (CAS e n))) /\
      snd t = CASDef a None) \/
    (ReturnAny (exchImpl A) i s (eq x) t (eq y)).

Definition Rely {T A} (i : Name T) : SRelt T A :=
  SRTC (fun s x t y =>
    exists j, i <> j /\
      (InvokeAny (exchImpl A) j s (eq x) t (eq y) \/
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
  forall s x t y m,
  snd s = snd t ->
  PState x = PState y ->
  forall P : AtomicStatePrec T A,
  [[P]] m s x -> [[P]] m t y.
unfold atomicPrecSem. intros.
destruct P; psimpl;
unfold CCleared, COffered, CAcceptd in *;
psimpl.
rewrite <- H, <- H0. easy.
rewrite <- H, <- H0. easy.
rewrite <- H, <- H0. easy.
Qed.

(* Definition casVal {T A} (s : CASState T A) : option A :=
  match s with
  | CASDef s _ => s
  end.

Lemma pres_sem_val {T A} :
  forall s x t y m1 m2,
  casVal (snd s) = casVal (snd t) ->
  PState x = PState y ->
  forall P : AtomicStatePrec T A,
  [[P]] m1 s x -> [[P]] m2 t y.
unfold atomicPrecSem. intros.
destruct P; psimpl;
unfold CCleared, COffered, CAcceptd in *;
psimpl.
rewrite <- H, <- H0. easy.
rewrite <- H, <- H0. easy.
rewrite <- H, <- H0. easy.
Qed. *)


Lemma sem_shows_pend {T A} :
  forall s x m,
  forall P : AtomicStatePrec T A,
  [[P]] m s x ->
  exists a,
    snd s = CASDef a m.
unfold atomicPrecSem.
destruct P; psimpl;
unfold CCleared, COffered, CAcceptd in *;
psimpl.
{
  intros. now exists None.
}
{
  intros. now exists (OFFERED v).
}
{
  intros. now exists (ACCEPTED v).
}
Qed.

Lemma Rely_pres_self {T A} :
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
  InvokeAny, TInvoke
in *.
elim_disj; psimpl.
{
  apply equal_f with (x:=σ) in H3.
  rewrite refl_triv in H3.
  apply eq_triv in H3. psimpl.
  rewrite H7, H8; easy.
}
{
  unfold Guar in H0.
  unfold ReturnAny, TReturn in *.
  elim_disj; psimpl.
  {
    apply H0. easy.
  }
  {
    apply H0. easy.
  }
  {
    easy.
  }
  {
    apply equal_f with (x:=σ) in H3.
    rewrite refl_triv in H3.
    apply eq_triv in H3. psimpl.
    unfold mapRetPoss in H4. psimpl.
    rewrite H7, H8; easy.
  }
}
Qed.

(* Subsidiary proofs *)

Lemma semStableInvoke {T A R} {i} {m : F A R} :
  forall (P : AtomicStatePrec T A) m',
  SStable
    (fun s x t y => TInvoke (exchImpl A) i _ m s (eq x) t (eq y))
    ([[P]] m').
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
  forall (P : AtomicStatePrec T A) m',
  SStable
    (fun s x t y => TReturn (exchImpl A) i m v s (eq x) t (eq y))
    ([[P]] m').
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

Lemma Rely_resp_call {T A} {i} :
  forall s x t y a R m,
  Rely (T:=T) (A:=A) i s x t y ->
  snd s = CASDef a (Some (@MkCASPend _ _ i R m)) ->
  snd s = snd t /\
  PState x = PState y.
unfold Rely. intros.
induction H. easy.
clear H1. psimpl.
unfold Guar in H1.
elim_disj; psimpl.
{
  unfold InvokeAny, TInvoke in H1. psimpl.
  rewrite H3 in H0. apply IHSRTC in H0. psimpl.
  clear IHSRTC. rewrite <- H5.
  split. congruence.
  apply equal_f with (x:=σ) in H4.
  rewrite refl_triv in H4.
  apply eq_triv in H4. psimpl.
  easy.
}
{
  apply sem_shows_pend in H2. psimpl.
  rewrite H2 in H0.
  now ddestruct H0.
}
{
  rewrite H0 in H2.
  congruence.
}
{
  rewrite H0 in H2.
  now ddestruct H2.
}
{
  unfold ReturnAny, TReturn in H1. psimpl.
  rewrite H3 in H0. apply IHSRTC in H0. psimpl.
  clear IHSRTC. rewrite <- H5.
  split. congruence.
  apply equal_f with (x:=σ) in H4.
  rewrite refl_triv in H4.
  apply eq_triv in H4.
  unfold mapRetPoss in H4. psimpl.
  easy.
}
Qed.

(* Lemma semGuarTran {T A} : *)

Lemma Precs_stable {T A} :
  forall (i : Name T),
  SStable (Rely (A:=A) i) (Precs i).
(* unfold SStable, stableSPrec, ssub, subSPrec.
unfold Precs, Rely. intros. psimpl.
generalize dependent x1.
generalize dependent x2.
induction H0; intros. now exists x1, x2.
clear H0. psimpl.
unfold InvokeAny in *.
elim_disj; psimpl.
{
  apply IHSRTC with (x2:=x2) (x1:=x1).
  eapply semStableInvoke.
  psplit. exact H1. exact H0.
}
{
  unfold Guar in *. elim_disj; psimpl.
  {
    apply IHSRTC with (x2:=None) (x1:=x3).
    easy.
  }
  {
    apply IHSRTC with (x2:= Some (MkCASPend x (CAS x3 x4))) (x1:=x1).
    clear - H1 H2 H3 H4. destruct x1.
    {
      psimpl. unfold CCleared in *. psimpl.
      rewrite H in H2. ddestruct H2.
      now rewrite <- H4.
    }
    {
      psimpl. unfold COffered in *. psimpl.
      rewrite H in H2. ddestruct H2.
      now rewrite <- H4.
    }
    {
      psimpl. unfold CAcceptd in *. psimpl.
      rewrite H in H2. ddestruct H2.
      now rewrite <- H4.
    }
  }
  {
    assert (H1' := H1).
    eapply sem_shows_pend in H1'. psimpl.
    rewrite H2 in H0. ddestruct H0.
    eapply IHSRTC with (x2:=None) (x1:=x1).
    clear - H1 H2 H3.
    destruct x1; psimpl;
    unfold CCleared, COffered, CAcceptd in *;
    psimpl.
    rewrite H2 in H. now ddestruct H.
    rewrite H2 in H. now ddestruct H.
    rewrite H2 in H. now ddestruct H.
  }
  {
    apply IHSRTC with (x2:=x2) (x1:=x1).
    unfold ReturnAny in *. psimpl.
    apply TReturn_pres_state in H0. psimpl.
    eapply pres_sem. exact H2. exact H0. easy.
  }
} *)
Admitted.

(* Lemma Precs_stable_Invoke {T A} :
  forall (i : Name T) R (m : F A R),
  SStable
    (fun s x t y => InvokeAny (exchImpl A) i s (eq x) t (eq y))
    (Precs R m).
unfold SStable, stableSPrec, ssub, subSPrec.
unfold Precs in *. intros. psimpl.
unfold InvokeAny in *. psimpl.
exists x1. eapply semStableInvoke.
psplit. exact H. exact H0.
Qed. *)

Definition CallStep {T A} i (e n : option (Offer A)) : SRelt T A :=
  fun s x t y =>
    exists a,
      snd s = CASDef a None /\
      snd t = CASDef a (Some (MkCASPend i (CAS e n))) /\
      PState x = PState y /\
      PCalls x i = PCalls y i /\
      PRets x i = PRets y i.

Lemma weakenCommitPre {T E F} {VE : Spec T E} {VF : Spec T F} {i G Q P' e} :
  forall P : Prec VE VF,
  P' ==> P ->
  Commit i G P e Q ->
  Commit i G P' e Q.
unfold Commit. intros.
apply H0.
destruct_all.
apply H.
easy.
easy.
easy.
easy.
Qed.

Lemma sem_uniq {A T} :
  forall P Q : AtomicStatePrec T A,
  forall pm qm s x,
  [[P]] pm s x ->
  [[Q]] qm s x ->
  pm = qm /\
  P = Q.
intros.
destruct P, Q; psimpl;
unfold CCleared, COffered, CAcceptd in *;
psimpl.
{ rewrite H in H0. now ddestruct H0. }
{ rewrite H in H0. now ddestruct H0. }
{ rewrite H in H0. now ddestruct H0. }
{ rewrite H in H0. now ddestruct H0. }
{
  rewrite H in H0. rewrite H2 in H1.
  ddestruct H1. apply insert_cong in x.
  psimpl. now ddestruct H1.
}
{
  rewrite H in H0. rewrite H1 in H2.
  ddestruct H1.
}
{ rewrite H in H0. now ddestruct H0. }
{ rewrite H in H0. now ddestruct H0. }
{
  rewrite H in H0. ddestruct H0.
  rewrite H2 in H1. ddestruct H1.
  apply insert_cong in x1. psimpl.
  ddestruct H1. clear H2.
  apply insert_cong in x. psimpl.
  ddestruct H1. clear H2. easy.
}
Qed.

Lemma lemCAS {T A} {P : SPrec T A} :
  forall (QT QF : SPrec T A) i e n,
  SStable (Rely i) QT ->
  SStable (Rely i) QF ->
  SCommit i
    (Guar i)
    (P <<S CallStep i e n)
    (RetEv (CAS e n) true)
    (fun _ _ => QT) ->
  SCommit i
    (Guar i)
    (P <<S CallStep i e n)
    (RetEv (CAS e n) false)
    (fun _ _ => QF) ->
  VerifyProg i
    (LiftSRelt (Rely i)) (LiftSRelt (Guar i))
    (fun _ _ => LiftSPrec P)
    (call (CAS e n))
    (fun (v : bool) _ _ => LiftSPrec (if v then QT else QF)).
intros.
eapply weakenPost with
  (Q:=fun (v : bool) =>
    (fun _ _ => LiftSPrec P) ->>
    LiftSRelt (CallStep i e n) ->>
    LiftSRelt (fun _ _ => if v then QT else QF)).
2:{
  unfold sub, subRelt, LiftSPrec, LiftSRelt.
  intros. psimpl.
  specialize (H4 x3 eq_refl). psimpl.
  specialize (H5 x0 eq_refl). psimpl.
  exists x2. split. easy.
  easy.
}
apply lemCall.
{
  unfold Stable, stableRelt, sub, subRelt, LiftSRelt.
  intros. psimpl. unfold CallStep in H3. psimpl.
  specialize (H3 x eq_refl). psimpl.
  specialize (H5 x2 eq_refl). psimpl.
  exists x1. split. easy. exists x3.
  assert (H5' := H5).
  eapply Rely_resp_call in H5. psimpl. 2: exact H6.
  eapply Rely_pres_self in H5'. psimpl.
  now rewrite <- H10, <- H11, <- H3, <- H5.
}
{
  unfold Stable, stablePost, stableRelt, sub, subRelt.
  unfold LiftSRelt, LiftSPrec.
  intros. psimpl.
  specialize (H3 x eq_refl). psimpl.
  specialize (H5 x2 eq_refl). psimpl.
  exists x1. split. easy.
  destruct v.
  apply H. psplit. exact H4. easy.
  apply H0. psplit. exact H4. easy.
}
{
  unfold Commit, LiftSPrec, LiftSRelt.
  intros. psimpl. exists (eq x1).
  split.
  { exists x1. easy. }
  split. 
  {
    intros. subst. exists σ.
    repeat (easy || constructor).
  }
  split.
  {
    intros.
    apply eq_inj in H3. subst.
    exists x. split. easy.
    ddestruct H5. ddestruct H6.
    now exists a.
  }
  {
    intros.
    apply eq_inj in H3. subst.
    exists x. split. easy.
    right. left.
    ddestruct H5. ddestruct H6.
    split. easy.
    now exists a, e, n.
  }
}
{
  intros. destruct v.
  {
    eapply weakenCommitPre.
    2:{
      eapply liftSCommit.
      exact H1.
    }
    unfold sub, subPrec, LiftSPrec, LiftSRelt.
    intros. psimpl.
    specialize (H4 x3 eq_refl). psimpl.
    exists x2. split. easy.
    psplit. exact H5. easy.
  }
  {
    eapply weakenCommitPre.
    2:{
      eapply liftSCommit.
      exact H2.
    }
    unfold sub, subPrec, LiftSPrec, LiftSRelt.
    intros. psimpl.
    specialize (H4 x3 eq_refl). psimpl.
    exists x2. split. easy.
    psplit. exact H5. easy.
  }
}
Qed.

Unset Printing Records.

Lemma sem_case_cleared {T A} :
  forall P : AtomicStatePrec T A,
  forall s x m m',
  [[P]] m s x ->
  snd s = CASDef None m' ->
  m = m' /\
  P = SCleared.
unfold atomicPrecSem.
unfold CCleared, COffered, CAcceptd.
intros. destruct P; psimpl.
rewrite H in H0. now ddestruct H0.
rewrite H in H0. now ddestruct H0.
rewrite H in H0. now ddestruct H0.
Qed.

Lemma Rely_is_trans {T A} :
  forall P : AtomicStatePrec T A,
  forall i m s x t y,
  Rely i s x t y ->
  [[P]] m s x ->
  exists Q m',
    [[Q]] m' t y /\
    clos_refl_trans_1n _
      (fun P Q =>
        exists i, AtomicStateTran i P Q)
      P Q.
unfold Rely, Guar. intros.
generalize dependent P.
generalize dependent m.
induction H; intros; psimpl.
{
  exists P, m.
  split. easy.
  constructor.
}
{
  clear H0.
  cut (
    (exists Q m',
      [[Q]] m' t σ /\
      AtomicStateTran x P Q) \/
    (exists m',
      [[P]] m' t σ)
  ).
  {
    intros. psimpl.
    destruct H0.
    {
      psimpl.
      apply IHSRTC in H0. psimpl.
      exists x2, x3. split. easy.
      econstructor.
      exists x. exact H3.
      easy.
    }
    {
      psimpl.
      eapply IHSRTC.
      exact H0.
    }
  }
  clear IHSRTC.
  unfold InvokeAny, ReturnAny in H2.
  elim_disj; psimpl.
  {
    right. exists m.
    apply pres_state in H0. psimpl.
    eapply pres_sem.
    exact H2. exact H0.
    easy.
  }
  {
    left.
    exists x1, None.
    split. easy.
    eapply sem_uniq in H2.
    2: exact H1. psimpl.
    easy.
  }
  {
    right. exists (Some (MkCASPend x (CAS x1 x2))).
    assert (H1' := H1).
    eapply sem_shows_pend in H1'. psimpl.
    rewrite H2 in H5. ddestruct H5.
    clear - H1 H2 H3 H4.
    destruct P; psimpl;
    unfold CCleared, COffered, CAcceptd in *;
    psimpl.
    {
      rewrite H in H2.
      ddestruct H2.
      now rewrite <- H4.
    }
    {
      rewrite H in H2.
      ddestruct H2.
      now rewrite <- H4.
    }
    {
      rewrite H in H2.
      ddestruct H2.
      now rewrite <- H4.
    }
  }
  {
    right. exists None.
    assert (H1' := H1).
    eapply sem_shows_pend in H1'. psimpl.
    rewrite H2 in H0. ddestruct H0.
    clear - H1 H2 H3.
    destruct P; psimpl;
    unfold CCleared, COffered, CAcceptd in *;
    psimpl.
    {
      rewrite H in H2.
      now ddestruct H2.
    }
    {
      rewrite H in H2.
      now ddestruct H2.
    }
    {
      rewrite H in H2.
      now ddestruct H2.
    }
  }
  {
    apply TReturn_pres_state in H0. psimpl.
    right. exists m. eapply pres_sem.
    exact H2. exact H0. easy.
  }
}
Qed.

Lemma float_lift {T A} {PT PF : SPrec T A}:
  (fun b : bool =>
    if b then
      (fun _ _ => LiftSPrec PT) : Relt (VE T A) (VF T A)
    else
      (fun _ _ => LiftSPrec PF)) =
  (fun (b : bool) _ _ => LiftSPrec (if b then PT else PF)).
extensionality b. now destruct b.
Qed.

Lemma exch_correct {T A} {i : Name T} :
  forall v,
  VerifyProg i (LiftSRelt (Rely i)) (LiftSRelt (Guar i))
    (prComp (LiftSPrec (Precs i)) (TInvoke (exchImpl A) i _ (Exch v)) ->> LiftSRelt (Rely i))
    (exch v)
    (fun v' => LiftSRelt (Posts i) ->> PrecToRelt (Returned i (Exch v) v')).
unfold exch. intros.
eapply weakenPrec with
  (P:=fun _ _ => LiftSPrec (fun s x =>
    Precs i s x /\
    PCalls x i = CallPoss (Exch v) /\
    PRets x i = RetIdle)).
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
  exists x0. split. easy.
  split.
  {
    eapply Precs_stable.
    psplit. 2: exact H0.
    apply pres_state in H1. psimpl.
    unfold Precs in *. psimpl.
    exists x3. admit.
  }
  {
    apply Rely_pres_self in H0. psimpl.
    rewrite <- H, <- H0. clear H H0.
    unfold TInvoke in H1. psimpl.
    apply equal_f with (x:=x2) in H3.
    rewrite refl_triv in H3.
    apply eq_triv in H3. psimpl.
    easy.
  }
}
unfold Precs.
eapply lemIf with
  (PT:=fun _ _ => LiftSPrec (fun s x =>
    PCalls x i = CallDone (Exch v) /\
    PRets x i = RetIdle /\
    ((exists m, [[SOffered i v]] m s x) \/
     (exists j w, i <> j /\
      [[SAcceptd i j v w]] None s x))))
  (PF:=fun _ _ => LiftSPrec (fun s x =>
    PCalls x i = CallPoss (Exch v) /\
    PRets x i = RetIdle /\
    Precs i s x)).
{
  rewrite float_lift at 1.
  apply lemCAS.
  {
    admit.
  }
  {
    admit.
  }
  {
    unfold SCommit, CallStep.
    intros. psimpl.
    ddestruct H1. ddestruct H2.
    elim_disj; psimpl;
    unfold CCleared, COffered, CAcceptd in *;
    psimpl.
    2:{
      rewrite H1 in H3. ddestruct H3.
      rewrite H6 in x7. ddestruct x7.
    }
    2:{
      rewrite H10 in H3. ddestruct H3.
      rewrite H6 in x7. ddestruct x7.
    }
    exists (@MkPoss _ _ (VF T A)
      (ExchDef {i => v} {})
      (fun j =>
        if i =? j then
          CallDone (Exch v)
        else
          PCalls x4 j)
      (PRets x4)).
    split.
    {
      eapply PossStepsStep
        with (i:=i).
      4: constructor.
      2:{ cbn. intros. now rewrite eqb_nid. }
      2:{ easy. }
      eapply PCommitCall
        with (m:= Exch v).
      {
        cbn. rewrite <- H7, H1 at 1.
        constructor.
      }
      { now rewrite <- H8 at 1. }
      { cbn. now rewrite eqb_id. }
      { now rewrite <- H9 at 1. }
      { cbn. now rewrite <- H9 at 1. }
    }
    split.
    {
      cbn. rewrite eqb_id.
      split. easy.
      split. now rewrite <- H9.
      left. now exists None.
    }
    {
      left. split.
      { cbn. intros. now rewrite eqb_nid. }
      exists SCleared, (SOffered i v), None, (OFFERED v).
      split. { cbn. unfold CCleared. now rewrite <- H7. }
      split. { easy. }
      constructor.
    }
  }
  {
    unfold SCommit, CallStep.
    intros. psimpl.
    ddestruct H1. ddestruct H2.
    elim_disj; psimpl;
    unfold CCleared, COffered, CAcceptd in *;
    psimpl.
    {
      rewrite H in H3. ddestruct H3.
      rewrite H6 in x7. ddestruct x7.
      easy.
    }
    {
      exists x4.
      split. constructor.
      split.
      {
        split. now rewrite <- H8 at 1.
        split. now rewrite <- H9 at 1.
        exists None.
        rewrite H2 in H3. ddestruct H3.
        rewrite H6 in x7. ddestruct x7.
        right. left.
        exists x8, x9.
        split. easy.
        now rewrite H7 in H10.
      }
      {
        right. right. left.
        exists a, None, (OFFERED v).
        easy.
      }
    }
    {
      exists x4.
      split. constructor.
      split.
      {
        split. now rewrite <- H8 at 1.
        split. now rewrite <- H9 at 1.
        exists None.
        rewrite H11 in H3. ddestruct H3.
        rewrite H6 in x7. ddestruct x7.
        right. right.
        exists x8, x9, x10, x11.
        repeat (split; try easy).
        congruence.
      }
      {
        right. right. left.
        exists a, None, (OFFERED v).
        easy.
      }
    }
  }
}
{
  
}

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
  right. easy.
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
  exists i. split. easy.
  do 3 right. easy.
}
{
  exists initPoss. split. easy.
  exists SCleared, None. easy.
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
  exists x1, x3. eapply pres_sem.
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
      do 2 right.
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