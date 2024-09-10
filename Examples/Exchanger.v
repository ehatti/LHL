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
  TransUtil
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
Import ListNotations.

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
    PState ρ = ExchDef {i => v} {} /\
    PCalls ρ i = CallDone (Exch v) /\
    PRets ρ i = RetIdle.

Definition CAcceptd {A T} m (i j : Name T) (v w : A) : SPrec T A :=
  fun s ρ =>
    snd s = CASDef (ACCEPTED w) m /\
    PState ρ = ExchDef {j => w} {i => v} /\
    PCalls ρ i = CallDone (Exch v) /\
    PRets ρ i = RetIdle.

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
      i <> j /\ j <> k /\
      [[SAcceptd j k v w]] m s x).

Definition Posts {A T} (i : Name T) : SRelt T A :=
  fun _ _ => Precs i.
Notation Pend i m := (Some (MkCASPend i m)).

Variant VisPossStep {T F} {VF : Spec T F} : Poss VF -> ThreadEvent T F -> Poss VF -> Prop :=
| VPCommitCall i A (m : F A) (x y : Poss VF) :
  VF.(Step) x.(PState) (i, CallEv m) y.(PState) ->
  x.(PCalls) i = CallPoss m ->
  y.(PCalls) i = CallDone m ->
  x.(PRets) i = RetIdle ->
  y.(PRets) i = RetIdle ->
  VisPossStep x (i, CallEv m) y
| VPCommitRet i A (m : F A) v (x y : Poss VF) :
  VF.(Step) x.(PState) (i, RetEv m v) y.(PState) ->
  x.(PCalls) i = CallDone m ->
  y.(PCalls) i = CallDone m ->
  x.(PRets) i = RetIdle ->
  y.(PRets) i = RetPoss m v ->
  VisPossStep x (i, RetEv m v) y.

Inductive VisPossSteps {T F} {VF : Spec T F} : Poss VF -> Trace (ThreadEvent T F) -> Poss VF -> Prop :=
| VRefl x :
    VisPossSteps x [] x
| VStep x y z i e p :
    VisPossStep x (i, e) y ->
    differ_pointwise (PCalls x) (PCalls y) i ->
    differ_pointwise (PRets x) (PRets y) i ->
    VisPossSteps y p z ->
    VisPossSteps x ((i, e) :: p) z.

Variant ExchTran {T A} : Name T -> InterState (F A) (VE T A) -> Poss (VF T A) -> InterState (F A) (VE T A) -> Poss (VF T A) -> Prop :=
(* | ExchInvoke i v s x t y :
    TInvoke (exchImpl A) i _ (Exch v) s (eq x) t (eq y) ->
    ExchTran i s x t y
| ExchReturn i v w s x t y :
    TReturn (exchImpl A) i (Exch v) w s (eq x) t (eq y) ->
    ExchTran i s x t y *)
| ExchCall i ths tht a R (m : E A R) x :
    PointStep UnderThreadStep ths (i, Some (CallEv m)) tht ->
    ExchTran i
      (ths, CASDef a None) x
      (tht, CASDef a (Pend i m)) x
(* | ExchFailAccept i ths tht v w x y :
    PointStep UnderThreadStep ths (i, Some (RetEv (CAS (OFFERED w) (ACCEPTED v)) false)) tht ->
    VisPossSteps x [(i, CallEv (Exch v)); (i, RetEv (Exch v) None)] y ->
    ExchTran i
      (ths, CASDef None (Pend i (CAS (OFFERED w) (ACCEPTED v)))) x
      (tht, CASDef None None) y *)
| ExchOffer i ths tht (x y : Poss (VF T A)) v :
    PointStep UnderThreadStep ths (i, Some (RetEv (CAS None (OFFERED v)) true)) tht ->
    VisPossSteps x [(i, CallEv (Exch v))] y ->
    ExchTran i
      (ths, CASDef None (Pend i (CAS None (OFFERED v)))) x
      (tht, CASDef (OFFERED v) None) y
| ExchFailOffer i ths tht a v x :
    a <> None ->
    PointStep UnderThreadStep ths (i, Some (RetEv (CAS None (OFFERED v)) false)) tht ->
    ExchTran i
      (ths, CASDef a (Pend i (CAS None (OFFERED v)))) x
      (tht, CASDef a None) x
| ExchGetPass i ths tht (x : Poss (VF T A)) a :
  PointStep UnderThreadStep ths (i, Some (RetEv Get a)) tht ->
  ExchTran i
    (ths, CASDef a (Pend i Get)) x
    (tht, CASDef a None) x
(* | ExchGetPass i ths tht a x :
    PointStep UnderThreadStep ths (i, Some (RetEv Get a)) tht ->
    ExchTran i
      (ths, CASDef a (Pend i Get)) x
      (tht, CASDef a None) x*)
| ExchGetFail i v ths tht x y :
    PointStep UnderThreadStep ths (i, Some (RetEv Get None)) tht ->
    VisPossSteps x [(i, CallEv (Exch v)); (i, RetEv (Exch v) None)] y ->
    ExchTran i
      (ths, CASDef None (Pend i Get)) x
      (tht, CASDef None None) y
| ExchRevoke i ths tht (x y : Poss (VF T A)) v :
    PointStep UnderThreadStep ths (i, Some (RetEv (CAS (OFFERED v) None) true)) tht ->
    VisPossSteps x [(i, RetEv (Exch v) None)] y ->
    ExchTran i
      (ths, CASDef (OFFERED v) (Pend i (CAS (OFFERED v) None))) x
      (tht, CASDef None None) y
| ExchFailRevoke i ths tht (x : Poss (VF T A)) v w :
    PointStep UnderThreadStep ths (i, Some (RetEv (CAS (OFFERED v) None) false)) tht ->
    ExchTran i
      (ths, CASDef (ACCEPTED w) (Pend i (CAS (OFFERED v) None))) x
      (tht, CASDef (ACCEPTED w) None) x
(* | ExchAccept i j ths tht (x y : Poss (VF T A)) v w :
    PointStep UnderThreadStep ths (i, Some (RetEv (CAS (OFFERED v) (ACCEPTED w)) true)) tht ->
    VisPossSteps x [(j, CallEv (Exch w)); (j, RetEv (Exch w) (Some v))] y ->
    ExchTran j
      (ths, CASDef (OFFERED v) (Pend i (CAS (OFFERED v) (ACCEPTED w)))) x
      (tht, CASDef (ACCEPTED w) None) y*)
| ExchFinish i ths tht (x y : Poss (VF T A)) v w :
    PointStep UnderThreadStep ths (i, Some (RetEv (CAS (ACCEPTED w) None) true)) tht ->
    VisPossSteps x [(i, RetEv (Exch v) (Some w))] y ->
    ExchTran i
      (ths, CASDef (ACCEPTED w) (Pend i (CAS (ACCEPTED w) None))) x
      (tht, CASDef None None) y
.

Definition SomeTran {A T} (R : Name T -> SRelt T A) : SRelt T A :=
  fun s x t y => exists i, R i s x t y.

Definition OtherTran {A T} (i : Name T) (R : Name T -> SRelt T A) : SRelt T A :=
  fun s x t y => exists j, i <> j /\ R j s x t y.

Definition Guar {T A} (i : Name T) : SRelt T A :=
  ExchTran i.

Definition Rely {T A} (i : Name T) : SRelt T A :=
  SRTC (OtherTran i ExchTran).

Lemma forget_other {T A} :
  forall (R : Name T -> SRelt T A) i,
  SRTC (OtherTran i R) S=> SRTC (SomeTran R).
unfold ssub, subSRelt. intros.
induction H. constructor.
destruct H. psimpl.
econstructor.
exists x. exact H1.
easy.
Qed.


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
intros. now exists None.
intros. now exists (OFFERED v).
intros. now exists (ACCEPTED w).
Qed.

(* Subsidiary proofs *)

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

Definition CallStep {T A R} i (m : CASSig (Offer A) R) : SRelt T A :=
  fun s x t y =>
    exists a,
      snd s = CASDef a None /\
      snd t = CASDef a (Some (MkCASPend i m)) /\
      PState x = PState y /\
      PCalls x i = PCalls y i /\
      PRets x i = PRets y i /\
      (forall j, i <> j ->
        PCalls x j <> CallIdle ->
        PCalls x j = PCalls y j /\
        PRets x j = PRets y j).

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
  rewrite H in H0. rewrite H4 in H1.
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

Lemma lemGet {T A} {P : SPrec T A} {i : Name T} :
  forall (Q : option (Offer A) -> SPrec T A),
  (forall v, SStable (Rely i) (Q v)) ->
  (forall v,
    SCommit i
      (Guar i)
      (P <<S CallStep i Get)
      (RetEv Get v)
      (fun _ _ => Q v)) ->
  VerifyProg i
    (LiftSRelt (Rely i)) (LiftSRelt (Guar i))
    (fun _ _ => LiftSPrec P)
    (call Get)
    (fun v _ _ => LiftSPrec (Q v)).
intros.
eapply weakenPost with
  (Q:=fun v =>
    (fun _ _ => LiftSPrec P) ->>
    LiftSRelt (CallStep i Get) ->>
    LiftSRelt (fun _ _ => Q v)).
2:{
  unfold sub, subRelt, LiftSPrec, LiftSRelt.
  intros. psimpl.
  specialize (H2 x3 eq_refl). psimpl.
  specialize (H3 x0 eq_refl). psimpl.
  exists x2. split. easy.
  easy.
}
apply lemCall.
{
  admit.
}
{
  admit.
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
    apply eq_inj in H1. subst.
    exists x. split. easy.
    ddestruct H3. ddestruct H4.
    now exists a.
  }
  {
    intros.
    apply eq_inj in H1. subst.
    exists x. split. easy.
    destruct s, t. cbn in *.
    ddestruct H4. apply ExchCall.
    constructor. easy.
    intros. now rewrite H2.
  }
}
{
  intros.
  eapply weakenCommitPre.
  2:{
    eapply liftSCommit.
    apply H0.
  }
  unfold sub, subPrec, CallStep, LiftSPrec, LiftSRelt.
  intros. psimpl.
  specialize (H2 x3 eq_refl). psimpl.
  exists x2. split. easy.
  psplit. exact H3.
  now exists x4.
}
Admitted.

Lemma lemCAS {T A} {P : SPrec T A} :
  forall (QT QF : SPrec T A) i e n,
  SStable (Rely i) QT ->
  SStable (Rely i) QF ->
  SCommit i
    (Guar i)
    (P <<S CallStep i (CAS e n))
    (RetEv (CAS e n) true)
    (fun _ _ => QT) ->
  SCommit i
    (Guar i)
    (P <<S CallStep i (CAS e n))
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
    LiftSRelt (CallStep i (CAS e n)) ->>
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
  admit.
}
{
  admit.
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
    destruct s, t. cbn in *.
    ddestruct H6. apply ExchCall.
    constructor. easy.
    intros. now rewrite H4.
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
Admitted.

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

Lemma float_lift {T A} {PT PF : SPrec T A}:
  (fun b : bool =>
    if b then
      (fun _ _ => LiftSPrec PT) : Relt (VE T A) (VF T A)
    else
      (fun _ _ => LiftSPrec PF)) =
  (fun (b : bool) _ _ => LiftSPrec (if b then PT else PF)).
extensionality b. now destruct b.
Qed.

Ltac begin_stable :=
  unfold SStable, stableSPrec, ssub, subSPrec,
         stableSRelt, subSRelt;
  intros; psimpl.

Ltac begin_commit :=
  unfold SCommit, CallStep;
  intros; psimpl.


Definition comInvPoss {T F} {VF : Spec T F} i (ρ : Poss VF) {A} (m : F A) (s : State VF) : Poss VF := {|
  PState := s;
  PCalls j := if i =? j then CallDone m else PCalls ρ j;
  PRets j := PRets ρ j
|}.

Definition comRetPoss {T F} {VF : Spec T F} i (ρ : Poss VF) {A} (m : F A) (s : State VF) v : Poss VF := {|
  PState := s;
  PCalls := PCalls ρ;
  PRets j := if i =? j then RetPoss m v else PRets ρ j
|}.

Lemma psteps_trans {T F} {VF : Spec T F} :
  forall x y z : Poss VF,
  PossSteps x y ->
  PossSteps y z ->
  PossSteps x z.
intros. induction H. easy.
eapply PossStepsStep with (i:=i).
4: now apply IHPossSteps.
all: easy.
Qed.

Lemma retStep {T F} {VF : Spec T F} :
  forall i (x z : Poss VF) A (m : F A) v (y : State VF),
  PossSteps x z ->
  (PCalls z i = CallDone m /\
   PRets z i = RetIdle /\
   VF.(Step) (PState z) (i, RetEv m v) y) ->
  PossSteps x (comRetPoss i z m y v).
intros.
eapply psteps_trans.
exact H.
eapply PossStepsStep with
  (i:=i). 4: constructor.
psimpl.
eapply PCommitRet with
  (m:=m) (v:=v).
all: try easy.
cbn. now rewrite eqb_id.
cbn. intros. now rewrite eqb_nid.
Qed.

Lemma callStep {T F} {VF : Spec T F} :
  forall i (x z : Poss VF) A (m : F A) (y : State VF),
  PossSteps x z ->
  (PCalls z i = CallPoss m /\
   PRets z i = RetIdle /\
   VF.(Step) (PState z) (i, CallEv m) y) ->
  PossSteps x (comInvPoss i z m y).
intros.
eapply psteps_trans.
exact H.
eapply PossStepsStep with
  (i:=i). 4: constructor.
psimpl.
eapply PCommitCall with
  (m:=m).
all: try easy.
cbn. now rewrite eqb_id.
cbn. intros. now rewrite eqb_nid.
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
  admit.
}
unfold Precs.
eapply lemIf with
  (PT:=fun _ _ => LiftSPrec (fun s x =>
    ((exists m, [[SOffered i v]] m s x) \/
     (exists m j w, i <> j /\
      [[SAcceptd i j v w]] m s x))))
  (PF:=fun _ _ => LiftSPrec (fun s x =>
    PCalls x i = CallPoss (Exch v) /\
    PRets x i = RetIdle /\
    Precs i s x)).
{
  rewrite float_lift at 1.
  apply lemCAS.
  {
    begin_stable.
    admit.
  }
  {
    begin_stable.
    admit.
  }
  {
    begin_commit.
    ddestruct H1. ddestruct H2.
    elim_disj; psimpl;
    unfold CCleared, COffered, CAcceptd in *;
    psimpl.
    2:{
      rewrite H1 in H3. ddestruct H3.
      rewrite H6 in x7. ddestruct x7.
    }
    2:{
      rewrite H6 in x7. ddestruct x7.
      rewrite H2 in H3. ddestruct H3.
    }
    exists (comInvPoss i x4 (Exch v) (ExchDef {i => v} {})).
    split.
    {
      apply callStep.
      constructor.
      {
        rewrite <- H8, <- H9.
        rewrite <- H7, H1 at 1.
        repeat (easy || constructor).
      }
    }
    split.
    {
      left. exists None.
      cbn. rewrite eqb_id.
      now rewrite <- H9.
    }
    {
      destruct s, t. psimpl.
      rewrite H in H3. ddestruct H3.
      apply ExchOffer.
      {
        constructor; cbn.
        econstructor.
        symmetry. exact x5. easy.
        intros. now rewrite H0.
      }
      {
        econstructor. 4: constructor.
        {
          constructor; cbn.
          { rewrite <- H7, H1. constructor. }
          { now rewrite <- H8. }
          { now rewrite eqb_id. }
          { now rewrite <- H9. }
          { now rewrite <- H9. }
        }
        { apply differ_pointwise_trivial. }
        { easy. }
      }
    }
  }
  {
    begin_commit.
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
        cbn. unfold COffered. cbn.
        apply H10 in H. psimpl. 2: congruence.
        now rewrite <- H, <- H3, <- H7.
      }
      {
        destruct s, t.
        psimpl. rewrite H2 in H3.
        ddestruct H3. ddestruct x7.
        apply ExchFailOffer. easy.
        constructor; cbn.
        {
          econstructor.
          symmetry. exact x5.
          easy.
        }
        { intros. now rewrite H0. }
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
        cbn. unfold CAcceptd. cbn.
        split. easy. split. easy.
        apply H10 in H. psimpl.
        2: congruence.
        now rewrite <- H, <- H3, <- H7.
      }
      {
        destruct s, t. psimpl. ddestruct x7.
        apply ExchFailOffer. easy.
        constructor; cbn.
        {
          econstructor.
          symmetry. exact x5.
          easy.
        }
        { intros. now rewrite H0. }
      }
    }
  }
}
{
  eapply lemIf with
    (PT:=fun _ _ => LiftSPrec (fun s x =>
      Precs i s x /\
      Returned i (Exch v) None s (eq x)))
    (PF:=fun _ _ => LiftSPrec (fun s x =>
      PCalls x i = CallDone (Exch v) /\
      PRets x i = RetIdle /\
      exists m j w, i <> j /\
        [[SAcceptd i j v w]] m s x)).
  {
    erewrite float_lift at 1.
    apply lemCAS.
    {
      begin_stable.
      admit.
    }
    {
      begin_stable.
      admit.
    }
    {
      begin_commit.
      ddestruct H1. ddestruct H2.
      unfold COffered, CAcceptd in H.
      elim_disj; psimpl.
      {
        exists (comRetPoss i x3
          (Exch v)
          (ExchDef {} {})
          None).
        split.
        {
          apply retStep.
          constructor.
          {
            rewrite <- H7, <- H6, <- H5, H1.
            repeat (easy || constructor).
          }
        }
        split.
        {
          split.
          { exists None. now left. }
          {
            unfold Returned.
            intros. psimpl.
            cbn. rewrite eqb_id.
            now rewrite <- H6.
          }
        }
        {
          destruct s, t.
          psimpl. ddestruct x6.
          apply ExchRevoke.
          {
            constructor; cbn.
            {
              econstructor.
              symmetry. exact x4.
              easy.
            }
            { intros. now rewrite H0. }
          }
          {
            econstructor. 4: constructor.
            {
              constructor; cbn.
              { rewrite <- H5, H1. now constructor. }
              { now rewrite <- H6. }
              { now rewrite <- H6. }
              { now rewrite <- H7. }
              { now rewrite eqb_id. }
            }
            { easy. }
            { apply differ_pointwise_trivial. }
          }
        }
      }
      {
        rewrite H1 in H3. ddestruct H3.
        rewrite H4 in x6. ddestruct x6.
      }
    }
    {
      begin_commit.
      ddestruct H1. ddestruct H2.
      unfold COffered, CAcceptd in H.
      elim_disj; psimpl.
      {
        rewrite H in H3. ddestruct H3.
        rewrite H4 in x6. ddestruct x6.
        easy.
      }
      rewrite H2 in H3. ddestruct H3.
      rewrite H4 in x6. ddestruct x6.
      exists x3.
      split.
      { constructor. }
      split.
      {
        cbn. unfold CAcceptd.
        rewrite <- H6, <- H7, <- H5.
        repeat split; try easy.
        now exists None, x8, x9.
      }
      {
        destruct s, t. psimpl.
        apply ExchFailRevoke.
        {
          constructor; cbn.
          {
            econstructor.
            symmetry. exact x4.
            easy.
          }
          { intros. now rewrite H0. }
        }
      }
    }
  }
  {
    apply lemRet.
    unfold sub, subRelt, LiftSPrec.
    intros. psimpl.
    exists t, (eq x).
    split.
    {
      unfold LiftSRelt, Posts.
      intros. psimpl.
      exists x. easy.
    }
    { easy. }
  }
  {
    eapply lemBind.
    {
      eapply lemGet with
        (Q:=fun w s x =>
          PCalls x i = CallDone (Exch v) /\
          PRets x i = RetIdle /\
          exists m w' j, i <> j /\
            w = ACCEPTED w' /\
            [[SAcceptd i j v w']] m s x).
      {
        admit.
      }
      {
        begin_commit. ddestruct H1.
        rewrite H6 in H2. ddestruct H2.
        exists x6. split. constructor.
        unfold CAcceptd in *. psimpl.
        rewrite H1 in H3. ddestruct H3.
        split.
        {
          rewrite <- H8, <- H9 at 1.
          repeat split; try easy.
          exists None, x5, x4.
          rewrite <- H7, <- H8, <- H9.
          easy.
        }
        {
          destruct s, t. psimpl.
          apply ExchGetPass.
          {
            constructor; cbn.
            {
              econstructor.
              symmetry. exact x7.
              easy.
            }
            { intros. now rewrite H0. }
          }
        }
      }
    }
    {
      cbn. intros.
      rename v0 into w.
      destruct w.
      {
        destruct o. rename a into w.
        eapply lemBind.
        {
          eapply lemCAS with
            (QT:=fun s x =>
              Precs i s x /\
              Returned i (Exch v) (Some w) s (eq x))
            (QF:=fun _ _ => False).
          {
            begin_stable.
            admit.
          }
          {
            begin_stable.
            admit.
          }
          {
            begin_commit.
            ddestruct H1. ddestruct H2.
            unfold CAcceptd in H12. psimpl.
            rewrite H1 in H3. ddestruct H3.
            rewrite H6 in x9. ddestruct x9.
            exists (comRetPoss i x6
              (Exch v)
              (ExchDef {} {})
              (Some x4)).
            split.
            {
              apply retStep.
              constructor.
              {
                rewrite <- H8, <- H9, <- H7, H2.
                repeat (easy || constructor).
              }
            }
            split.
            {
              split.
              { exists None. now left. }
              {
                unfold Returned. intros. psimpl.
                cbn. now rewrite eqb_id, <- H8.
              }
            }
            {
              destruct s, t. psimpl.
              eapply ExchFinish with
                (v:=v).
              {
                constructor; cbn.
                {
                  econstructor.
                  symmetry. exact x7.
                  easy.
                }
                { intros. now rewrite H0. }
              }
              {
                econstructor. 4: constructor.
                {
                  constructor; cbn.
                  { rewrite <- H7, H2. now constructor. }
                  { now rewrite <- H8. }
                  { now rewrite <- H8. }
                  { now rewrite <- H9. }
                  { now rewrite eqb_id. }
                }
                { easy. }
                { apply differ_pointwise_trivial. }
              }
            }
          }
          {
            begin_commit. ddestruct H2.
            unfold CAcceptd in *. psimpl.
            rewrite H12 in H3. ddestruct H3.
            rewrite H6 in x7. ddestruct x7.
            easy.
          }
        }
        {
          intros. apply lemRet.
          unfold sub, subRelt, LiftSPrec, LiftSRelt.
          intros. psimpl. destruct v0. 2: easy.
          exists t, (eq x). split.
          { intros. now exists x. }
          { easy. }
        }
      }
      {
        apply lemRet.
        unfold sub, subRelt, LiftSPrec.
        intros. psimpl.
        congruence.
      }
    }
  }
}
{
  eapply lemBind.
  {
    apply lemGet with
      (Q:=fun w s x =>
        Precs i s x /\
        match w with
        | Some _ =>
            PCalls x i = CallPoss (Exch v) /\
            PRets x i = RetIdle
        | None =>
            PCalls x i = CallDone (Exch v) /\
            PRets x i = RetPoss (Exch v) None
        end).
    {
      begin_stable.
      admit.
    }
    {
      begin_commit.
      ddestruct H2. ddestruct H1.
      destruct v0.
      {
        exists x3.
        split. constructor.
        split.
        {
          split. 2: now rewrite <- H8, <- H9.
          unfold Precs in H5. psimpl.
          unfold CCleared, COffered, CAcceptd in H1.
          exists None.
          elim_disj; psimpl.
          {
            rewrite H1 in H3. ddestruct H3.
            rewrite H6 in x5. ddestruct x5.
          }
          {
            rewrite H2 in H3. ddestruct H3.
            rewrite H6 in x5. ddestruct x5.
            right. left. exists x8, x9.
            split. easy. unfold COffered.
            apply H10 in H1. psimpl.
            rewrite <- H1, <- H3, <- H7, H5.
            easy. congruence.
          }
          {
            rewrite H5 in H3. ddestruct H3.
            rewrite H6 in x5. ddestruct x5.
            right. right. exists x8, x9, x10, x11.
            split. easy. split. easy. unfold CAcceptd.
            apply H10 in H1. psimpl.
            rewrite <- H1, <- H3, <- H7, H11.
            easy. congruence.
          }
        }
        {
          destruct s, t. psimpl.
          destruct x2; ddestruct x5.
          apply ExchGetPass.
          {
            constructor; cbn.
            {
              econstructor.
              symmetry. exact x4.
              easy.
            }
            { intros. now rewrite H0. }
          }
        }
      }
      {
        unfold Precs in H5. psimpl.
        unfold CCleared, COffered, CAcceptd in H1.
        elim_disj; psimpl.
        2:{
          rewrite H2 in H3. ddestruct H3.
          rewrite H6 in x5. ddestruct x5.
        }
        2:{
          rewrite H5 in H3. ddestruct H3.
          rewrite H6 in x5. ddestruct x5.
        }
        rewrite H1 in H3. ddestruct H3.
        rewrite H6 in x5. ddestruct x5.
        exists (
          comRetPoss i
            (comInvPoss i x3
              (Exch v)
              (ExchDef {i => v} {}))
            (Exch v)
            (ExchDef {} {})
            None
        ).
        split.
        {
          apply retStep.
          apply callStep.
          constructor.
          {
            rewrite <- H8, <- H9, <- H7, H2.
            repeat (easy || constructor).
          }
          {
            cbn. rewrite eqb_id, <- H9.
            repeat (easy || constructor).
          }
        }
        split.
        {
          cbn. rewrite eqb_id.
          split. 2: easy.
          exists None. now left.
        }
        {
          destruct s, t. psimpl.
          apply ExchGetFail with
            (v:=v).
          {
            constructor; cbn.
            {
              econstructor.
              symmetry. exact x4.
              easy.
            }
            { intros. now rewrite H0. }
          }
          {
            eapply VStep with
              (y:= comInvPoss i x3 (Exch v) (ExchDef {i => v} {})).
            {
              constructor; cbn.
              { rewrite <- H7, H2. constructor. }
              { now rewrite <- H8. }
              { now rewrite eqb_id. }
              { now rewrite <- H9. }
              { now rewrite <- H9. }
            }
            { apply differ_pointwise_trivial. }
            { easy. }
            econstructor. 4: constructor.
            {
              constructor; cbn.
              { constructor. }
              { now rewrite eqb_id. }
              { now rewrite eqb_id. }
              { now rewrite <- H9. }
              { now rewrite eqb_id. }
            }
            { easy. }
            { apply differ_pointwise_trivial. }
          }
        }
      }
    }
  }
  {
    intros. cbn. destruct v0.
    {
      destruct o.
      rename a into w.
      eapply lemIf with
        (PT:=fun _ _ => LiftSPrec (fun s x =>
          Precs i s x /\
          PCalls x i = CallDone (Exch v) /\
          PRets x i = RetPoss (Exch v) (Some w)))
        (PF:=fun _ _ => LiftSPrec (fun s x =>
          Precs i s x /\
          PCalls x i = CallDone (Exch v) /\
          PRets x i = RetPoss (Exch v) None)).
      {
        erewrite float_lift.
        eapply lemCAS.
        {
          begin_stable.
          admit.
        }
        {
          begin_stable.
          admit.
        }
        {
          begin_commit.
          ddestruct H1. ddestruct H2.
          unfold Precs in H. psimpl.
          unfold CCleared, COffered, CAcceptd in H.
          elim_disj; psimpl.
          {
            rewrite H in H3. ddestruct H3.
            rewrite H6 in x6. ddestruct x6.
          }
          2:{
            rewrite H2 in H3. ddestruct H3.
            rewrite H6 in x6. ddestruct x6.
          }
          rewrite H1 in H3. ddestruct H3.
          rewrite H6 in x6. ddestruct x6.
          rename x9 into w. rename x8 into j.
          exists (@MkPoss _ _ (VF T A)
            (ExchDef {i => v} {j => w})
            (fun k =>
              if i =? k then
                CallDone (Exch v)
              else
                PCalls x3 k)
            (fun k =>
              if i =? k then
                RetPoss (Exch v) (Some w)
              else
                PRets x3 k)).
          split.
          {
            eapply PossStepsStep with
              (i:=i)
              (σ:= comInvPoss i x3
                (Exch v)
                (ExchDef {i => v, j => w} {})).
            {
              eapply PCommitCall with
                (m:= Exch v).
              {
                cbn. rewrite <- H7, H2 at 1.
                now constructor.
              }
              { now rewrite <- H8 at 1. }
              { cbn. now rewrite eqb_id. }
              { now rewrite <- H9 at 1. }
              { cbn. now rewrite <- H9 at 1. }
            }
            { cbn. intros. now rewrite eqb_nid. }
            { easy. }
            eapply PossStepsStep with
              (i:=i). 4: constructor.
            {
              eapply PCommitRet with
                (m:= Exch v) (v:= Some w).
              { cbn. now constructor. }
              { cbn. now rewrite eqb_id. }
              { cbn. now rewrite eqb_id. }
              { cbn. now rewrite <- H9. }
              { cbn. now rewrite eqb_id. }
            }
            { easy. }
            { cbn. intros. now rewrite eqb_nid. }
          }
          split.
          {
            cbn. split.
            {
              exists None. right. right.
              exists j, i, w, v.
              split. easy.
              split. easy.
              cbn. unfold CAcceptd. cbn.
              rewrite eqb_nid; try easy.
              move H at bottom. apply H10 in H.
              psimpl. now rewrite <- H, <- H3.
              congruence.
            }
            { now rewrite eqb_id. }
          }
          {
            destruct s, t. psimpl.
            apply ExchAccept.
            {
              constructor.
              econstructor; cbn.
              symmetry. exact x4. easy.
              intros. now rewrite H0.
            }
            {
              eapply VStep with
                (y:=(@MkPoss _ _ (VF T A)
                  (ExchDef {i => v, j => w} {})
                  (fun k =>
                    if i =? k then
                      CallDone (Exch v)
                    else
                      PCalls x3 k)
                  (PRets x3))).
              {
                constructor.
                {
                  cbn. rewrite <- H7, H2.
                  constructor. easy.
                }
                { now rewrite <- H8 at 1. }
                { cbn. now rewrite eqb_id. }
                { now rewrite <- H9. }
                { cbn. now rewrite <- H9. }
              }
              { apply differ_pointwise_trivial. }
              { easy. }
              eapply VStep with
                (y:=(@MkPoss _ _ (VF T A)
                  (ExchDef {i => v} {j => w})
                  (fun k =>
                    if i =? k then
                      CallDone (Exch v)
                    else
                      PCalls x3 k)
                  (fun k =>
                    if i =? k then
                      RetPoss (Exch v) (Some w)
                    else
                      PRets x3 k))).
              {
                constructor.
                { now constructor. }
                { cbn. now rewrite eqb_id. }
                { cbn. now rewrite eqb_id. }
                { cbn. now rewrite <- H9. }
                { cbn. now rewrite eqb_id. }
              }
              { easy. }
              { apply differ_pointwise_trivial. }
              constructor.
            }
          }
        }
        {
          begin_commit.
          ddestruct H2. ddestruct H1.
          assert (x5' := x5).
          rewrite H6 in x5. ddestruct x5.
          unfold Precs in H. psimpl.
          unfold CCleared, COffered, CAcceptd in H.
          elim_disj; psimpl.
          {
            exists (@MkPoss _ _ (VF T A)
              (ExchDef {} {})
              (fun j =>
                if i =? j then
                  CallDone (Exch v)
                else
                  PCalls x3 j)
              (fun j =>
                if i =? j then
                  RetPoss (Exch v) None
                else
                  PRets x3 j)).
            split.
            {
              eapply PossStepsStep with
                (i:=i) (σ:= comInvPoss i x3
                  (Exch v)
                  (ExchDef {i => v} {})).
              {
                eapply PCommitCall with
                  (m:= Exch v).
                {
                  rewrite <- H7, H1 at 1.
                  constructor.
                }
                { now rewrite <- H8 at 1. }
                { cbn. now rewrite eqb_id. }
                { now rewrite <- H9 at 1. }
                { cbn. now rewrite <- H9. }
              }
              { cbn. intros. now rewrite eqb_nid. }
              { easy. }
              eapply PossStepsStep with
                (i:=i). 4: constructor.
              {
                eapply PCommitRet with
                  (m:= Exch v) (v:= None).
                { constructor. }
                { cbn. now rewrite eqb_id. }
                { cbn. now rewrite eqb_id. }
                { cbn. now rewrite <- H9. }
                { cbn. now rewrite eqb_id. }
              }
              { easy. }
              { cbn. intros. now rewrite eqb_nid. }
            }
            rewrite H in H3. ddestruct H3.
            rewrite H6 in x5'. ddestruct x5'.
            split.
            {
              split.
              exists None. now left.
              cbn. now rewrite eqb_id.
            }
            {
              destruct s, t. psimpl.
              apply ExchFail.
              {
                constructor.
                {
                  econstructor; cbn.
                  symmetry. exact x4.
                  easy.
                }
                { intros. now rewrite H0. }
              }
              {
                eapply VStep with
                  (y:=(@MkPoss _ _ (VF T A)
                    (ExchDef {i => v} {})
                    (fun k =>
                      if i =? k then
                        CallDone (Exch v)
                      else
                        PCalls x3 k)
                    (PRets x3))).
                {
                  constructor; cbn.
                  { rewrite <- H7, H1. constructor. }
                  { now rewrite <- H8. }
                  { now rewrite eqb_id. }
                  { now rewrite <- H9. }
                  { now rewrite <- H9. }
                }
                { apply differ_pointwise_trivial. }
                { easy. }
                eapply VStep with
                  (y:=(@MkPoss _ _ (VF T A)
                    (ExchDef {} {})
                    (fun k =>
                      if i =? k then
                        CallDone (Exch v)
                      else
                        PCalls x3 k)
                    (fun k =>
                      if i =? k then
                        RetPoss (Exch v) None
                      else
                        PRets x3 k))).
                {
                  constructor; cbn.
                  { constructor. }
                  { now rewrite eqb_id. }
                  { now rewrite eqb_id. }
                  { now rewrite <- H9. }
                  { now rewrite eqb_id. }
                }
                { easy. }
                { apply differ_pointwise_trivial. }
                constructor.
              }
            }
          }
          {
            rewrite H1 in H3. ddestruct H3.
            rewrite H6 in x5'. ddestruct x5'.
            exists (
              comRetPoss i
                (comInvPoss i
                  (comRetPoss x7
                    x3
                    (Exch x8)
                    (ExchDef {} {})
                    None)
                  (Exch v)
                  (ExchDef {i => v} {}))
                (Exch v)
                (ExchDef {} {})
                None
            ).
            split.
            {
              apply retStep.
              apply callStep.
              apply retStep.
              constructor.
              {
                apply H10 in H. psimpl. 2: congruence.
                rewrite <- H, <- H3, <- H7, H11.
                repeat (easy || constructor).
              }
              {
                cbn. rewrite eqb_nid; try easy.
                rewrite <- H8, <- H9.
                repeat (easy || constructor).
              }
              {
                cbn. rewrite eqb_id, eqb_nid; try easy.
                rewrite <- H9.
                repeat (easy || constructor).
              }              
            }
            split.
            {
              admit.
            }
            {
              admit.
            }
          }
          {
            rewrite H11 in H3. ddestruct H3.
            rewrite H6 in x5'. ddestruct x5'.
            exists (
              comRetPoss i
                (comInvPoss i
                  (comRetPoss x7
                    x3
                    (Exch x9)
                    (ExchDef {} {})
                    (Some x10))
                  (Exch v)
                  (ExchDef {i => v} {}))
                (Exch v)
                (ExchDef {} {})
                None
            ).
            split.
            {
              apply H10 in H. psimpl.
              2: congruence.
              apply retStep.
              apply callStep.
              apply retStep.
              constructor.
              {
                rewrite <- H7, H12.
                repeat (constructor || easy).
                now rewrite <- H.
                now rewrite <- H3.
              }
              {
                cbn. rewrite eqb_nid; try easy.
                rewrite <- H8, <- H9.
                repeat (constructor || easy).
                unfold not. intro. subst.
                apply H10 in H1. psimpl.
                2: congruence.
                rewrite H13 in H4. ddestruct H4.
              }
              {
                cbn. rewrite eqb_id, eqb_nid; try easy.
                2:{
                  unfold not. intro. subst.
                  apply H10 in H1. psimpl.
                  2: congruence.
                  rewrite H13 in H4. ddestruct H4.
                }
                rewrite <- H9.
                repeat (constructor || easy).
              }
            }
            split.
            {
              split.
              {
                unfold comRetPoss, comInvPoss. cbn.

              }
            }
          }
        }
      }
      {
        eapply lemRet.
        unfold sub, subRelt, LiftSPrec.
        intros. unfold Posts, LiftSRelt.
        psimpl. psplit.
        2:{
          split. 2: easy.
          unfold Returned.
          intros. subst.
          easy.
        }
        {
          intros. subst.
          exists x. easy.
        }
      }
      {
        eapply lemRet.
        unfold sub, subRelt, LiftSPrec.
        intros. unfold Posts, LiftSRelt.
        psimpl. psplit.
        2:{
          split. 2: easy.
          unfold Returned.
          intros. subst.
          easy.
        }
        {
          intros. subst.
          exists x. easy.
        }
      }
    }
    {
      eapply lemRet.
      unfold sub, subRelt, LiftSPrec.
      intros. unfold Posts, LiftSRelt.
      psimpl. psplit.
      2:{
        split. 2: easy.
        unfold Returned.
        intros. subst.
        easy.
      }
      {
        intros. subst.
        exists x. easy.
      }
    }
  }
}
Qed.

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