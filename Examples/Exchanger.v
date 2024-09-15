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

Variant Offer {T A} :=
| Offered (i : Name T) (v : A)
| Accepted (i j : Name T) (v w : A).
Arguments Offer : clear implicits.

Notation OFFERED i v := (Some (Offered i v)).
Notation ACCEPTED i j v w := (Some (Accepted i j v w)).
Notation EMPTY := (None (A:= Offer _ _)).

Definition E T A :=
  CASSig (Offer T A).

Definition VE T A : Spec T (E T A) :=
  casSpec.

Definition F A := ExchSig A.

Definition VF T A : Spec T (F A) :=
  exchSpec.

(* Code *)

Definition exch {T A} (i : Name T) (v : A) : Prog (E T A) (option A) :=
  my_offer_placed <- call (CAS None (OFFERED i v));
  if my_offer_placed : bool then
    no_change <- call (CAS (OFFERED i v) EMPTY);
    if no_change : bool then
      ret None
    else
      w <- call Get;
      match w : option (Offer T A) with
      | ACCEPTED _ _ _ w' =>
          call (CAS w EMPTY);;
          ret (Some w')
      | _ =>
          ret None (* impossible *)
      end
  else
    w <- call Get;
    match w : option (Offer T A) with
    | OFFERED j w =>
        my_offer_accepted <- call (CAS (OFFERED j w) (ACCEPTED j i w v));
        if my_offer_accepted : bool then
          ret (Some w)
        else
          ret None
    | _ =>
        ret None
    end.

Definition exchImpl {T A} (i : Name T) : Impl (E T A) (F A) :=
  fun _ m => match m with
  | Exch v => exch i v
  end.

(* Conditions *)

Definition SRelt T A := SRelt (VE T A) (VF T A).
Definition SPrec T A := SPrec (VE T A) (VF T A).

Variant AtomicStatePrec {T A} :=
| SCleared
| SOffered (i : Name T) (v : A)
| SAcceptd (i j : Name T) (v w : A).
Arguments AtomicStatePrec : clear implicits.

Definition CCleared {A T} m : SPrec T A :=
  fun s ρ =>
    snd s = CASDef None m /\
    PState ρ = ExchDef {} {}.

Definition COffered {A T} m (i : Name T) (v : A) : SPrec T A :=
  fun s ρ =>
    snd s = CASDef (OFFERED i v) m /\
    PState ρ = ExchDef {} {} /\
    PCalls ρ i = CallPoss (Exch v) /\
    PRets ρ i = RetIdle.

Definition CAcceptd {A T} m (i j : Name T) (v w : A) : SPrec T A :=
  fun s ρ =>
    snd s = CASDef (ACCEPTED i j v w) m /\
    PState ρ = ExchDef {} {} /\
    PCalls ρ i = CallDone (Exch v) /\
    PRets ρ i = RetPoss (Exch v) (Some w).

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

Notation UnderStep s i e t := (PointStep UnderThreadStep s (i, Some e) t).

Variant ExchTran {T A} : Name T -> InterState (F A) (VE T A) -> Poss (VF T A) -> InterState (F A) (VE T A) -> Poss (VF T A) -> Prop :=
| ExchInvoke i v s x t y :
    TInvoke (exchImpl i) i _ (Exch v) s (eq x) t (eq y) ->
    ExchTran i s x t y
| ExchReturn i v w s x t y :
    TReturn (exchImpl i) i (Exch v) w s (eq x) t (eq y) ->
    ExchTran i s x t y
| ExchCall i ths tht a R (m : E T A R) x :
    UnderStep ths i (CallEv m) tht ->
    ExchTran i
      (ths, CASDef a None) x
      (tht, CASDef a (Pend i m)) x
| ExchOfferPass i ths tht v x :
    UnderStep ths i (RetEv (CAS EMPTY (OFFERED i v)) true) tht ->
    ExchTran i
      (ths, CASDef EMPTY (Pend i (CAS EMPTY (OFFERED i v)))) x
      (tht, CASDef (OFFERED i v) None) x
| ExchRevokePass i ths tht v x y :
    VisPossSteps x [(i, CallEv (Exch v)); (i, RetEv (Exch v) None)] y ->
    UnderStep ths i (RetEv (CAS (OFFERED i v) EMPTY) true) tht ->
    ExchTran i
      (ths, CASDef (OFFERED i v) (Pend i (CAS (OFFERED i v) EMPTY))) x
      (tht, CASDef EMPTY None) y
| ExchRevokeFail i ths tht a v x :
    a <> OFFERED i v ->
    UnderStep ths i (RetEv (CAS (OFFERED i v) EMPTY) false) tht ->
    ExchTran i
      (ths, CASDef a (Pend i (CAS (OFFERED i v) EMPTY))) x
      (tht, CASDef a None) x
| ExchGetAccept i j ths tht v w x :
    i <> j ->
    UnderStep ths i (RetEv Get (ACCEPTED i j v w)) tht ->
    ExchTran i
      (ths, CASDef (ACCEPTED i j v w) (Pend i Get)) x
      (tht, CASDef (ACCEPTED i j v w) None) x
| ExchFinishPass i j ths tht v w x :
    i <> j ->
    UnderStep ths i (RetEv (CAS (ACCEPTED i j v w) EMPTY) true) tht ->
    ExchTran i
      (ths, CASDef (ACCEPTED i j v w) (Pend i (CAS (ACCEPTED i j v w) EMPTY))) x
      (tht, CASDef EMPTY None) x
| ExchOfferFail i ths tht a v x :
    a <> EMPTY ->
    UnderStep ths i (RetEv (CAS EMPTY (OFFERED i v)) false) tht ->
    ExchTran i
      (ths, CASDef a (Pend i (CAS EMPTY (OFFERED i v)))) x
      (tht, CASDef a None) x
| ExchGetOfferPass i j ths tht w x :
    i <> j ->
    UnderStep ths i (RetEv Get (OFFERED j w)) tht ->
    ExchTran i
      (ths, CASDef (OFFERED j w) (Pend i Get)) x
      (tht, CASDef (OFFERED j w) None) x
| ExchGetOfferFail i ths tht a v x y :
    ~(exists j w, i <> j /\ a = OFFERED j w) ->
    VisPossSteps x [(i, CallEv (Exch v)); (i, RetEv (Exch v) None)] y ->
    UnderStep ths i (RetEv Get a) tht ->
    ExchTran i
      (ths, CASDef a (Pend i Get)) x
      (tht, CASDef a None) y
| ExchAcceptPass i j ths tht v w x y :
    i <> j ->
    VisPossSteps x [(j, CallEv (Exch w)); (i, CallEv (Exch v)); (i, RetEv (Exch v) (Some w)); (j, RetEv (Exch w) (Some v))] y ->
    UnderStep ths i (RetEv (CAS (OFFERED j w) (ACCEPTED j i w v)) true) tht ->
    ExchTran i
      (ths, CASDef (OFFERED j w) (Pend i (CAS (OFFERED j w) (ACCEPTED j i w v)))) x
      (tht, CASDef (ACCEPTED j i w v) None) y
| ExchAcceptFail i j ths tht a v w x y :
    i <> j ->
    a <> OFFERED j w ->
    VisPossSteps x [(i, CallEv (Exch v)); (i, RetEv (Exch v) None)] y ->
    UnderStep ths i (RetEv (CAS (OFFERED j w) (ACCEPTED j i w v)) false) tht ->
    ExchTran i
      (ths, CASDef a (Pend i (CAS (OFFERED j w) (ACCEPTED j i w v)))) x
      (tht, CASDef a None) y.

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

Lemma erase_vis {T F} {VF : Spec T F} :
  forall (x y : Poss VF) p,
  VisPossSteps x p y ->
  PossSteps x y.
intros. induction H. constructor.
cut (PossStep i x y).
{
  intros. econstructor.
  exact H3.
  intros. now rewrite H0.
  intros. now rewrite H1.
  easy.
}
clear - H. ddestruct H.
{
  eapply PCommitCall.
  exact H. all: easy.
}
{
  eapply PCommitRet.
  exact H. all: easy.
}
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
  TInvoke (VE:= VE T A) (VF:= VF T A) (exchImpl i) i R m s (eq ρ) t (eq σ) ->
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
  TReturn (VE:= VE T A) (VF:= VF T A) (exchImpl i) i m v s (eq ρ) t (eq σ) ->
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
  TInvoke (VE:= VE T A) (VF:= VF T A) (exchImpl i) i R m s (eq ρ) t σs ->
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
  TReturn (VE:= VE T A) (VF:= VF T A) (exchImpl i) i m v s (eq ρ) t σs ->
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
intros. now exists (OFFERED i v).
intros. now exists (ACCEPTED i j v w).
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

Definition CallStep {T A R} i (m : CASSig (Offer T A) R) : SRelt T A :=
  fun s x t y =>
    exists a,
      snd s = CASDef a None /\
      snd t = CASDef a (Some (MkCASPend i m)) /\
      PState y = PState x /\
      PCalls y i = PCalls x i /\
      PRets y i = PRets x i /\
      (forall j, i <> j ->
        PCalls x j <> CallIdle ->
        ~(exists A (m : _ A) v, PRets x j = RetPoss m v) ->
        PCalls y j = PCalls x j /\
        PRets y j = PRets x j).

Ltac begin_stable :=
  unfold SStable, stableSPrec, ssub, subSPrec;
  unfold stableSRelt, subSRelt;
  unfold Stable, stablePrec, sub, subPrec;
  unfold stablePost, stableRelt, subRelt;
  unfold sub, subRelt;
  intros; psimpl.

Ltac begin_commit :=
  unfold SCommit, CallStep;
  intros; psimpl.

Ltac begin_return :=
  unfold sub, subRelt, LiftSPrec, LiftSRelt in *;
  intros; psimpl.

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

Lemma sing_elem {A} {P : A -> Prop} :
  forall x : A,
  eq x = P ->
  P x.
intros. now rewrite <- H.
Qed.

Lemma call_stable {T} :
  forall i A R (m : _ R),
  SStable (Rely (T:=T) (A:=A) i) (CallStep i m).
begin_stable. unfold ssub. intros. psimpl.
generalize dependent s.
generalize dependent ρ.
induction H0. easy.
intros. apply IHSRTC. clear - H H1.
unfold CallStep, OtherTran in *. psimpl.
exists x. split. easy.
ddestruct H6.
{
  unfold TInvoke, InterOStep in H0.
  psimpl. ddestruct H7.
  cbn in *. ddestruct H1.
  apply sing_elem in H9. psimpl.
  rewrite <- H8, H13, H14, H9; try easy.
  do 4 (split;[easy|idtac]). intros.
  assert (i0 <> j).
  {
    unfold not. intros. subst.
    unfold TIdle in H0. psimpl.
    specialize (H17 x3 eq_refl). psimpl.
    apply H10 in H. psimpl.
    2: congruence. 2: easy.
    rewrite <- H, H1 in H15. easy.
  }
  rewrite H13, H14; try easy.
  now apply H10.
}
{
  unfold TReturn, InterOStep, mapRetPoss in H0.
  psimpl. ddestruct H7.
  cbn in *. ddestruct H1.
  apply sing_elem in H9. psimpl.
  rewrite <- H8, H16, H14, H15; try easy.
  do 4 (split;[easy|idtac]). intros.
  assert (i0 <> j).
  {
    unfold not. intros. subst.
    apply H10 in H1. psimpl.
    2: congruence. 2: easy.
    apply H18. rewrite <- H19.
    now exists _, (Exch v), w.
  }
  rewrite H14, H15; try easy.
  now apply H10.
}
{ easy. }
{ now ddestruct H2. }
{ now ddestruct H3. }
{ now ddestruct H3. }
{ now ddestruct H3. }
{ now ddestruct H3. }
{ now ddestruct H3. }
{ now ddestruct H3. }
{ now ddestruct H4. }
{ now ddestruct H4. }
{ now ddestruct H5. }
Qed.

Lemma lemGet {T A} {P : SPrec T A} {i : Name T} :
  forall (Q : option (Offer T A) -> SPrec T A),
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
  apply liftSReltStable.
  apply call_stable.
}
{
  begin_stable. unfold LiftSRelt in *.
  intros. psimpl.
  specialize (H1 x1 eq_refl). psimpl.
  specialize (H2 x2 eq_refl). psimpl.
  exists x0. split. easy.
  apply H. psplit.
  exact H3. easy.
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
Qed.

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
  apply liftSReltStable.
  apply call_stable.
}
{
  begin_stable. unfold LiftSRelt in *.
  intros. psimpl.
  specialize (H3 x1 eq_refl). psimpl.
  specialize (H4 x2 eq_refl). psimpl.
  exists x0. split. easy.
  destruct v.
  {
    apply H. psplit.
    exact H5. easy.
  }
  {
    apply H0. psplit.
    exact H5. easy.
  }
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

Lemma float_lift {T A} {PT PF : SPrec T A}:
  (fun b : bool =>
    if b then
      (fun _ _ => LiftSPrec PT) : Relt (VE T A) (VF T A)
    else
      (fun _ _ => LiftSPrec PF)) =
  (fun (b : bool) _ _ => LiftSPrec (if b then PT else PF)).
extensionality b. now destruct b.
Qed.

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
  forall (x y z : Poss VF) p q,
  VisPossSteps x p y ->
  VisPossSteps y q z ->
  VisPossSteps x (p ++ q) z.
intros. induction H. easy.
eapply VStep with (i:=i).
4: now apply IHVisPossSteps.
all: easy.
Qed.

Lemma retStep {T F} {VF : Spec T F} :
  forall i (x z : Poss VF) p A (m : F A) v (y : State VF),
  VisPossSteps x p z ->
  (PCalls z i = CallDone m /\
   PRets z i = RetIdle /\
   VF.(Step) (PState z) (i, RetEv m v) y) ->
  VisPossSteps x (p ++ [(i, RetEv m v)]) (comRetPoss i z m y v).
intros.
eapply psteps_trans.
exact H.
eapply VStep with
  (i:=i). 4: constructor.
psimpl.
eapply VPCommitRet with
  (m:=m) (v:=v).
all: try easy.
cbn. now rewrite eqb_id.
apply differ_pointwise_trivial.
Qed.

Lemma callStep {T F} {VF : Spec T F} :
  forall i (x z : Poss VF) p A (m : F A) (y : State VF),
  VisPossSteps x p z ->
  (PCalls z i = CallPoss m /\
   PRets z i = RetIdle /\
   VF.(Step) (PState z) (i, CallEv m) y) ->
  VisPossSteps x (p ++ [(i, CallEv m)]) (comInvPoss i z m y).
intros.
eapply psteps_trans.
exact H.
eapply VStep with
  (i:=i). 4: constructor.
psimpl.
eapply VPCommitCall with
  (m:=m).
all: try easy.
cbn. now rewrite eqb_id.
apply differ_pointwise_trivial.
Qed.

Lemma exch_correct {T A} {i : Name T} :
  forall v,
  VerifyProg i (LiftSRelt (Rely (A:=A) i)) (LiftSRelt (Guar i))
    (prComp (LiftSPrec (Precs i)) (TInvoke (exchImpl i) i _ (Exch v)) ->> LiftSRelt (Rely i))
    (exch i v)
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
    exists x4.
    split. constructor.
    split.
    {
      left. exists None.
      now rewrite H7, H8, H9.
    }
    {
      destruct s, t. psimpl.
      rewrite H in H3. ddestruct H3.
      clear x7. apply ExchOfferPass.
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
    begin_commit.
    intros. psimpl.
    ddestruct H1. ddestruct H2.
    elim_disj; psimpl;
    unfold Precs; cbn;
    unfold CCleared, COffered, CAcceptd in *;
    psimpl.
    {
      rewrite H in H3. ddestruct H3.
      rewrite H6 in x7. ddestruct x7.
      easy.
    }
    {
      exists x4.
      rewrite H2 in H3. ddestruct H3.
      rewrite H6 in x7. ddestruct x7.
      split. constructor.
      split.
      {
        rewrite H8, H9.
        split. easy. split. easy.
        exists None. right. left.
        exists x8, x9.
        rewrite H7. split. easy.
        apply H10 in H. psimpl.
        now rewrite H, H3.
        { congruence. }
        {
          unfold not. intros. psimpl.
          rewrite H13 in H3. ddestruct H3.
        }
      }
      {
        destruct s, t. psimpl.
        apply ExchOfferFail. easy.
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
      rewrite H11 in H3. ddestruct H3.
      rewrite H6 in x7. ddestruct x7.
      split. constructor.
      split.
      {
        rewrite H8, H9.
        split. easy. split. easy.
        exists None. right. right.
        exists x8, x9, x10, x11.
        do 3 (split;[easy|idtac]).
        apply H10 in H. psimpl.
        all: try congruence.
        now rewrite H, H3, H7.
        {
          unfold not. intros. psimpl.
        }
      }
      {
        destruct s, t. psimpl.
        apply ExchOfferFail. easy.
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
        exists (
          comRetPoss i
            (comInvPoss i
              x3
              (Exch v)
              (ExchDef {i => v} {}))
            (Exch v)
            (ExchDef {} {})
            None
        ).
        assert (
          VisPossSteps
            x3
            ([(i, CallEv (Exch v))] ++ [(i, RetEv (Exch v) None)])
            (comRetPoss i
              (comInvPoss i
                x3
                (Exch v)
                (ExchDef {i => v} {}))
              (Exch v)
              (ExchDef {} {})
              None)
        ).
        {
          apply retStep.
          apply callStep with (p:=[]).
          constructor.
          {
            rewrite H6, H7, H5, H1.
            repeat (easy || constructor).
          }
          {
            cbn. rewrite eqb_id, H7.
            repeat (easy || constructor).
          }
        }
        split.
        {
          eapply erase_vis.
          exact H10.
        }
        split.
        {
          split.
          { exists None. now left. }
          {
            unfold Returned.
            intros. psimpl.
            cbn. now rewrite eqb_id.
          }
        }
        {
          destruct s, t.
          psimpl. ddestruct x6.
          apply ExchRevokePass.
          { easy. }
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
        exists None, x8, x9.
        split. easy.
        now rewrite H5, H6, H7.
      }
      {
        destruct s, t. psimpl.
        apply ExchRevokeFail. easy.
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
          exists m w' j, i <> j /\
            w = ACCEPTED i j v w' /\
            [[SAcceptd i j v w']] m s x).
      {
        begin_stable.
        admit.
      }
      {
        begin_commit.
        unfold CAcceptd in H9. psimpl.
        ddestruct H1. ddestruct H2.
        rewrite H9 in H3. ddestruct H3.
        rewrite H4 in x9. ddestruct x9.
        exists x6.
        split. constructor.
        split.
        {
          exists None, x5, x4.
          unfold CAcceptd.
          split. easy.
          now rewrite H5, H6, H7.
        }
        {
          destruct s, t. psimpl.
          apply ExchGetAccept. easy.
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
    {
      cbn. intros.
      rename v0 into w.
      destruct w.
      {
        destruct o.
        {
          apply lemRet. begin_return.
          congruence.
        }
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
            ddestruct H1. ddestruct H2. ddestruct H9.
            unfold CAcceptd in H10. psimpl.
            rewrite H1 in H3. ddestruct H3.
            rewrite H4 in x9. ddestruct x9.
            rename x5 into j. rename x4 into w.
            exists x6.
            split. constructor.
            split.
            {
              split.
              {
                exists None. left.
                cbn. unfold CCleared.
                now rewrite H5.
              }
              {
                unfold Returned.
                intros. psimpl.
                now rewrite H6, H7.
              }
            }
            {
              destruct s, t. psimpl.
              apply ExchFinishPass. easy.
              constructor; cbn.
              {
                econstructor.
                symmetry. exact x7.
                easy.
              }
              { intros. now rewrite H0. }
            }
          }
          {
            begin_commit. ddestruct H2.
            unfold CAcceptd in *. psimpl.
            rewrite H10 in H3. ddestruct H3.
            rewrite H4 in x7. ddestruct x7.
            easy.
          }
        }
        {
          intros. apply lemRet.
          unfold sub, subRelt, LiftSPrec, LiftSRelt.
          intros. psimpl. destruct v1. 2: easy.
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
        match w with
        | OFFERED j w =>
          PCalls x i = CallPoss (Exch v) /\
          PRets x i = RetIdle /\
          i <> j /\
          exists m,
            ([[SOffered j w]] m s x) \/
            (exists k u,
              i <> k /\ j <> k /\
              [[SAcceptd j k w u]] m s x)
        | _ =>
          Precs i s x /\
          Returned i (Exch v) None s (eq x)
        end).
    {
      begin_stable.
      admit.
    }
    {
      intros. begin_commit.
      ddestruct H1. ddestruct H2.
      destruct H5. cbn in H1.
      unfold CCleared, COffered, CAcceptd in H1.
      elim_disj; psimpl.
      2:{
        rewrite H2 in H3. ddestruct H3.
        rewrite H6 in x6. ddestruct x6.
        exists x3.
        split. constructor.
        split.
        {
          rewrite H8, H9.
          do 3 (split;[easy|idtac]).
          exists None. left.
          unfold COffered.
          apply H10 in H1. psimpl.
          2: congruence.
          now rewrite H1, H3, H7.
        }
        {
          destruct s, t. psimpl.
          apply ExchGetOfferPass. easy.
          constructor; cbn.
          {
            econstructor.
            symmetry. exact x4.
            easy.
          }
          { intros. now rewrite H0. }
        }
      }
      {
        rewrite H1 in H3. ddestruct H3.
        rewrite H6 in x6. ddestruct x6.
        exists (
          comRetPoss i
            (comInvPoss i
              x3
              (Exch v)
              (ExchDef {i => v} {}))
            (Exch v)
            (ExchDef {} {})
            None
        ).
        assert (
          VisPossSteps
            x3
            ([(i, CallEv (Exch v))] ++ [(i, RetEv (Exch v) None)])
            (comRetPoss i
              (comInvPoss i
                x3
                (Exch v)
                (ExchDef {i => v} {}))
              (Exch v)
              (ExchDef {} {})
              None)
        ).
        {
          apply retStep.
          apply callStep with (p:=[]).
          constructor.
          {
            rewrite H8, H9, H7, H2.
            repeat (easy || constructor).
          }
          {
            cbn. rewrite eqb_id, H9.
            repeat (easy || constructor).
          }
        }
        split.
        {
          eapply erase_vis.
          exact H3.
        }
        split.
        {
          split.
          { exists None. now left. }
          {
            unfold Returned. intros. psimpl.
            cbn. now rewrite eqb_id.
          }
        }
        {
          destruct s, t. psimpl.
          apply ExchGetOfferFail with (v:=v).
          { unfold not. intros. psimpl. easy. }
          { easy. }
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
        rewrite H5 in H3. ddestruct H3.
        rewrite H6 in x6. ddestruct x6.
        exists (
          comRetPoss i
            (comInvPoss i
              x3
              (Exch v)
              (ExchDef {i => v} {}))
            (Exch v)
            (ExchDef {} {})
            None
        ).
        assert (
          VisPossSteps
            x3
            ([(i, CallEv (Exch v))] ++ [(i, RetEv (Exch v) None)])
            (comRetPoss i
              (comInvPoss i
                x3
                (Exch v)
                (ExchDef {i => v} {}))
              (Exch v)
              (ExchDef {} {})
              None)
        ).
        {
          apply retStep.
          apply callStep with (p:=[]).
          constructor.
          {
            rewrite H8, H9, H7, H11.
            repeat (easy || constructor).
          }
          {
            cbn. rewrite eqb_id, H9.
            repeat (easy || constructor).
          }
        }
        split.
        {
          eapply erase_vis.
          exact H3.
        }
        split.
        {
          split.
          {
            exists None.
            right. right.
            exists x8, x9, x10, x11.
            split. easy. split. easy.
            cbn. unfold CAcceptd. cbn.
            rewrite eqb_nid; try easy.
            apply H10 in H1. psimpl.
            2: congruence.
            now rewrite H1, H14.
          }
          {
            unfold Returned. intros. psimpl.
            cbn. now rewrite eqb_id.
          }
        }
        {
          destruct s, t. psimpl.
          apply ExchGetOfferFail with (v:=v).
          { unfold not. intros. psimpl. easy. }
          { easy. }
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
  }
  {
    intros. cbn. destruct v0.
    {
      destruct o.
      {
        rename i0 into j.
        rename v0 into w.
        eapply lemIf with
          (PT:=fun _ _ => LiftSPrec (fun s x =>
            Precs i s x /\
            Returned i (Exch v) (Some w) s (eq x)))
          (PF:=fun _ _ => LiftSPrec (fun s x =>
            Precs i s x /\
            Returned i (Exch v) None s (eq x))).
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
            unfold COffered, CAcceptd in H6.
            elim_disj; psimpl.
            2:{
              rewrite H6 in H3. ddestruct H3.
              rewrite H7 in x7. ddestruct x7.
            }
            rewrite H1 in H3. ddestruct H3.
            rewrite H7 in x7. ddestruct x7.
            exists (
              comRetPoss j
                (comRetPoss i
                  (comInvPoss i
                    (comInvPoss j
                      x4
                      (Exch w)
                      (ExchDef {j => w} {}))
                    (Exch v)
                    (ExchDef {i => v, j => w} {}))
                  (Exch v)
                  (ExchDef {i => v} {j => w})
                  (Some w))
                (Exch w)
                (ExchDef {} {})
                (Some v)
            ).
            assert (
              VisPossSteps
                x4
                ([(j, CallEv (Exch w))] ++
                 [(i, CallEv (Exch v))] ++
                 [(i, RetEv (Exch v) (Some w))] ++
                 [(j, RetEv (Exch w) (Some v))])
                (comRetPoss j
                  (comRetPoss i
                    (comInvPoss i
                      (comInvPoss j
                        x4
                        (Exch w)
                        (ExchDef {j => w} {}))
                      (Exch v)
                      (ExchDef {i => v, j => w} {}))
                    (Exch v)
                    (ExchDef {i => v} {j => w})
                    (Some w))
                  (Exch w)
                  (ExchDef {} {})
                  (Some v))
            ).
            {
              repeat rewrite app_assoc.
              apply retStep. apply retStep.
              apply callStep. apply callStep with (p:=[]).
              constructor.
              {
                apply H11 in H5. psimpl.
                2: congruence.
                rewrite H3, H5, H8, H2.
                repeat (easy || constructor).
              }
              {
                cbn. rewrite eqb_nid; try easy.
                rewrite H9, H10.
                repeat (easy || constructor).
              }
              {
                cbn. rewrite eqb_id.
                rewrite H10.
                repeat (easy || constructor).
              }
              {
                cbn. rewrite eqb_id, eqb_nid; try easy.
                assert (H5' := H5).
                apply H11 in H5. psimpl. 2: congruence.
                rewrite H5.
                repeat (easy || constructor).
              }
            }
            split.
            {
              eapply erase_vis.
              exact H3.
            }
            split.
            {
              split.
              {
                exists None. right. right.
                exists j, i, w, v.
                do 2 (split;[easy|idtac]).
                cbn. unfold CAcceptd. cbn.
                now rewrite eqb_nid, eqb_id.
              }
              {
                unfold Returned. intros. psimpl.
                cbn. now rewrite eqb_id, eqb_nid.
              }
            }
            {
              destruct s, t. psimpl.
              apply ExchAcceptPass. easy.
              { easy. }
              {
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
          {
            begin_commit.
            ddestruct H1. ddestruct H2.
            unfold COffered, CAcceptd in H6.
            elim_disj; psimpl.
            {
              rewrite H2 in H3. ddestruct H3.
              rewrite H7 in x7. ddestruct x7.
              easy.
            }
            rewrite H12 in H3. ddestruct H3.
            rewrite H7 in x7. ddestruct x7.
            exists (
              comRetPoss i
                (comInvPoss i
                  x4
                  (Exch v)
                  (ExchDef {i => v} {}))
                (Exch v)
                (ExchDef {} {})
                None
            ).
            assert (
              VisPossSteps
                x4
                ([(i, CallEv (Exch v))] ++ [(i, RetEv (Exch v) None)])
                (comRetPoss i
                  (comInvPoss i
                    x4
                    (Exch v)
                    (ExchDef {i => v} {}))
                  (Exch v)
                  (ExchDef {} {})
                  None)
            ).
            {
              apply retStep.
              apply callStep with (p:=[]).
              constructor.
              {
                rewrite H8, H9, H10, H13.
                repeat (easy || constructor).
              }
              {
                cbn. rewrite eqb_id, H10.
                repeat (easy || constructor).
              }
            }
            split.
            {
              eapply erase_vis.
              exact H3.
            }
            split.
            {
              split.
              {
                exists None. right. right.
                cbn. unfold CAcceptd. cbn.
                exists j, x8, w, x9.
                split. easy. split. easy.
                rewrite eqb_nid; try easy.
                apply H11 in H5. psimpl.
                rewrite H5, H16. easy.
                congruence.
              }
              {
                unfold Returned. intros. psimpl.
                cbn. now rewrite eqb_id.
              }
            }
            {
              destruct s, t. psimpl.
              apply ExchAcceptFail; try easy.
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
        {
          apply lemRet. begin_return.
          exists t, (eq x). split.
          {
            intros. psimpl.
            exists x. easy.
          }
          { easy. }
        }
        {
          apply lemRet. begin_return.
          exists t, (eq x). split.
          {
            intros. psimpl.
            exists x. easy.
          }
          { easy. }
        }
      }
      {
        apply lemRet. begin_return.
        exists t, (eq x). split.
        {
          intros. psimpl.
          exists x. easy.
        }
        { easy. }
      }
    }
    {
      eapply lemRet.
      unfold sub, subRelt, LiftSPrec.
      intros. unfold Posts, LiftSRelt.
      psimpl. psplit.
      2:{
        split. 2: easy.
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
    (fun i _ m => LiftSPrec (Precs i))
    (exchImpl)
    (fun i _ m v' => LiftSRelt (Posts i v')  ->> PrecToRelt (Returned i m v'))
    (fun i => TReturn (exchImpl i) i).
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