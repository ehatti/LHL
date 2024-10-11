From LHL.Core Require Import
  ProgramRules
  LogicFacts
  SingConds
  Program
  ProgramFacts
  Traces
  Tensor
  Logic
  Specs
  VisPoss.

From LHL.Util Require Import
  TransUtil
  Tactics
  Util.

From LHL.Examples Require Import
  NameSpec
  ExchangerSpec
  ThreadLocal
  CASSpec.

From Coq Require Import
  Logic.Classical
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
  NameSig T |+| CASSig (Offer T A).

Definition VE T A : Spec T (E T A) :=
  tensorSpec nameSpec casSpec.

Definition F A := ExchSig A.

Definition VF T A : Spec T (F A) :=
  exchSpec.

(* Code *)

Definition exch {T A} (v : A) : Prog (E T A) (option A) :=
  i <- call Self;
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

Definition exchImpl {T A} : Impl (E T A) (F A) :=
  fun _ m => match m with
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

Variant Filler :=
| fill.

Notation casSt s := (RState (snd s)).

Definition CCleared {A T} m : SPrec T A :=
  fun s ρ =>
    casSt s = CASDef None m /\
    PState ρ = ExchDef {} {}.

Definition COffered {A T} m (i : Name T) (v : A) : SPrec T A :=
  fun s ρ =>
    casSt s = CASDef (OFFERED i v) m /\
    PState ρ = ExchDef {} {} /\
    PCalls ρ i = CallPoss (Exch v) /\
    PRets ρ i = RetIdle /\
    ~(exists R (m : _ R) v, fst s i = Cont m (Return v)).

Definition CAcceptd {A T} m (i j : Name T) (v w : A) : SPrec T A :=
  fun s ρ =>
    casSt s = CASDef (ACCEPTED i j v w) m /\
    PState ρ = ExchDef {} {} /\
    PCalls ρ i = CallDone (Exch v) /\
    PRets ρ i = RetPoss (Exch v) (Some w) /\
    (* Filler *)
    ~(exists R (m : _ R) v, fst s i = Cont m (Return v)).

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

Notation UnderStep s i e t := (PointStep UnderThreadStep s (i, Some e) t).

Notation TS := (MkTS (specL:=nameSpec) (specR:=casSpec)).

Variant ExchTran {T A} : Name T -> InterState (F A) (VE T A) -> Poss (VF T A) -> InterState (F A) (VE T A) -> Poss (VF T A) -> Prop :=
| ExchInvoke i v s x t y :
    TInvoke exchImpl i _ (Exch v) s (eq x) t (eq y) ->
    ExchTran i s x t y
| ExchReturn i v w s x t y :
    TReturn exchImpl i (Exch v) w s (eq x) t (eq y) ->
    ExchTran i s x t y
| ExchCall i ths tht a R (m : CASSig _ R) x ps qs ns :
    UnderStep ths i (CallEv (inr m)) tht ->
    ExchTran i
      (ths, TS ps ns (CASDef a None)) x
      (tht, TS qs ns (CASDef a (Pend i m))) x
| ExchOfferPass i ths tht v x ps qs ns :
    PCalls x i = CallPoss (Exch v) ->
    PRets x i = RetIdle ->
    ~ (exists R (m : F A R) v0, tht i = Cont m (Return v0)) ->
    UnderStep ths i (RetEv (inr (CAS EMPTY (OFFERED i v))) true) tht ->
    ExchTran i
      (ths, TS ps ns (CASDef EMPTY (Pend i (CAS EMPTY (OFFERED i v))))) x
      (tht, TS qs ns (CASDef (OFFERED i v) None)) x
| ExchRevokePass i ths tht v x y ps qs ns :
    VisPossSteps x [(i, CallEv (Exch v)); (i, RetEv (Exch v) None)] y ->
    UnderStep ths i (RetEv (inr (CAS (OFFERED i v) EMPTY)) true) tht ->
    ExchTran i
      (ths, TS ps ns (CASDef (OFFERED i v) (Pend i (CAS (OFFERED i v) EMPTY)))) x
      (tht, TS qs ns (CASDef EMPTY None)) y
| ExchRevokeFail i ths tht a v x ps qs ns :
    a <> OFFERED i v ->
    ~(exists R (m : _ R) v0, tht i = Cont m (Return v0)) ->
    UnderStep ths i (RetEv (inr (CAS (OFFERED i v) EMPTY)) false) tht ->
    ExchTran i
      (ths, TS ps ns (CASDef a (Pend i (CAS (OFFERED i v) EMPTY)))) x
      (tht, TS qs ns (CASDef a None)) x
| ExchGetAccept i j ths tht v w x ps qs ns :
    i <> j ->
    UnderStep ths i (RetEv (inr Get) (ACCEPTED i j v w)) tht ->
    ~(exists R (m : _ R) v0, tht i = Cont m (Return v0)) ->
    ExchTran i
      (ths, TS ps ns (CASDef (ACCEPTED i j v w) (Pend i Get))) x
      (tht, TS qs ns (CASDef (ACCEPTED i j v w) None)) x
| ExchFinishPass i j ths tht v w x ps qs ns :
    i <> j ->
    UnderStep ths i (RetEv (inr (CAS (ACCEPTED i j v w) EMPTY)) true) tht ->
    ExchTran i
      (ths, TS ps ns (CASDef (ACCEPTED i j v w) (Pend i (CAS (ACCEPTED i j v w) EMPTY)))) x
      (tht, TS qs ns (CASDef EMPTY None)) x
| ExchOfferFail i ths tht a v x ps qs ns :
    a <> EMPTY ->
    UnderStep ths i (RetEv (inr (CAS EMPTY (OFFERED i v))) false) tht ->
    ~ (exists R (m : F A R) v0, tht i = Cont m (Return v0)) ->
    ExchTran i
      (ths, TS ps ns (CASDef a (Pend i (CAS EMPTY (OFFERED i v))))) x
      (tht, TS qs ns (CASDef a None)) x
| ExchGetOfferPass i j ths tht w x ps qs ns :
    i <> j ->
    UnderStep ths i (RetEv (inr Get) (OFFERED j w)) tht ->
    ExchTran i
      (ths, TS ps ns (CASDef (OFFERED j w) (Pend i Get))) x
      (tht, TS qs ns (CASDef (OFFERED j w) None)) x
| ExchGetOfferFail i ths tht a v x y ps qs ns :
    ~(exists w, a = OFFERED i w) ->
    ~(exists j w, i <> j /\ a = OFFERED j w) ->
    VisPossSteps x [(i, CallEv (Exch v)); (i, RetEv (Exch v) None)] y ->
    UnderStep ths i (RetEv (inr Get) a) tht ->
    ~(exists j w w', a = ACCEPTED i j w w') ->
    Filler ->
    ExchTran i
      (ths, TS ps ns (CASDef a (Pend i Get))) x
      (tht, TS qs ns (CASDef a None)) y
| ExchAcceptPass i j ths tht v w x y ps qs ns :
    i <> j ->
    VisPossSteps x [(j, CallEv (Exch w)); (i, CallEv (Exch v)); (i, RetEv (Exch v) (Some w)); (j, RetEv (Exch w) (Some v))] y ->
    UnderStep ths i (RetEv (inr (CAS (OFFERED j w) (ACCEPTED j i w v))) true) tht ->
    ExchTran i
      (ths, TS ps ns (CASDef (OFFERED j w) (Pend i (CAS (OFFERED j w) (ACCEPTED j i w v))))) x
      (tht, TS qs ns (CASDef (ACCEPTED j i w v) None)) y
| ExchAcceptFail i j ths tht a v w x y ps qs ns :
    (* i <> j -> *) Filler ->
    ~(exists u, a = OFFERED i u) ->
    ~(exists j u u', a = ACCEPTED i j u u') ->
    a <> OFFERED j w ->
    VisPossSteps x [(i, CallEv (Exch v)); (i, RetEv (Exch v) None)] y ->
    UnderStep ths i (RetEv (inr (CAS (OFFERED j w) (ACCEPTED j i w v))) false) tht ->
    ExchTran i
      (ths, TS ps ns (CASDef a (Pend i (CAS (OFFERED j w) (ACCEPTED j i w v))))) x
      (tht, TS qs ns (CASDef a None)) y.

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
  TInvoke (VE:= VE T A) (VF:= VF T A) exchImpl i R m s (eq ρ) t (eq σ) ->
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
  TReturn (VE:= VE T A) (VF:= VF T A) exchImpl i m v s (eq ρ) t (eq σ) ->
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
  TInvoke (VE:= VE T A) (VF:= VF T A) exchImpl i R m s (eq ρ) t σs ->
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
  TReturn (VE:= VE T A) (VF:= VF T A) exchImpl i m v s (eq ρ) t σs ->
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
    casSt s = CASDef a m.
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
      (exists OR (om : _ OR) k,
        fst s i = Cont om (Bind (inr m) k) /\
        fst t i = UCall om (inr m) k) /\
      casSt s = CASDef a None /\
      casSt t = CASDef a (Pend i m) /\
      PState y = PState x /\
      PCalls y i = PCalls x i /\
      PRets y i = PRets x i /\
      (forall j, i <> j ->
        PCalls x j <> CallIdle ->
        ~(exists A (m : _ A) v, fst s j = Cont m (Return v)) ->
        PCalls y j = PCalls x j /\
        PRets y j = PRets x j /\
        fst t j = fst s j).

Ltac begin_stable :=
  unfold SStable, stableSPrec, ssub, subSPrec;
  unfold stableSRelt, subSRelt;
  unfold Stable, stablePrec, sub, subPrec;
  unfold stablePost, stableRelt, subRelt;
  unfold sub, subRelt;
  intros; psimpl.

Ltac begin_commit :=
  unfold Commit, SCommit, CallStep;
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
exists x. ddestruct H8.
{
  unfold TInvoke, InterOStep in H0.
  psimpl. ddestruct H9.
  cbn in *. ddestruct H1.
  apply sing_elem in H11. psimpl.
  split.
  {
    rewrite H3, <- H2, H7; try easy.
    repeat econstructor.
  }
  rewrite <- H9, <- H8, <- H6, <- H10, H15, H16; try easy.
  do 5 (split;[easy|idtac]).
  intros.
  assert (i0 <> j).
  {
    unfold not. intros. subst.
    unfold TIdle in H0. psimpl.
    specialize (H19 x6 eq_refl). psimpl.
    apply H12 in H. psimpl.
    2: congruence. 2: easy.
    rewrite <- H, H1 in H17. easy.
  }
  rewrite H15, H16, <- H2; try easy.
  now apply H12.
}
{
  unfold TReturn, InterOStep, mapRetPoss in H0.
  psimpl. ddestruct H9.
  cbn in *. ddestruct H1.
  apply sing_elem in H11. psimpl.
  split.
  {
    rewrite H3, <- H2, H7; try easy.
    repeat econstructor.
  }
  rewrite <- H10, <- H9, <- H8, <- H6, H16, H17; try easy.
  do 5 (split;[easy|idtac]). intros.
  assert (i0 <> j).
  {
    unfold not. intros. subst.
    apply H12 in H1. psimpl.
    2: congruence. 2: easy.
    apply H20. rewrite <- H22.
    now exists _, (Exch v), w.
  }
  rewrite H16, H17, <- H2; try easy.
  now apply H12.
}
{ easy. }
{ now ddestruct H6. }
{ now ddestruct H4. }
{ now ddestruct H5. }
{ now ddestruct H5. }
{ now ddestruct H4. }
{ now ddestruct H5. }
{ now ddestruct H4. }
{ now ddestruct H9. }
{ now ddestruct H5. }
{ now ddestruct H9. }
Qed.

Lemma lemGet {T A} {P : SPrec T A} {i : Name T} :
  forall (Q : option (Offer T A) -> SPrec T A),
  (forall v, SStable (Rely i) (Q v)) ->
  (forall v,
    SCommit i
      (Guar i)
      (P <<S CallStep i Get)
      (RetEv (inr Get) v)
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
  intros. do 2 psimpl. exists (eq x1).
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
    apply eq_inj in H9. subst.
    exists x. split. easy.
    ddestruct H3. ddestruct H1.
    unfold CallStep.
    exists a.
    repeat split; try easy.
    2: now rewrite H2.
    now exists _, om, k.
  }
  {
    intros.
    apply eq_inj in H9. subst.
    exists x. split. easy.
    destruct s, t. cbn in *.
    ddestruct H1.
    destruct s, t1. cbn in *.
    subst.
    apply ExchCall.
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
  exists x4.
  split.
  {
    rewrite H2, H10.
    repeat econstructor.
  }
  easy.
}
Qed.

Lemma lemCAS {T A} {P : SPrec T A} :
  forall (QT QF : SPrec T A) i e n,
  SStable (Rely i) QT ->
  SStable (Rely i) QF ->
  SCommit i
    (Guar i)
    (P <<S CallStep i (CAS e n))
    (RetEv (inr (CAS e n)) true)
    (fun _ _ => QT) ->
  SCommit i
    (Guar i)
    (P <<S CallStep i (CAS e n))
    (RetEv (inr (CAS e n)) false)
    (fun _ _ => QF) ->
  VerifyProg i
    (LiftSRelt (Rely i)) (LiftSRelt (Guar i))
    (fun _ _ => LiftSPrec P)
    (call (inr (CAS e n)))
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
  intros. do 2 psimpl. exists (eq x1).
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
    apply eq_inj in H11. subst.
    exists x. split. easy.
    ddestruct H5. ddestruct H3.
    exists a.
    repeat split; try easy.
    2: now rewrite H4.
    now exists _, om, k.
  }
  {
    intros.
    apply eq_inj in H11. subst.
    exists x. split. easy.
    destruct s, t, s, t1. cbn in *.
    ddestruct H3. subst.
    apply ExchCall.
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
Qed.

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

(* Rely lemmas *)

Lemma conj_assoc {A B C : Prop} :
  (A /\ B /\ C) = ((A /\ B) /\ C).
now apply propositional_extensionality.
Qed.

Ltac destruct_big_steps :=
repeat (match goal with
| [ H : VisPossSteps ?x ?p ?y |- _ ] =>
    ddestruct H
| [ H : VisPossStep ?x ?e ?y |- _ ] =>
    ddestruct H
| [ H : UnderStep ?s ?i ?e ?t |- _] =>
    ddestruct H
| [ H : UnderThreadStep ?s ?e ?t |- _ ] =>
    ddestruct H
end; cbn in *).


Ltac destruct_all_steps :=
repeat (match goal with
| [ H : VisPossSteps ?x ?p ?y |- _ ] =>
    ddestruct H
| [ H : VisPossStep ?x ?e ?y |- _ ] =>
    ddestruct H
| [ H : UnderStep ?s ?i ?e ?t |- _] =>
    ddestruct H
| [ H : UnderThreadStep ?s ?e ?t |- _ ] =>
    ddestruct H
| [ H : ExchStep ?x ?e ?y |- _ ] =>
    ddestruct H
end; cbn in *).

Lemma rw1 {A} {P : A -> Prop} :
    ~(exists x, P x) <-> forall x, ~P x.
unfold not. split; intros.
{ apply H. now exists x. }
{ psimpl. eapply H. exact H0. }
Qed.

Lemma rw2 {P Q : Prop} :
    ~(P /\ Q) <-> ~P \/ ~Q.
split; intros.
{
  decide_prop P.
  2: now left.
  decide_prop Q.
  2: now right.
  exfalso.
  now apply H.
}
{
  unfold not in *.
  intros. psimpl.
  destruct H;
  now apply H.
}
Qed.

Lemma rw3 {A} {x y : A} :
    ~(x <> y) <-> (x = y).
split; intros.
{ now apply NNPP. }
{ easy. }
Qed.

Section Rely_lemmas.

Variables (T : nat) (A : Type) (i : Name T).
Variables s t : InterState (F A) (VE T A).
Variables x y : Poss (VF T A).

Lemma Rely_pres_precs :
  Rely i s x t y ->
  Precs i s x ->
  Precs i t y.
intros. induction H. easy.
apply IHSRTC. clear IHSRTC H1.
unfold Precs, OtherTran in *. psimpl.
unfold CCleared, COffered, CAcceptd in *.
elim_disj; psimpl.
{
  ddestruct H1.
  {
    unfold TInvoke, InterOStep in H0.
    psimpl. ddestruct H3. psimpl.
    apply sing_elem in H5. psimpl.
    exists x0. left. now rewrite H7, <- H4.
  }
  {
    unfold TReturn, InterOStep in H0.
    psimpl. ddestruct H3. psimpl.
    apply sing_elem in H5. psimpl.
    unfold mapRetPoss in *. psimpl.
    exists x0. left. now rewrite H12, <- H4.
  }
  {
    ddestruct H1. ddestruct H0.
    exists (Pend i0 m). now left.
  }
  {
    ddestruct H1. ddestruct H0.
    exists None. right. left.
    now exists i0, v.
  }
  { ddestruct H2. }
  {
    cbn in *. ddestruct H3.
    exists None. now left.
  }
  { ddestruct H3. }
  { ddestruct H2. }
  { now ddestruct H3. }
  { ddestruct H2. }
  {
    cbn in *. ddestruct H6.
    destruct_big_steps.
    rewrite H20 in H2.
    destruct_all_steps.
    2: now apply disj_cons in x2.
    exists None. now left.
  }
  { ddestruct H3. }
  {
    cbn in *. ddestruct H6.
    destruct_big_steps.
    rewrite H20 in H4.
    destruct_all_steps.
    2: now apply disj_cons in x2.
    exists None. now left.
  }
}
{
  ddestruct H1.
  {
    unfold TInvoke, InterOStep in H0.
    psimpl. ddestruct H7. psimpl.
    apply sing_elem in H9. psimpl.
    exists x0. right. left.
    exists x1, x2.
    assert (x1 <> i0).
    {
      unfold not. intros. subst.
      unfold TIdle in H0. psimpl.
      specialize (H9 x3 eq_refl).
      psimpl. now rewrite H3 in H6.
    }
    now rewrite H11, <- H8, H14, H15, <- H2.
  }
  {
    unfold TReturn, InterOStep in H0.
    psimpl. ddestruct H7. psimpl.
    apply sing_elem in H9. psimpl.
    unfold mapRetPoss in *. psimpl.
    exists x0. right. left.
    exists x1, x2.
    assert (x1 <> i0).
    {
      unfold not. intros. subst.
      apply H10. ddestruct H1.
      now exists _, (Exch v), w.
    }
    now rewrite <- H8, H14, H15, H16, <- H2.
  }
  {
    cbn in *. ddestruct H2.
    exists (Pend i0 m). right. left.
    exists x1, x2. ddestruct H0.
    repeat split; try easy.
    cbn in *. dec_eq_nats i0 x1.
    {
      unfold not. intros.
      psimpl. ddestruct H0.
      rewrite H7 in x at 1.
      easy.
    }
    { now rewrite <- H1. }
  }
  { ddestruct H5. }
  {
    cbn in *. ddestruct H3.
    exists None. left.
    destruct_big_steps.
    rewrite H17 in H0.
    destruct_all_steps.
    2: now apply disj_cons in x4.
    easy.
  }
  {
    cbn in *. ddestruct H4.
    exists None. right. left.
    exists x1, x2.
    repeat split; try easy.
    dec_eq_nats i0 x1.
    { easy. }
    {
      ddestruct H2.
      now rewrite <- H3.
    }
  }
  { ddestruct H4. }
  { ddestruct H3. }
  {
    cbn in *. ddestruct H4.
    exists None. right. left.
    exists x1, x2.
    repeat split; try easy.
    dec_eq_nats i0 x1.
    { easy. }
    {
      do 2 ddestruct H1. cbn in *.
      now rewrite <- H2.
    }
  }
  {
    cbn in *. ddestruct H3.
    exists None. right. left.
    exists x1, x2.
    repeat split; try easy.
    ddestruct H1. cbn in *.
    now rewrite <- H2.
  }
  {
    cbn in *. ddestruct H7.
    exists None. right. left.
    assert (i0 = x1).
    {
      move H1 at bottom.
      rewrite rw1 in H1.
      specialize (H1 x1).
      rewrite rw1 in H1.
      specialize (H1 x2).
      rewrite rw2, rw3 in H1.
      now destruct H1.
    } subst.
    exfalso. apply H0.
    now exists x2.
  }
  {
    cbn in *. ddestruct H4.
    exists None. right. right.
    exists x1, i0, x2, v.
    destruct_big_steps.
    rewrite H32 in H1. ddestruct H1.
    2: now apply disj_cons in x4.
    rewrite <- x in H8. ddestruct H8.
    symmetry in x5. now apply disj_cons in x5.
    rewrite <- x in H15. ddestruct H15.
    2: now apply disj_cons in x12.
    rewrite <- x in H22. ddestruct H22.
    symmetry in x15. now apply disj_cons in x15.
    repeat split; try easy.
    now rewrite <- H30.
  }
  {
    cbn in *. ddestruct H7.
    exists None. right. left.
    exists x1, x2.
    destruct_big_steps.
    rewrite H21 in H4.
    destruct_all_steps.
    2: now apply disj_cons in x4.
    decide_prop (i0 = x1).
    {
      exfalso. apply H1. exists x2.
      repeat f_equal. easy.
    }
    rewrite H16, H17, H10, H9; try easy.
    repeat split; try easy.
    now rewrite <- H19.
  }
}
{
  ddestruct H1.
  {
    unfold TInvoke, InterOStep in H0.
    psimpl. ddestruct H8. cbn in *.
    apply sing_elem in H10. psimpl.
    exists x0. right. right.
    exists x1, x2, x3, x4.
    assert (i0 <> x1).
    {
      unfold not. intros. psimpl.
      unfold TIdle in H0. psimpl.
      specialize (H3 x5 eq_refl).
      rewrite H7 in H3. now psimpl.
    }
    now rewrite H15, H16, H12, <- H9, <- H2.
  }
  {
    unfold TReturn, InterOStep in H0.
    psimpl. ddestruct H8. cbn in *.
    apply sing_elem in H10. psimpl.
    exists x0. right. right.
    exists x1, x2, x3, x4.
    unfold mapRetPoss in H12. psimpl.
    assert (i0 <> x1).
    {
      unfold not. intros.
      subst. ddestruct H1.
      apply H11. now exists _, (Exch v), w.
    }
    now rewrite H15, H16, H17, <- H9, <- H2.
  }
  {
    cbn in *. ddestruct H3.
    exists (Pend i0 m). right. right.
    exists x1, x2, x3, x4.
    ddestruct H0. cbn in *.
    repeat split; try easy.
    dec_eq_nats i0 x1.
    {
      ddestruct H0. rewrite <- x.
      unfold not. intros. psimpl.
      ddestruct H0. 
    }
    { now rewrite <- H1. }
  }
  { ddestruct H6. }
  { ddestruct H4. }
  {
    cbn in *. ddestruct H5.
    exists None. right. right.
    exists x1, x2, x3, x4.
    repeat split; try easy.
    dec_eq_nats i0 x1.
    { easy. }
    {
      ddestruct H2. cbn in *.
      now rewrite <- H3.
    }
  }
  {
    cbn in *. ddestruct H5.
    exists None. right. right.
    exists x1, x2, x3, x4.
    easy.
  }
  {
    cbn in *. ddestruct H4.
    exists None. now left.
  }
  {
    cbn in *. ddestruct H5.
    exists None. right. right.
    exists x1, x2, x3, x4.
    repeat split; try easy.
    dec_eq_nats i0 x1.
    { easy. }
    {
      ddestruct H1. cbn in *.
      now rewrite <- H2.
    }
  }
  { ddestruct H4. }
  {
    cbn in *. ddestruct H8.
    rewrite rw1 in H4.
    specialize (H4 x2).
    rewrite rw1 in H4.
    specialize (H4 x3).
    rewrite rw1 in H4.
    specialize (H4 x4).
    assert (x1 <> i0) by congruence.
    exists None. right. right.
    exists x1, x2, x3, x4.
    destruct_big_steps.
    rewrite H22 in H2.
    destruct_all_steps.
    2: now apply disj_cons in x6.
    rewrite H15, H14, H8, H7, <- H17.
    all: easy.
  }
  { ddestruct H5. }
  {
    cbn in *. ddestruct H8.
    exists None. right. right.
    exists x1, x2, x3, x4.
    destruct_big_steps.
    rewrite H22 in H4. ddestruct H4.
    2: now apply disj_cons in x6.
    decide_prop (i0 = x1).
    {
      subst. exfalso.
      apply H2. repeat eexists.
    }
    rewrite H16, H17, H9, H10, <- H19; try easy.
    repeat split; try easy.
    rewrite <- x in H11.
    now ddestruct H11.
  }
}
Qed.

Lemma Rely_pres_self_ths :
  Rely i s x t y ->
  fst t i = fst s i.
intros.
induction H. easy.
rewrite IHSRTC. clear IHSRTC H0.
do 2 destruct H. ddestruct H0.
{
  unfold TInvoke, InterOStep in H0.
  psimpl. ddestruct H1. now rewrite H2.
}
{
  unfold TReturn, InterOStep in H0.
  psimpl. ddestruct H1. now rewrite H2.
}
{ ddestruct H0. now rewrite H1. }
{ ddestruct H3. now ddestruct H4. }
{ ddestruct H1. now rewrite H2. }
{ ddestruct H2. now rewrite H3. }
{ ddestruct H1. now rewrite H2. }
{ ddestruct H1. now rewrite H2. }
{ ddestruct H1. now rewrite H2. }
{ ddestruct H1. now rewrite H2. }
{ ddestruct H3. now rewrite H4. }
{ ddestruct H2. now rewrite H3. }
{ ddestruct H5. now rewrite H6. }
Qed.

Lemma Rely_trans_self_acceptd :
  Rely i s x t y ->
  forall j v w,
  i <> j ->
  (exists m, CAcceptd m i j v w s x) ->
  (exists m, CAcceptd m i j v w t y).
intros.
induction H. easy.
apply IHSRTC. clear - H H1.
unfold OtherTran, CAcceptd in *.
psimpl. ddestruct H5.
{
  unfold TInvoke, InterOStep in H0.
  psimpl. ddestruct H6. ddestruct H1.
  apply sing_elem in H8. psimpl.
  rewrite <- H2, H12, H13, <- H7, H8; try easy.
  now exists x2.
}
{
  unfold TReturn, InterOStep in H0.
  psimpl. ddestruct H6. ddestruct H1.
  apply sing_elem in H8.
  unfold mapRetPoss in H8. psimpl.
  rewrite <- H7, H15, H13, H14, <- H2; try easy.
  now exists x2.
}
{
  ddestruct H1. ddestruct H0.
  eexists. split. easy.
  now rewrite <- H1.
}
{ ddestruct H4. }
{
  ddestruct H1. ddestruct H1.
  exists None. split. easy.
  now rewrite <- H2.
}
{
  ddestruct H3. ddestruct H2.
  eexists. split. easy.
  now rewrite <- H3.
}
{
  ddestruct H1. ddestruct H4.
  eexists. split. easy.
  now rewrite <- H2.
}
{
  ddestruct H1. ddestruct H3.
  exists None. split. easy.
  now rewrite <- H2.
}
{
  ddestruct H1. ddestruct H4.
  exists None. split. easy.
  now rewrite <- H2.
}
{ ddestruct H1. ddestruct H3. }
{
  destruct_all_steps; ddestruct H20.
  2:{
    rewrite <- x in x5. ddestruct x5.
    apply insert_cong in x. destruct x.
    exfalso. eapply disj_cons.
    symmetry. exact H16.
  }
  eexists. split. easy.
  now rewrite H14, H15, H7, H8, <- H17.
}
{ ddestruct H3. }
{
  ddestruct H6. destruct_all_steps.
  2:{
    rewrite <- x in x5. ddestruct x5.
    apply insert_cong in x. destruct x.
    exfalso. eapply disj_cons.
    symmetry. exact H18.
  }
  eexists. split. easy.
  now rewrite H16, H17, H9, H10, <- H19.
}
Qed.

Lemma Rely_trans_self_offered :
  Rely i s x t y ->
  forall v,
  (exists m, COffered m i v s x) ->
  (exists m, COffered m i v t y) \/
  (exists m j w, i <> j /\ CAcceptd m i j v w t y).
intros H v.
cut (
  (exists m, COffered m i v s x) \/
  (exists m j w, i <> j /\ CAcceptd m i j v w s x) ->
  (exists m, COffered m i v t y) \/
  (exists m j w, i <> j /\ CAcceptd m i j v w t y)
).
{ intros. apply H0. now left. }
induction H. easy.
clear H0. do 2 destruct H.
intros. apply IHSRTC. clear IHSRTC.
ddestruct H0.
{
  unfold TInvoke, InterOStep in H0. psimpl.
  ddestruct H2. ddestruct H1. cbn in *.
  apply sing_elem in H4. psimpl.
  unfold COffered, CAcceptd in *.
  rewrite H8, H9, H4, <- H2.
  setoid_rewrite <- H3.
  all: easy.
}
{
  unfold TReturn, InterOStep in H0. psimpl.
  ddestruct H2. ddestruct H1. cbn in *.
  unfold mapRetPoss in H4.
  apply sing_elem in H4. psimpl.
  unfold COffered, CAcceptd in *.
  rewrite H9, H10, H11, <- H2.
  setoid_rewrite <- H3.
  all: easy.
}
{
  unfold COffered, CAcceptd in *.
  elim_disj; psimpl.
  {
    left.
    ddestruct H1. ddestruct H0.
    cbn in *. rewrite <- H1.
    exists (Pend i0 m). all: easy.
  }
  {
    right.
    ddestruct H0. ddestruct H3.
    cbn in *. rewrite <- H1.
    exists (Pend i0 m), x1, x2.
    all: easy.
  }
}
{
  unfold COffered, CAcceptd in *.
  elim_disj; psimpl.
  { ddestruct H4. }
  { ddestruct H5. }
}
{
  unfold COffered, CAcceptd in *.
  elim_disj; psimpl.
  { now ddestruct H2. }
  { ddestruct H3. }
}
{
  unfold COffered, CAcceptd in *.
  elim_disj; psimpl.
  {
    left.
    ddestruct H2. ddestruct H4.
    cbn in *. rewrite <- H3.
    exists None. all: easy.
  }
  {
    right.
    ddestruct H2. ddestruct H5.
    cbn in *. rewrite <- H3.
    exists None, x1, x2.
    all: easy.
  }
}
{
  unfold COffered, CAcceptd in *.
  elim_disj; psimpl.
  { ddestruct H3. }
  { now ddestruct H4. }
}
{
  unfold COffered, CAcceptd in *.
  elim_disj; psimpl.
  { ddestruct H2. }
  { now ddestruct H3. }
}
{
  unfold COffered, CAcceptd in *.
  elim_disj; psimpl.
  {
    left.
    ddestruct H1. ddestruct H4.
    cbn in *. rewrite <- H2.
    exists None. all: easy.
  }
  {
    right.
    ddestruct H1. ddestruct H5.
    cbn in *. rewrite <- H2.
    exists None, x1, x2.
    all: easy.
  }
}
{
  unfold COffered, CAcceptd in *.
  elim_disj; psimpl.
  {
    left.
    ddestruct H2. ddestruct H1.
    cbn in *. rewrite <- H2.
    exists None. all: easy.
  }
  { ddestruct H3. }
}
{
  unfold COffered, CAcceptd in *.
  elim_disj; psimpl.
  {
    left.
    ddestruct H6. destruct_big_steps.
    cbn in *. exists None.
    rewrite <- H17, H14, H15, H8, H7.
    all: try easy. repeat split; try easy.
    rewrite H20 in H2. destruct_all_steps.
    2:{ now apply disj_cons in x2. }
    easy.
  }
  {
    right.
    ddestruct H7. destruct_big_steps.
    cbn in *. exists None, x1, x2.
    rewrite H15, H14, H8, H7, <- H17.
    all: try easy. repeat split; try easy.
    rewrite H21 in H2. destruct_all_steps.
    2:{ now apply disj_cons in x4. }
    easy.
  }
}
{
  unfold COffered, CAcceptd in *.
  elim_disj; psimpl.
  {
    right.
    ddestruct H3. ddestruct H2.
    cbn in *. exists None, i0, v.
    destruct_big_steps. rewrite <- H30.
    repeat split; try easy. 2: easy.
    rewrite H31 in H1. ddestruct H1.
    2: now apply disj_cons in x2.
    rewrite <- x in H8. ddestruct H8.
    symmetry in x3. now apply disj_cons in x3.
    rewrite <- x in H15. ddestruct H15.
    2: now apply disj_cons in x10.
    rewrite <- x in H22. ddestruct H22.
    symmetry in x13. now apply disj_cons in x13.
    easy.
  }
  { ddestruct H4. }
}
{
  unfold COffered, CAcceptd in *.
  elim_disj; psimpl.
  {
    left.
    ddestruct H5. ddestruct H7.
    cbn in *. exists None.
    destruct_big_steps.
    rewrite H16, H17, H9, H10, <- H19.
    all: try easy.
    rewrite H20 in H4. ddestruct H4.
    2: now apply disj_cons in x2.
    rewrite <- x in H11. ddestruct H11.
    easy.
  }
  {
    right.
    ddestruct H5. ddestruct H8.
    cbn in *. exists None, x1, x2.
    destruct_big_steps.
    rewrite H16, H17, H9, H10, <- H19.
    all: try easy.
    rewrite H21 in H4. ddestruct H4.
    2: now apply disj_cons in x4.
    rewrite <- x in H11. ddestruct H11.
    easy.
  }
}
Qed.

End Rely_lemmas.

Section Rely_lemmas.

Variables (T : nat) (A : Type) (i : Name T).
Variables s t : InterState (F A) (VE T A).
Variables x y : Poss (VF T A).


Lemma Rely_pres_waiting_poss :
  Rely i s x t y ->
  ~((exists m v,
      casSt s = CASDef (OFFERED i v) m)) ->
  forall v,
  (PCalls x i = CallPoss (Exch v) /\ PRets x i = RetIdle) ->
  (PCalls y i = CallPoss (Exch v) /\ PRets y i = RetIdle).
intros. induction H. easy.
apply IHSRTC.
clear IHSRTC H2.
{
  clear H1. unfold not.
  intros. psimpl. apply H0.
  clear - H1 H.
  do 2 destruct H. ddestruct H0.
  {
    unfold TInvoke in H0.
    psimpl. rewrite H3.
    now exists x0, x1.
  }
  {
    unfold TReturn in H0.
    psimpl. rewrite H3.
    now exists x0, x1.
  }
  { cbn in *. ddestruct H1. repeat eexists. }
  { cbn in *. ddestruct H4. easy. }
  { cbn in *. ddestruct H2. }
  { cbn in *. ddestruct H3. repeat eexists. }
  { cbn in *. ddestruct H3. }
  { cbn in *. ddestruct H2. }
  { cbn in *. ddestruct H3. repeat eexists. }
  { cbn in *. ddestruct H2. repeat eexists. }
  { cbn in *. ddestruct H6. repeat eexists. }
  { cbn in *. ddestruct H3. }
  { cbn in *. ddestruct H6. repeat eexists. }
}
clear H2 IHSRTC.
do 2 destruct H. ddestruct H2.
{
  unfold TInvoke in H0. psimpl.
  apply sing_elem in H6. psimpl.
  now rewrite H10, H11.
}
{
  unfold TReturn in H0. psimpl.
  apply sing_elem in H6.
  unfold mapRetPoss in H6. psimpl.
  now rewrite H11, H12.
}
all: try easy.
{
  destruct_big_steps.
  now rewrite H12, H13, H5, H6.
}
{
  destruct_big_steps.
  now rewrite H14, H15, H7, H8.
}
{
  do 2 ddestruct H2. cbn in *.
  assert (i <> j).
  {
    unfold not. intro. subst.
    exfalso. apply H4.
    repeat eexists.
  }
  destruct_big_steps.
  now rewrite H28, H27, H21, H20, H14, H13, H7, H6.
}
{
  do 2 ddestruct H4. cbn in *.
  destruct_big_steps.
  now rewrite H16, H17, H9, H10.
}
Qed.

Lemma Invoke_pres_precs :
  forall v,
  TInvoke exchImpl i _ (Exch v) s (eq x) t (eq y) ->
  Precs i s x ->
  Precs i t y.
intros.
unfold TInvoke, InterOStep in H.
psimpl. ddestruct H1. ddestruct H0.
psimpl. apply sing_elem in H3. psimpl.
unfold Precs in *. psimpl.
unfold CCleared, COffered, CAcceptd in *.
psimpl. exists x0. elim_disj; psimpl;
setoid_rewrite <- H2;
setoid_rewrite H3.
{
  now left.
}
{
  right. left. exists x3, x4.
  now rewrite <- H1, H7, H8.
}
{
  right. right.
  exists x3, x4, x5, x6.
  now rewrite <- H1, H7, H8.
}
Qed.

End Rely_lemmas.

Section Rely_lemmas.

Variables (T : nat) (A : Type) (i : Name T).
Variables s t : InterState (F A) (VE T A).
Variables x y : Poss (VF T A).

Lemma Rely_pres_returned :
  Rely i s x t y ->
  forall v w,
  Returned i (Exch v) w s (eq x) ->
  Returned i (Exch v) w t (eq y).
unfold Returned. intros. psimpl.
assert (H' := H).
apply Rely_pres_self_ths in H'.
rewrite H' in H1 at 1.
eapply H0 in H1. 2: easy.
clear - H1 H. induction H. easy.
apply IHSRTC. clear IHSRTC H0.
do 2 destruct H. ddestruct H0.
{
  unfold TInvoke in H0. psimpl.
  apply sing_elem in H5. psimpl.
  now rewrite H9, H10.
}
{
  unfold TReturn in H0. psimpl.
  apply sing_elem in H5.
  unfold mapRetPoss in H5. psimpl.
  now rewrite H10, H11.
}
all: try easy.
{ destruct_big_steps. now rewrite H12, H13, H5, H6. }
{ destruct_big_steps. now rewrite H14, H15, H7, H8. }
{
  assert (i <> j).
  {
    unfold not. intros. subst.
    ddestruct H1. ddestruct H1.
    destruct H10. rewrite H2 in H11.
    ddestruct H11.
  }
  destruct_big_steps.
  now rewrite H27, H28, H20, H21, H14, H13, H7, H6.
}
{
  destruct_big_steps.
  now rewrite H16, H17, H9, H10.
}
Qed.

End Rely_lemmas.

Lemma exch_correct {T A} {i : Name T} :
  forall v,
  VerifyProg i (LiftSRelt (Rely (A:=A) i)) (LiftSRelt (Guar i))
    (prComp (LiftSPrec (Precs i)) (TInvoke exchImpl i _ (Exch v)) ->> LiftSRelt (Rely i))
    (exch v)
    (fun v' => LiftSRelt (Posts i) ->> PrecToRelt (Returned i (Exch v) v')).
unfold exch. intros.
eapply weakenPrec with
  (P:=fun _ _ => LiftSPrec (fun s x =>
    Precs i s x /\
    PCalls x i = CallPoss (Exch v) /\
    PRets x i = RetIdle /\
    fst s i = Cont (Exch v) (exch v))).
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
  repeat rewrite conj_assoc.
  assert (H1' := H1).
  unfold TInvoke, InterOStep in H1.
  psimpl. ddestruct H1. ddestruct H0.
  split.
  2:{
    apply Rely_pres_self_ths in H5.
    now rewrite H5 at 1.
  }
  rewrite <- conj_assoc.
  apply sing_elem in H4. psimpl.
  split.
  {
    eapply Rely_pres_precs. exact H5.
    eapply Invoke_pres_precs. exact H1'.
    easy.
  }
  {
    eapply Rely_pres_waiting_poss.
    exact H5. 2: easy.
    {
      unfold not. intros. psimpl.
      rewrite <- H3 in H0.
      unfold Precs in *. psimpl.
      unfold CCleared, COffered, CAcceptd in H2.
      elim_disj; psimpl.
      { rewrite H2 in H0. ddestruct H0. }
      { rewrite H10 in H0. ddestruct H0. easy. }
      { rewrite H11 in H0. ddestruct H0. }
    }
  }
}
unfold Precs.
eapply lemBind with
  (Q:=fun i' _ _ => LiftSPrec (fun s x =>
    Precs i s x /\
    PCalls x i = CallPoss (Exch v) /\
    PRets x i = RetIdle /\
    fst s i = Cont (Exch v)
      (my_offer_placed <- call (CAS EMPTY (OFFERED i v));
      if my_offer_placed : bool then
        no_change <- call (CAS (OFFERED i v) EMPTY);
        if no_change : bool then
          ret None
        else
          w <- call Get;
          match w with
          | ACCEPTED _ _ _ w' => call (CAS w EMPTY);; ret (Some w')
          | _ => ret None
          end
      else
        w <- call Get;
        match w with
        | OFFERED j w0 =>
          my_offer_accepted <-
            call (CAS (OFFERED j w0) (ACCEPTED j i w0 v));
          if my_offer_accepted : bool then
            ret (Some w0)
          else
            ret None
        | _ => ret None
        end) /\
    i = i')).
{
  eapply weakenPost.
  eapply (lemCall
    (Q:=fun _ _ => LiftSPrec (fun s x =>
      Precs i s x /\
      PCalls x i = CallPoss (Exch v) /\
      PRets x i = RetIdle /\
      fst s i = UCall (Exch v) (inl Self)
        (fun i => my_offer_placed <- call (CAS EMPTY (OFFERED i v));
        if my_offer_placed : bool then
          no_change <- call (CAS (OFFERED i v) EMPTY);
          if no_change : bool then
            ret None
          else
            w <- call Get;
            match w with
            | ACCEPTED _ _ _ w' => call (CAS w EMPTY);; ret (Some w')
            | _ => ret None
            end
        else
          w <- call Get;
          match w with
          | OFFERED j w0 =>
            my_offer_accepted <-
              call (CAS (OFFERED j w0) (ACCEPTED j i w0 v));
            if my_offer_accepted : bool then
              ret (Some w0)
            else
              ret None
          | _ => ret None
          end)))
    (S:=fun i' _ _ => LiftSPrec (fun s x =>
      Precs i s x /\
      PCalls x i = CallPoss (Exch v) /\
      PRets x i = RetIdle /\
      fst s i = Cont (Exch v)
        (my_offer_placed <- call (CAS EMPTY (OFFERED i v));
        if my_offer_placed : bool then
          no_change <- call (CAS (OFFERED i v) EMPTY);
          if no_change : bool then
            ret None
          else
            w <- call Get;
            match w with
            | ACCEPTED _ _ _ w' => call (CAS w EMPTY);; ret (Some w')
            | _ => ret None
            end
        else
          w <- call Get;
          match w with
          | OFFERED j w0 =>
            my_offer_accepted <-
              call (CAS (OFFERED j w0) (ACCEPTED j i w0 v));
            if my_offer_accepted : bool then
              ret (Some w0)
            else
              ret None
          | _ => ret None
          end) /\
      i = i'))).
  5:{
    unfold sub, subRelt.
    intros. now psimpl.
  }
  {
    unfold LiftSPrec, LiftSRelt.
    begin_stable.
    specialize (H0 x1 eq_refl). psimpl.
    exists x0. split. easy.
    split.
    {
      eapply Rely_pres_precs.
      exact H0. easy.
    }
    rewrite conj_assoc.
    split.
    {
      eapply Rely_pres_waiting_poss.
      exact H0.
      {
        unfold not. intros. psimpl.
        move H1 at bottom.
        destruct H1. cbn in *.
        unfold CCleared, COffered, CAcceptd in *.
        elim_disj; psimpl.
        { rewrite H in H1. ddestruct H1. }
        { rewrite H in H5. now ddestruct H5. }
        { rewrite H in H6. now ddestruct H6. }
      }
      easy.
    }
    {
      erewrite Rely_pres_self_ths.
      exact H4. exact H0.
    }
  }
  {
    unfold LiftSPrec, LiftSRelt.
    begin_stable.
    specialize (H0 x1 eq_refl). psimpl.
    exists x0. split. easy.
    split.
    {
      eapply Rely_pres_precs.
      exact H0. easy.
    }
    rewrite conj_assoc.
    split.
    {
      eapply Rely_pres_waiting_poss.
      exact H0.
      {
        unfold not. intros. psimpl.
        move H1 at bottom.
        destruct H1. cbn in *.
        unfold CCleared, COffered, CAcceptd in *.
        elim_disj; psimpl.
        { rewrite H in H1. ddestruct H1. }
        { rewrite H in H5. now ddestruct H5. }
        { rewrite H in H6. now ddestruct H6. }
      }
      easy.
    }
    split.
    {
      erewrite Rely_pres_self_ths.
      exact H4. exact H0.
    }
    easy.
  }
  {
    unfold LiftSPrec. begin_commit.
    destruct H2, H2, H7, H8.
    clear H2 H7 H8. psimpl.
    ddestruct H.
    exists (eq x1).
    split.
    { repeat econstructor. }
    split.
    {
      intros. subst.
      repeat econstructor.
    }
    split.
    {
      exists x1. split. easy.
      split.
      {
        exists x2. cbn.
        unfold CCleared, COffered, CAcceptd in *.
        elim_disj.
        { left. now rewrite <- H9 at 1. }
        {
          right. left. psimpl.
          exists x, x3.
          rewrite <- H9 at 1.
          repeat split; try easy.
          now setoid_rewrite H0.
        }
        {
          right. right. psimpl.
          exists x, x3, x4, x5.
          rewrite <- H9 at 1.
          repeat split; try easy.
          now setoid_rewrite H0.
        }
      }
      rewrite conj_assoc.
      split.
      { easy. }
      {
        ddestruct H1.
        rewrite H6 in x3.
        unfold exch in x3. ddestruct x3.
        rewrite frobProgId in x.
        cbn in x. ddestruct x.
        rewrite <- x3 at 1.
        f_equal. extensionality i'.
        rewrite frobProgId at 1. cbn.
        rewrite frobProgId with (p:= x <- call (CAS EMPTY (OFFERED _ _)); _).
        cbn. easy.
      }
    }
    {
      admit.
    }
  }
  {
    unfold LiftSPrec. begin_commit.
    destruct H2, H2, H3, H12.
    clear H2 H3 H12. psimpl.
    ddestruct H.
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
      exists x3. split. easy.
      split.
      {
        clear H8. destruct H4. cbn in *.
        exists x2. cbn.
        unfold CCleared, COffered, CAcceptd in *.
        elim_disj; psimpl.
        { left. now rewrite <- H13 at 1. }
        {
          right. left. psimpl.
          exists x6, x7.
          rewrite <- H13 at 1.
          repeat split; try easy.
          now setoid_rewrite H0.
        }
        {
          right. right. psimpl.
          exists x6, x7, x8, x9.
          rewrite <- H13 at 1.
          repeat split; try easy.
          now setoid_rewrite H0.
        }
      }
      rewrite conj_assoc.
      split.
      { easy. }
      {
        ddestruct H1.
        rewrite H7 in x6.
        ddestruct x6. rewrite <- x.
      }
    }
    {
      admit.
    }
  }
}
eapply lemIf with
  (PT:=fun _ _ => LiftSPrec (fun s x =>
    fst s i = Cont (Exch v)
     (no_change <- call (CAS (OFFERED i v) EMPTY);
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
        end) /\
    ((exists m, [[SOffered i v]] m s x) \/
     (exists m j w, i <> j /\
      [[SAcceptd i j v w]] m s x))))
  (PF:=fun _ _ => LiftSPrec (fun s x =>
    fst s i = Cont (Exch v)
     (w <- call Get;
      match w : option (Offer T A) with
      | OFFERED j w =>
          my_offer_accepted <- call (CAS (OFFERED j w) (ACCEPTED j i w v));
          if my_offer_accepted : bool then
            ret (Some w)
          else
            ret None
      | _ =>
          ret None
      end) /\
    PCalls x i = CallPoss (Exch v) /\
    PRets x i = RetIdle /\
    Precs i s x)).
clear i'.
{
  rewrite float_lift at 1.
  apply lemCAS.
  {
    begin_stable.
    split.
    {
      apply Rely_pres_self_ths in H0.
      now rewrite H0 at 1.
    }
    {
      clear H. elim_disj; psimpl.
      {
        eapply Rely_trans_self_offered.
        exact H0. now exists x1.
      }
      {
        eapply Rely_trans_self_acceptd in H0.
        2: exact H. 2:{ exists x1. exact H1. }
        right. psimpl. now exists x4, x2, x3.
      }
    }
  }
  {
    begin_stable.
    split.
    {
      apply Rely_pres_self_ths in H0.
      now rewrite H0 at 1.
    }
    {
      rewrite conj_assoc. 
      split.
      {
        eapply Rely_pres_waiting_poss.
        exact H0. 2: easy.
        {
          unfold not. intros. psimpl.
          unfold Precs in *. psimpl.
          unfold CCleared, COffered, CAcceptd in H3.
          elim_disj; psimpl.
          { rewrite H3 in H4. ddestruct H4. }
          { rewrite H5 in H4. ddestruct H4. easy. }
          { rewrite H6 in H4. ddestruct H4. }
        }
      }
      {
        eapply Rely_pres_precs.
        exact H0. easy.
      }
    }
  }
  {
    begin_commit.
    destruct H2, H14, H15, H16.
    rename H17 into ieq.
    clear H14 H15 H16.
    ddestruct H1. ddestruct H2.
    destruct H.
    elim_disj; psimpl;
    unfold CCleared, COffered, CAcceptd in *;
    psimpl.
    2:{
      rewrite H1 in H7. ddestruct H7.
      rewrite H8 in x9. ddestruct x9.
    }
    2:{
      rewrite H2 in H7. ddestruct H7.
      rewrite H8 in x9. ddestruct x9.
    }
    rewrite H6 in H3. ddestruct H3.
    rewrite frobProgId in x at 1.
    cbn in x. ddestruct x.
    rewrite H13 in x7. ddestruct x7.
    rewrite frobProgId in x8 at 1.
    cbn in x8.
    exists x6.
    split. constructor.
    split.
    {
      split.
      {
        rewrite frobProgId with (p:= x <- call _; if x : bool then _ else _).
        easy.
      }
      {
        left. exists None.
        rewrite H9, H10, H11.
        repeat split; try easy.
        unfold not. intros. psimpl.
        rewrite H2 in x8 at 1. ddestruct x8.
      }
    }
    {
      destruct s, t, s, t1. psimpl.
      rewrite H in H7. ddestruct H7.
      apply ExchOfferPass.
      { now rewrite H10. }
      { now rewrite H11. }
      {
        unfold not. intros. psimpl.
        rewrite H2 in x8. ddestruct x8.
      }
      constructor; cbn.
      {
        econstructor. exact H13.
        now rewrite frobProgId at 1.
      }
      { intros. now rewrite H0. }
    }
  }
  {
    begin_commit.
    destruct H2, H14, H15, H16.
    rename H17 into ieq.
    clear H14 H15 H16.
    intros. psimpl.
    ddestruct H1. ddestruct H2.
    destruct H.
    elim_disj; psimpl;
    unfold Precs; cbn;
    unfold CCleared, COffered, CAcceptd in *;
    psimpl.
    {
      rewrite H in H7. ddestruct H7.
      rewrite H8 in x9. ddestruct x9.
      easy.
    }
    {
      exists x6.
      rewrite H2 in H7. ddestruct H7.
      rewrite H8 in x9. ddestruct x9.
      split. constructor.
      split.
      rewrite H6 in H3. ddestruct H3.
      rewrite frobProgId in x at 1.
      cbn in x. ddestruct x.
      rewrite H13 in x7. ddestruct x7.
      rewrite frobProgId in x8 at 1.
      cbn in x8.
      {
        split.
        { rewrite frobProgId at 1. easy. }
        {
          rewrite H10, H11.
          repeat split; try easy.
          exists None. rewrite H9.
          right. left. exists x11, x12.
          move H at bottom. split. easy.
          assert (H' := H). apply H12 in H.
          all: try (easy || congruence).
          psimpl. rewrite H, H3.
          repeat split; try easy.
          unfold not. intros. psimpl.
          rewrite H0, H7 in H18. 2: easy.
          apply H17. now exists _, x3, x4.
        }
      }
      {
        destruct s, t, s, t1. psimpl.
        apply ExchOfferFail. easy.
        constructor; cbn.
        {
          econstructor.
          symmetry. exact x7.
          easy.
        }
        { intros. now rewrite H0. }
        {
          rewrite H6 in H3. ddestruct H3.
          rewrite frobProgId in x at 1.
          cbn in x. ddestruct x.
          rewrite H13 in x7. ddestruct x7.
          rewrite frobProgId in x8 at 1.
          cbn in x8.
          unfold not. intros. psimpl.
          rewrite <- x8 in H3. ddestruct H3.
        }
      }
    }
    {
      exists x6.
      rewrite H14 in H7. ddestruct H7.
      rewrite H8 in x9. ddestruct x9.
      split. constructor.
      split.
      {
        rewrite H6 in H3. ddestruct H3.
        rewrite frobProgId in x at 1.
        cbn in x. ddestruct x.
        rewrite H13 in x7. ddestruct x7.
        rewrite frobProgId in x8 at 1.
        cbn in x8.
        split.
        { now rewrite frobProgId at 1. }
        {
          rewrite H10, H11.
          split. easy. split. easy.
          exists None. right. right.
          move H at bottom.
          exists x11, x12, x13, x14.
          split. easy. split. easy.
          assert (H' := H). apply H12 in H.
          all: try (congruence || easy).
          psimpl. rewrite H, H3, H9.
          repeat split; try easy.
          unfold not. intros. psimpl.
          rewrite H0, H7 in H19. 2: easy.
          apply H18. now exists _, x3, x4.
        }
      }
      {
        destruct s, t, s, t1. psimpl.
        apply ExchOfferFail. easy.
        constructor; cbn.
        {
          econstructor.
          symmetry. exact x7.
          easy.
        }
        { intros. now rewrite H0. }
        {
          rewrite H6 in H3. ddestruct H3.
          rewrite frobProgId in x at 1.
          cbn in x. ddestruct x.
          rewrite H13 in x7. ddestruct x7.
          rewrite frobProgId in x8 at 1.
          cbn in x8.
          unfold not. intros. psimpl.
          rewrite H3 in x8. ddestruct x8.
        }
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
      fst s i = Cont (Exch v) (
        w <- call Get;
        match w : option (Offer T A) with
        | ACCEPTED _ _ _ w' =>
            call (CAS w EMPTY);;
            ret (Some w')
        | _ =>
            ret None (* impossible *)
        end
      ) /\
      exists m j w, i <> j /\
        [[SAcceptd i j v w]] m s x)).
  {
    erewrite float_lift at 1.
    apply lemCAS.
    {
      begin_stable.
      split.
      {
        eapply Rely_pres_precs.
        exact H0. easy.
      }
      {
        eapply Rely_pres_returned.
        exact H0. easy.
      }
    }
    {
      begin_stable.
      split.
      {
        apply Rely_pres_self_ths in H0.
        now rewrite H0 at 1.
      }
      {
        eapply Rely_trans_self_acceptd in H0.
        2: exact H1. 2:{ exists x1. exact H2. }
        psimpl. now exists x4, x2, x3.
      }
    }
    {
      begin_commit.
      destruct H2, H12, H13, H14.
      rename H15 into ieq.
      clear H12 H13 H14.
      ddestruct H1. ddestruct H2.
      unfold COffered, CAcceptd in H4.
      elim_disj; psimpl.
      {
        exists (
          comRetPoss i
            (comInvPoss i
              x6
              (Exch v)
              (ExchDef {i => v} {}))
            (Exch v)
            (ExchDef {} {})
            None
        ).
        assert (
          VisPossSteps
            x6
            ([(i, CallEv (Exch v))] ++ [(i, RetEv (Exch v) None)])
            (comRetPoss i
              (comInvPoss i
                x6
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
            rewrite H7, H8, H9, H2.
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
          exact H14.
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
          destruct s, t, s, t1.
          psimpl. ddestruct x9.
          apply ExchRevokePass.
          { easy. }
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
      {
        rewrite H2 in H5. ddestruct H5.
        rewrite H6 in x9. ddestruct x9.
      }
    }
    {
      begin_commit.
      destruct H2, H12, H13, H14.
      rename H15 into ieq.
      clear H12 H13 H14.
      ddestruct H1. ddestruct H2.
      unfold COffered, CAcceptd in H4.
      elim_disj; psimpl.
      {
        rewrite H2 in H5. ddestruct H5.
        rewrite H6 in x9. ddestruct x9.
        easy.
      }
      rewrite H4 in H5. ddestruct H5.
      rewrite H6 in x9. ddestruct x9.
      exists x6.
      rewrite H in H3. ddestruct H3.
      rewrite frobProgId in x at 1. psimpl.
      ddestruct x. rewrite H11 in x7.
      ddestruct x7. rewrite frobProgId in x8 at 1.
      cbn in x8.
      split.
      { constructor. }
      split.
      {
        cbn in *.
        split.
        { now rewrite frobProgId at 1. }
        {
          unfold CAcceptd.
          exists None, x11, x12.
          rewrite H7, H8, H9.
          repeat split; try easy.
          unfold not. intros. psimpl.
          rewrite H3 in x8 at 1. ddestruct x8.
        }
      }
      {
        destruct s, t, s, t1. psimpl.
        apply ExchRevokeFail. easy.
        {
          unfold not. intros. psimpl.
          rewrite H3 in x8. ddestruct x8.
        }
        {
          constructor; cbn.
          {
            econstructor. exact H11.
            now rewrite frobProgId at 1.
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
          fst s i = Cont (Exch v) (
            match w : option (Offer T A) with
            | ACCEPTED _ _ _ w' =>
                call (CAS w EMPTY);;
                ret (Some w')
            | _ =>
                ret None (* impossible *)
            end
          ) /\
          exists m w' j, i <> j /\
            w = ACCEPTED i j v w' /\
            [[SAcceptd i j v w']] m s x).
      {
        begin_stable.
        split.
        {
          apply Rely_pres_self_ths in H0.
          now rewrite H0 at 1.
        }
        {
          eapply Rely_trans_self_acceptd in H0.
          2: exact H1. 2:{ exists x1. exact H3. }
          psimpl. now exists x4, x2, x3.
        }
      }
      {
        begin_commit.
        destruct H2, H13, H14, H15.
        rename H16 into ieq.
        clear H13 H14 H15.
        unfold CAcceptd in H12. psimpl.
        ddestruct H1. ddestruct H2.
        rewrite H12 in H5. ddestruct H5.
        rewrite H6 in x12. ddestruct x12.
        rewrite H in H3. ddestruct H3.
        rewrite frobProgId in x at 1.
        cbn in x. ddestruct x.
        rewrite H11 in x10. ddestruct x10.
        rewrite frobProgId in x11 at 1. cbn in x11.
        exists x9.
        split. constructor.
        split.
        {
          split.
          { now rewrite frobProgId at 1. }
          {
            exists None, x8, x7.
            unfold CAcceptd.
            split. easy.
            rewrite H9, H8, H7.
            repeat split; try easy.
            unfold not. intros. psimpl.
            rewrite H1 in x11 at 1. ddestruct x11.
          }
        }
        {
          destruct s, t, s, t1. psimpl.
          apply ExchGetAccept. easy.
          constructor; cbn.
          {
            econstructor. exact H11.
            now rewrite frobProgId at 1.
          }
          { intros. now rewrite H0. }
          {
            unfold not. intros. psimpl.
            rewrite H1 in x11. ddestruct x11.
          }
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
            split.
            {
              eapply Rely_pres_precs.
              exact H0. easy.
            }
            {
              eapply Rely_pres_returned.
              exact H0. easy.
            }
          }
          {
            begin_stable.
            easy.
          }
          {
            begin_commit.
            destruct H2, H14, H15, H16.
            rename H17 into ieq.
            clear H14 H15 H16.
            ddestruct H1. ddestruct H2. ddestruct x12.
            unfold CAcceptd in H13. psimpl.
            rewrite H1 in H5. ddestruct H5.
            rewrite H6 in x. ddestruct x.
            rename x8 into j. rename x7 into w.
            rewrite H in H3 at 1. ddestruct H3.
            rewrite H11 in x10. ddestruct x10.
            exists x9.
            split. constructor.
            split.
            {
              split.
              {
                exists None. left.
                cbn. unfold CCleared.
                now rewrite H7.
              }
              {
                unfold Returned.
                intros. psimpl.
                now rewrite H8, H9.
              }
            }
            {
              destruct s, t, s, t1. psimpl.
              apply ExchFinishPass. easy.
              constructor; cbn.
              {
                econstructor.
                exact H11. easy.
              }
              { intros. now rewrite H0. }
            }
          }
          {
            begin_commit.
            destruct H2, H14, H15, H16.
            rename H17 into ieq.
            clear H14 H15 H16.
            ddestruct H2.
            unfold CAcceptd in *. psimpl.
            rewrite H13 in H5. ddestruct H5.
            rewrite H6 in x10. ddestruct x10.
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
        fst s i = Cont (Exch v) (
          match w : option (Offer T A) with
          | OFFERED j w =>
              my_offer_accepted <- call (CAS (OFFERED j w) (ACCEPTED j i w v));
              if my_offer_accepted : bool then
                ret (Some w)
              else
                ret None
          | _ =>
              ret None
          end
        ) /\
        Precs i s x /\
        match w with
        | OFFERED j w =>
          PCalls x i = CallPoss (Exch v) /\
          PRets x i = RetIdle
        | _ =>
          Returned i (Exch v) None s (eq x)
        end).
    {
      begin_stable.
      split.
      {
        apply Rely_pres_self_ths in H0.
        now rewrite H0 at 1.
      }
      split.
      {
        eapply Rely_pres_precs.
        exact H0. easy.
      }
      {
        remember v0.
        destruct o. destruct o.
        {
          eapply Rely_pres_waiting_poss.
          exact H0. 2: easy.
          unfold not. intros. psimpl.
          unfold Precs in H1. psimpl.
          unfold CCleared, COffered, CAcceptd in H1.
          elim_disj; psimpl.
          { rewrite H1 in H3. ddestruct H3. }
          { rewrite H5 in H3. now ddestruct H3. }
          { rewrite H6 in H3. ddestruct H3. }
        }
        {
          eapply Rely_pres_returned.
          exact H0. easy.
        }
        {
          eapply Rely_pres_returned.
          exact H0. easy.
        }
      }
    }
    {
      intros. begin_commit.
      destruct H2, H14, H15, H16.
      rename H17 into ieq.
      clear H14 H15 H16.
      ddestruct H1. ddestruct H2.
      destruct H6. cbn in H1.
      unfold CCleared, COffered, CAcceptd in H1.
      rewrite H in H3 at 1. ddestruct H3.
      rewrite frobProgId in x at 1. cbn in x.
      ddestruct x. rewrite H13 in x7. ddestruct x7.
      elim_disj; psimpl.
      2:{
        rewrite H2 in H7. ddestruct H7.
        rewrite H8 in x9. ddestruct x9.
        exists x6.
        split. constructor.
        split.
        {
          split.
          {
            rewrite frobProgId in x8 at 1.
            rewrite frobProgId at 1. easy.
          }
          {
            rewrite H10, H11.
            split. 2: easy.
            exists None. right. left.
            exists x, x4. cbn. unfold COffered.
            split. easy. split. easy.
            move H1 at bottom.
            assert (H1' := H1).
            apply H12 in H1. psimpl.
            2: congruence. 2: easy.
            rewrite H1, H7, H9.
            repeat split; try easy.
            rewrite H0, H16. easy.
            easy.
          }
        }
        {
          destruct s, t, s, t1. psimpl.
          apply ExchGetOfferPass. easy.
          constructor; cbn.
          {
            econstructor.
            exact H13. easy.
          }
          { intros. now rewrite H0. }
        }
      }
      {
        rewrite H1 in H7. ddestruct H7.
        rewrite H8 in x9. ddestruct x9.
        exists (
          comRetPoss i
            (comInvPoss i
              x6
              (Exch v)
              (ExchDef {i => v} {}))
            (Exch v)
            (ExchDef {} {})
            None
        ).
        assert (
          VisPossSteps
            x6
            ([(i, CallEv (Exch v))] ++ [(i, RetEv (Exch v) None)])
            (comRetPoss i
              (comInvPoss i
                x6
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
            rewrite H9, H10, H11, H2.
            repeat (easy || constructor).
          }
          {
            cbn. rewrite eqb_id, H11.
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
          { now rewrite frobProgId in x8 at 1. }
          split.
          { exists None. now left. }
          {
            unfold Returned. intros. psimpl.
            cbn. now rewrite eqb_id.
          }
        }
        {
          destruct s, t, s, t1. psimpl.
          apply ExchGetOfferFail with (v:=v).
          { unfold not. intros. psimpl. easy. }
          {
            unfold not. intros. psimpl. easy.
          }
          { easy. }
          {
            constructor; cbn.
            {
              econstructor.
              exact H13. easy.
            }
            { intros. now rewrite H0. }
          }
          {
            unfold not. intros. psimpl. easy.
          }
          {
            unfold not. intros. psimpl. easy.
          }
        }
      }
      {
        rewrite H3 in H7. ddestruct H7.
        rewrite H8 in x9. ddestruct x9.
        exists (
          comRetPoss i
            (comInvPoss i
              x6
              (Exch v)
              (ExchDef {i => v} {}))
            (Exch v)
            (ExchDef {} {})
            None
        ).
        assert (
          VisPossSteps
            x6
            ([(i, CallEv (Exch v))] ++ [(i, RetEv (Exch v) None)])
            (comRetPoss i
              (comInvPoss i
                x6
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
            rewrite H9, H10, H11, H6.
            repeat (easy || constructor).
          }
          {
            cbn. rewrite eqb_id, H11.
            repeat (easy || constructor).
          }
        }
        split.
        {
          eapply erase_vis.
          exact H7.
        }
        split.
        {
          split.
          { now rewrite frobProgId in x8 at 1. }
          split.
          {
            exists None. right. right.
            exists x, x4, x5, x7.
            cbn. unfold CAcceptd. cbn.
            split. easy. split. easy.
            move H1 at bottom.
            assert (H1' := H1).
            apply H12 in H1. psimpl.
            2: congruence. 2: easy.
            rewrite eqb_nid. 2: easy.
            now rewrite H1, H17, H0, H18.
          }
          {
            unfold Returned. intros. psimpl.
            cbn. now rewrite eqb_id.
          }
        }
        {
          destruct s, t, s, t1. psimpl.
          apply ExchGetOfferFail with (v:=v).
          { unfold not. intros. psimpl. easy. }
          {
            unfold not. intros. psimpl. easy.
          }
          { easy. }
          {
            constructor; cbn.
            {
              econstructor.
              exact H13. easy.
            }
            { intros. now rewrite H0. }
          }
          {
            unfold not. intros. psimpl.
            now ddestruct H8.
          }
          {
            constructor.
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
            split.
            {
              eapply Rely_pres_precs.
              exact H0. easy.
            }
            {
              eapply Rely_pres_returned.
              exact H0. easy.
            }
          }
          {
            begin_stable.
            split.
            {
              eapply Rely_pres_precs.
              exact H0. easy.
            }
            {
              eapply Rely_pres_returned.
              exact H0. easy.
            }
          }
          {
            begin_commit.
            destruct H2, H14, H15, H16.
            rename H17 into ieq.
            clear H14 H15 H16.
            ddestruct H1. ddestruct H2.
            unfold Precs in H4. psimpl.
            unfold CCleared, COffered, CAcceptd in H1.
            elim_disj; psimpl.
            {
              rewrite H1 in H7. ddestruct H7.
              rewrite H8 in x9. ddestruct x9.
            }
            2:{
              rewrite H4 in H7. ddestruct H7.
              rewrite H8 in x9. ddestruct x9.
            }
            {
              rewrite H2 in H7. ddestruct H7.
              rewrite H8 in x9. ddestruct x9.
              rename x11 into j.
              rename x12 into w.
              exists (
                comRetPoss j
                  (comRetPoss i
                    (comInvPoss i
                      (comInvPoss j
                        x6
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
                  x6
                  ([(j, CallEv (Exch w))] ++
                    [(i, CallEv (Exch v))] ++
                    [(i, RetEv (Exch v) (Some w))] ++
                    [(j, RetEv (Exch w) (Some v))])
                  (comRetPoss j
                    (comRetPoss i
                      (comInvPoss i
                        (comInvPoss j
                          x6
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
                  move H1 at bottom.
                  apply H12 in H1. psimpl.
                  2: congruence. 2: easy.
                  rewrite H1, H7, H9, H4.
                  repeat (easy || constructor).
                }
                {
                  cbn. rewrite eqb_nid; try easy.
                  rewrite H10, H11.
                  repeat (easy || constructor).
                }
                {
                  cbn. rewrite eqb_id.
                  rewrite H11.
                  repeat (easy || constructor).
                }
                {
                  cbn. rewrite eqb_id, eqb_nid; try easy.
                  move H1 at bottom. assert (H1' := H1).
                  apply H12 in H1. psimpl. 2: congruence. 2: easy.
                  rewrite H7.
                  repeat (easy || constructor).
                }
              }
              split.
              {
                eapply erase_vis.
                exact H7.
              }
              split.
              {
                split.
                {
                  exists None. right. right.
                  exists j, i, w, v.
                  do 2 (split;[easy|idtac]).
                  cbn. unfold CAcceptd. cbn.
                  rewrite eqb_nid, eqb_id.
                  repeat split; try easy.
                  assert (H1' := H1).
                  move H1 at bottom.
                  apply H12 in H1. psimpl.
                  2: congruence. 2: easy.
                  now rewrite H0, H18.
                  easy.
                }
                {
                  unfold Returned. intros. psimpl.
                  cbn. now rewrite eqb_id, eqb_nid.
                }
              }
              {
                destruct s, t, s, t1. psimpl.
                apply ExchAcceptPass. easy.
                { easy. }
                {
                  constructor; cbn.
                  {
                    econstructor. exact H13.
                    rewrite H in H3 at 1. ddestruct H3.
                    rewrite frobProgId in x at 1.
                    psimpl. ddestruct x.
                    rewrite H13 in x7. now ddestruct x7.
                  }
                  { intros. now rewrite H0. }
                }
              }
            }
          }
          {
            begin_commit.
            destruct H2, H14, H15, H16.
            rename H17 into ieq.
            clear H14 H15 H16.
            ddestruct H1. ddestruct H2.
            unfold Precs in H4. psimpl.
            unfold CCleared, COffered, CAcceptd in H2.
            elim_disj; psimpl.
            {
              rewrite H2 in H7. ddestruct H7.
              rewrite H8 in x9. ddestruct x9.
              exists (
                comRetPoss i
                  (comInvPoss i
                    x6
                    (Exch v)
                    (ExchDef {i => v} {}))
                  (Exch v)
                  (ExchDef {} {})
                  None
              ).
              assert (
                VisPossSteps
                  x6
                  ([(i, CallEv (Exch v))] ++ [(i, RetEv (Exch v) None)])
                  (comRetPoss i
                    (comInvPoss i
                      x6
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
                  rewrite H10, H11, H9, H4.
                  repeat (easy || constructor).
                }
                {
                  cbn. rewrite eqb_id, H11.
                  repeat (easy || constructor).
                }
              }
              split.
              {
                eapply erase_vis.
                exact H7.
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
                destruct s, t, s, t1. psimpl.
                apply ExchAcceptFail.
                constructor.
                {
                  unfold not. intros. psimpl. easy.
                }
                {
                  unfold not. intros. psimpl. easy.
                }
                {
                  unfold not. intros. psimpl. easy.
                }
                { easy. }
                constructor; cbn.
                {
                  econstructor. exact H13.
                  rewrite H in H3 at 1. ddestruct H3.
                  rewrite frobProgId in x at 1.
                  cbn in *. ddestruct x.
                  rewrite H13 in x7. now ddestruct x7.
                }
                { intros. now rewrite H0. }
              }
            }
            {
              rewrite H4 in H7. ddestruct H7.
              rewrite H8 in x9. ddestruct x9.
              exists (
                comRetPoss i
                  (comInvPoss i
                    x6
                    (Exch v)
                    (ExchDef {i => v} {}))
                  (Exch v)
                  (ExchDef {} {})
                  None
              ).
              assert (
                VisPossSteps
                  x6
                  ([(i, CallEv (Exch v))] ++ [(i, RetEv (Exch v) None)])
                  (comRetPoss i
                    (comInvPoss i
                      x6
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
                  rewrite H9, H10, H11, H14.
                  repeat (easy || constructor).
                }
                {
                  cbn. rewrite eqb_id, H11.
                  repeat (easy || constructor).
                }
              }
              split.
              {
                eapply erase_vis.
                exact H7.
              }
              split.
              {
                split.
                {
                  exists None. right. left.
                  cbn. unfold COffered. cbn.
                  exists x11, x12. split. easy.
                  assert (H2' := H2).
                  move H2 at bottom. apply H12 in H2.
                  2: congruence. 2: easy. psimpl.
                  rewrite eqb_nid; try easy.
                  rewrite H2, H18, H0, H19.
                  repeat split; try easy.
                  easy.
                }
                {
                  unfold Returned. intros. psimpl.
                  cbn. now rewrite eqb_id.
                }
              }
              {
                destruct s, t, s, t1. psimpl.
                apply ExchAcceptFail; try easy.
                {
                  unfold not. intros. psimpl.
                  now ddestruct H8.
                }
                {
                  unfold not. intros. psimpl.
                  now ddestruct H8.
                }
                constructor; cbn.
                {
                  econstructor. exact H13.
                  rewrite H in H3 at 1. ddestruct H3.
                  rewrite frobProgId in x at 1.
                  cbn in *. ddestruct x.
                  rewrite H13 in x7. now ddestruct x7.
                }
                { intros. now rewrite H0. }
              }
            }
            {
              rewrite H14 in H7. ddestruct H7.
              rewrite H8 in x9. ddestruct x9.
              exists (
                comRetPoss i
                  (comInvPoss i
                    x6
                    (Exch v)
                    (ExchDef {i => v} {}))
                  (Exch v)
                  (ExchDef {} {})
                  None
              ).
              assert (
                VisPossSteps
                  x6
                  ([(i, CallEv (Exch v))] ++ [(i, RetEv (Exch v) None)])
                  (comRetPoss i
                    (comInvPoss i
                      x6
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
                  rewrite H9, H10, H11, H15.
                  repeat (easy || constructor).
                }
                {
                  cbn. rewrite eqb_id, H11.
                  repeat (easy || constructor).
                }
              }
              split.
              {
                eapply erase_vis.
                exact H7.
              }
              split.
              {
                split.
                {
                  exists None. right. right.
                  cbn. unfold CAcceptd. cbn.
                  exists x11, x12, x13, x14.
                  split. easy. split. easy.
                  assert (H2' := H2).
                  move H2 at bottom. apply H12 in H2.
                  2: congruence. 2: easy. psimpl.
                  rewrite eqb_nid; try easy.
                  rewrite H2, H19, H0, H20.
                  repeat split; try easy.
                  easy.
                }
                {
                  unfold Returned. intros. psimpl.
                  cbn. now rewrite eqb_id.
                }
              }
              {
                destruct s, t, s, t1. psimpl.
                apply ExchAcceptFail; try easy.
                {
                  unfold not. intros. psimpl. ddestruct H8.
                }
                {
                  unfold not. intros. psimpl. now ddestruct H8.
                }
                constructor; cbn.
                {
                  econstructor. exact H13.
                  rewrite H in H3 at 1. ddestruct H3.
                  rewrite frobProgId in x at 1.
                  cbn in *. ddestruct x.
                  rewrite H13 in x7. now ddestruct x7.
                }
                { intros. now rewrite H0. }
              }
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