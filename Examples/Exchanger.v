From LHL.Core Require Import
  ProgramRules
  LogicFacts
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
  Program.Equality.

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

Definition Relt T A := Relt (VE T A) (VF T A).
Definition Prec T A := Prec (VE T A) (VF T A).
Definition Post T A := Post (VE T A) (VF T A).

Definition SPrec T A :=
  InterState (F A) (VE T A) -> Poss (VF T A) -> Prop.

Definition SPrecToPrec {T A} (P : SPrec T A) : Prec T A :=
  fun s ρs => exists ρ, ρs = eq ρ /\ P s ρ.

Definition CCleared {A T} : SPrec T A :=
  fun s ρ =>
    exists m,
      snd s = CASDef None m /\
      PState ρ = ExchDef {} {}.

Definition COffered {A T} (i : Name T) (v : A) : SPrec T A :=
  fun s ρ =>
    exists m,
      snd s = CASDef (OFFERED v) m /\
      PState ρ = ExchDef {i => v} {}.

Definition CAccepted {A T} (i j : Name T) (v w : A) : SPrec T A :=
  fun s ρ =>
    exists m,
      i <> j /\
      snd s = CASDef (ACCEPTED v) m /\
      PState ρ = ExchDef {j => w} {i => v}.

Definition Precs {A T} R (m : ExchSig A R) : Prec T A :=
  fun s ρs => exists ρ, ρs = eq ρ /\ (
    CCleared s ρ \/
    (exists i v, COffered i v s ρ) \/
    (exists i j v w, CAccepted i j v w s ρ)).

Definition Posts {A T} R (m : ExchSig A R) : Post T A R :=
  fun _ _ _ => Precs R m.

Definition Guar {T A} (i : Name T) : Relt T A :=
  fun s ρs t σs => forall ρ, ρs = eq ρ -> exists σ, σs = eq σ /\ (
    ( (* offer *)
      CCleared s ρ /\
      exists v, COffered i v t σ
    ) \/
    ( (* revoke *)
      exists v,
        COffered i v s ρ /\
        CCleared t σ
    ) \/
    ( (* finish *)
      exists j v w,
        CAccepted j i w v s ρ /\
        CCleared t σ
    ) \/
    ( (* accept *)
      exists j w,
        COffered j w s ρ /\
        exists v,
          CAccepted j i w v t σ
    ) \/
    (
      ρ = σ /\
      exists a m,
        snd s = CASDef a None /\
        snd t = CASDef a (Some m)
    )
  ).

Definition ManyInvokeReturn {T A} i : Relt T A :=
  RTC (fun s ρs t σs =>
    exists j, j <> i /\
      (InvokeAny (exchImpl A) j s ρs t σs \/
       ReturnAny (exchImpl A) j s ρs t σs)).

Definition Rely {T A} (i : Name T) : Relt T A :=
  RTC (fun s ρs t σs =>
    exists j, i <> j /\ (
      Guar j s ρs t σs \/
      InvokeAny (exchImpl A) j s ρs t σs \/
      ReturnAny (exchImpl A) j s ρs t σs)).

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

Lemma TReturn_pres_state {T A R} :
  forall (m : F A R) v i s ρ t σ,
  TReturn (VE:= VE T A) (VF:= VF T A) (exchImpl A) i m v s (eq ρ) t (eq σ) ->
  PState ρ = PState σ /\
  snd s = snd t.
unfold TReturn. intros. destruct_all.
assert (σ = retPoss i ρ).
{
  rewrite H2. exists ρ.
  specialize (H ρ eq_refl). destruct_all.
  unfold mapRetPoss. cbn. rewrite eqb_id.
  repeat split; (easy || apply differ_pointwise_trivial).
}
subst. easy.
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
  rewrite eqb_nid, H9; easy.
  extensionality j. dec_eq_nats i j.
  rewrite eqb_id. easy.
  rewrite eqb_nid, H10; easy.
}
{
  cbn. rewrite eqb_id. exists ρ.
  specialize (H ρ eq_refl).
  repeat split; (easy || apply differ_pointwise_trivial).
}
Qed.

Lemma Rely_pres_single {T A} :
  forall i s ρ t σs,
  Rely (T:=T) (A:=A) i s (eq ρ) t σs ->
  exists σ, σs = eq σ.
admit.
Admitted.

Lemma Rely_pres_self {T A} :
  forall i s ρ t σ,
  Rely (T:=T) (A:=A) i s (eq ρ) t (eq σ) ->
  PCalls ρ i = PCalls σ i /\
  PRets ρ i = PRets σ i.
admit.
Admitted.

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

Lemma CAS_atomic {T A} :
  forall i s ρ t σ a p,
  Rely (T:=T) (A:=A) i s (eq ρ) t (eq σ) ->
  snd s = CASDef a (Some p) ->
  snd s = snd t /\
  PState ρ = PState σ.
intros.
dependent induction H.
apply eq_inj in x. subst. easy.
destruct_all.
Admitted.

(* Subsidiary proofs *)

Lemma Precs_stable {T A} :
  forall (i : Name T) R (m : F A R),
  Stable (Rely i) (Precs R m).
unfold Stable, stablePrec, sub, subPrec.
intros. psimpl. induction H0. easy.
destruct_all. clear H1.
apply IHRTC. clear IHRTC.
elim_disj.
2:{
  unfold InvokeAny, TInvoke, TIdle in *. psimpl.
  unfold Precs in *. psimpl.
  exists (invPoss x x2 x1). split.
  {
    set_ext σ. split; intros; psimpl.
    {
      unfold invPoss. destruct x3, σ. cbn in *.
      f_equal. easy.
      extensionality j. dec_eq_nats x j.
      rewrite eqb_id. easy.
      rewrite eqb_nid, H9; easy.
      extensionality j. dec_eq_nats x j.
      rewrite eqb_id. easy.
      rewrite eqb_nid, H10; easy.
    }
    {
      exists x2. cbn. rewrite eqb_id.
      repeat split; (easy || apply differ_pointwise_trivial).
    }
  }
  {
    unfold CCleared, COffered, CAccepted in *.
    cbn in *. repeat rewrite <- H3. easy.
  }
}
2:{
  unfold ReturnAny, TReturn in *. psimpl.
  unfold Precs in *. psimpl.
  exists (retPoss x x3). split.
  {
    set_ext σ. split; intros; unfold mapRetPoss in *; psimpl.
    {
      unfold retPoss. destruct x4, σ. cbn in *.
      f_equal. easy.
      extensionality j. dec_eq_nats x j.
      rewrite eqb_id. easy.
      rewrite eqb_nid, H11; easy.
      extensionality j. dec_eq_nats x j.
      rewrite eqb_id. easy.
      rewrite eqb_nid, H12; easy.
    }
    {
      exists x3. cbn. rewrite eqb_id.
      specialize (H1 x3 eq_refl). destruct_all.
      repeat split; (easy || apply differ_pointwise_trivial).
    }
  }
  {
    unfold CCleared, COffered, CAccepted in *.
    cbn in *. repeat rewrite <- H3. easy.
  }
}
{
  unfold Precs, Guar in *. psimpl.
  specialize (H1 x0 eq_refl). psimpl.
  exists x1. split. easy.
  destruct H1; destruct_all.
  2: destruct H; destruct_all.
  3: destruct H; destruct_all.
  4: destruct H; destruct_all.
  right. left. exists x, x2. easy.
  left. easy.
  left. easy.
  {
    right. right.
    unfold CCleared, CAccepted, COffered in *. destruct_all.
    elim_disj; destruct_all.
    { rewrite H2 in H. discriminate. }
    2:{ rewrite H6 in H. discriminate. }
    {
      rewrite H2 in H. clear H2. ddestruct H.
      rewrite H6 in H5. clear H6. ddestruct H5.
      apply insert_cong in x. psimpl.
      ddestruct H. rewrite H3, H4. clear H3 H4.
      exists x2, x4, x3, x5, x8. easy.
    }
  }
  {
    subst.
    unfold CCleared, CAccepted, COffered in *. destruct_all.
    elim_disj; destruct_all.
    {
      left.
      rewrite H in H1 at 1. ddestruct H1.
      exists (Some x3). easy.
    }
    {
      right. left.
      rewrite H in H1 at 1. ddestruct H1.
      exists x0, x4, (Some x3). easy.
    }
    {
      right. right.
      rewrite H2 in H1 at 1. clear H2. ddestruct H1.
      exists x0, x4, x5, x6, (Some x3). easy.
    }
  }
}
Qed.

Definition PossSetSteps {T F} {VF : Spec T F} (ρs σs : PossSet VF) :=
  forall σ, σs σ ->
    exists ρ, ρs ρ /\
      PossSteps ρ σ.

Lemma lemCAS {T A} {i : Name T} :
  forall e n (P : Relt T A),
  forall (PS PF : PossSet (VF T A) -> PossSet (VF T A) -> Prop),
  (forall s ρs σs,
    ReltToPrec P s ρs ->
    snd s = CASDef e None ->
    σs = (fun σ =>
      exists ρ, ρs ρ /\
        σ.(PState) = ρ.(PState) /\
        σ.(PCalls) i = ρ.(PCalls) i /\
        σ.(PRets) i = ρ.(PRets) i) ->
    exists τs,
      PossSetSteps σs τs /\
      PS σs τs) ->
  (forall s ρs σs,
    ReltToPrec P s ρs ->
    (exists a,
      a <> e /\
      snd s = CASDef a None) ->
    σs = (fun σ =>
      exists ρ, ρs ρ /\
        σ.(PState) = ρ.(PState) /\
        σ.(PCalls) i = ρ.(PCalls) i /\
        σ.(PRets) i = ρ.(PRets) i) ->
    exists τs,
      PossSetSteps σs τs /\
      PF σs τs) ->
  (forall s ρs,
    ReltToPrec P s ρs ->
    exists a,
      snd s = CASDef a None) ->
  (forall s ρs t σs,
    snd s = CASDef e (Some (MkCASPend i (CAS e n))) ->
    snd t = CASDef n None ->
    PS ρs σs ->
    Guar i s ρs t σs) ->
  (forall a s ρs t σs,
    a <> e ->
    snd s = CASDef a (Some (MkCASPend i (CAS e n))) ->
    snd t = CASDef a None ->
    PF ρs σs ->
    Guar i s ρs t σs) ->
  VerifyProg i (Rely i) (Guar i)
    P
    (call (CAS e n))
    (fun v _ _ r τs =>
      exists (t : InterState (F A) (VE T A)) (ρs σs : PossSet (VF T A)),
        ((v = true /\
          snd t = CASDef n None /\
          PS ρs σs /\
          Rely i t σs r τs) \/
        (v = false /\
          (exists a,
            a <> e /\
            snd t = CASDef a None) /\
          PF ρs σs /\
          Rely i t σs r τs))).
intros.
eapply weakenPost.
eapply (lemCall
  (Q:=fun (s : InterState (F A) (VE T A)) ρs t σs =>
    σs = (fun σ =>
    exists ρ, ρs ρ /\
      σ.(PState) = ρ.(PState) /\
      σ.(PCalls) i = ρ.(PCalls) i /\
      σ.(PRets) i = ρ.(PRets) i) /\
    (exists a,
      snd s = CASDef a None /\
      snd t = CASDef a (Some (MkCASPend i (CAS e n)))))
  (S:=fun v s ρs r τs =>
    exists t σs,
    ((v = true /\
      PS ρs σs /\
      snd t = CASDef n None /\
      Rely i t σs r τs) \/
    (v = false /\
      PF ρs σs /\
      (exists a,
        a <> e /\
        snd t = CASDef a None) /\
      Rely i t σs r τs)))).
Admitted.

Lemma exch_correct {T A} {i : Name T} :
  forall v,
  VerifyProg i (Rely i) (Guar i)
    (prComp (Precs (option A) (Exch v)) (TInvoke (exchImpl A) i _ (Exch v)) ->> Rely i)
    (exch v)
    (fun v' => Posts _ (Exch v) v' ->> PrecToRelt (Returned i (Exch v))).
unfold exch. intros.
eapply lemBind.
{
  eapply lemCAS with
    (PS:=fun (ρs σs : PossSet (VF T A)) =>
      exists ρ, ρs = eq ρ /\ exists σ, σs = eq σ /\
      PState ρ = ExchDef {} {} /\
      (PState σ = ExchDef {i => v} {} \/
       exists j w,
        i <> j /\
        PState σ = ExchDef {j => w} {i => v})).
  {
    unfold Precs, CCleared, COffered, CAccepted.
    intros. psimpl. elim_disj; destruct_all.
    {
      admit.
    }
    {
      admit.
    }
    {
      admit.
    }
  }
  {
    admit.
  }
  {
    admit.
  }
  {
    admit.
  }
  {
    admit.
  }
}
intros. destruct v0.
{
  eapply lemBind.
  {
    eapply lemCAS with
      (PS:=fun s ρs => _)
      (PF:=fun s ρs => _).
    admit.
    admit.
    admit.
    admit.
    admit.
  }
  intros. destruct v0.
  {
    eapply lemRet.
    admit.
  }
  {
    eapply lemBind.
    {
      eapply lemCall.
      admit.
      admit.
      admit.
      admit.
    }
    intros. destruct v0.
    {
      destruct o.
      eapply lemBind.
      {
        eapply lemCAS.
        admit.
        admit.
        admit.
        admit.
        admit.
      }
      {
        intros.
        eapply lemRet.
        admit.
      }
    }
    {
      eapply lemRet.
      admit.
    }
  }
}
{
  eapply lemBind.
  {
    eapply lemCall.
    admit.
    admit.
    admit.
    admit.
  }
  {
    intros. destruct v0. destruct o.
    {
      eapply lemBind.
      {
        eapply lemCAS.
        admit.
        admit.
        admit.
        admit.
        admit.
      }
      {
        intros. destruct v0.
        {
          eapply lemRet.
          admit.
        }
        {
          eapply lemRet.
          admit.
        }
      }
    }
    {

    }
  }
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