From LHL.Core Require Import
  Program
  ProgramRules
  Specs
  Logic
  LogicFacts
  Tensor
  Traces
  Linearizability.

From LHL.Examples Require Import
  LockSpec
  FAISpec
  YieldSpec
  CounterSpec
  VarSpec.

From LHL.Util Require Import
  Tactics
  TransUtil
  Util.

From Coq Require Import
  Arith.PeanoNat
  Program.Equality
  Logic.FunctionalExtensionality
  Logic.PropExtensionality
  Logic.Classical_Prop.

Definition Underlay := FAISig |+| CounterSig |+| VarSig nat.

Definition acq : Prog Underlay unit :=
  my_tick <- call FAI;
  call (SetVar my_tick);;
  while (cur_tick <- call Get; ret (negb (cur_tick =? my_tick)))
    skip;;
  call ClrVar.

Definition rel : Prog Underlay unit :=
  call Inc.

Definition ticketLockImpl : Impl Underlay LockSig :=
  fun _ m => match m with
  | Acq => acq
  | Rel => rel
  end.

Definition E := Underlay.
Definition F := LockSig.
Definition VE := tensorSpec faiSpec (tensorSpec counterSpec (varSpec nat)).
Definition VF := lockSpec.

Definition Relt := Relt VE VF.
Definition Prec := Prec VE VF.
Definition Post := Post VE VF.

Definition countState (s : @InterState E F VE) : State counterSpec :=
  LState (RState (snd s)).
Definition varState (s : @InterState E F VE) : State (varSpec nat) :=
  RState (RState (snd s)).

Definition newtkt (s : @InterState E F VE) : nat :=
  fst (LState (snd s)).
Definition ctrval (s : @InterState E F VE) : nat :=
  match countState s with
  | CounterDef n _ => n
  | CounterUB => 0
  end.
Definition mytkt i (s : @InterState E F VE) : option nat :=
  match RState (RState (snd s)) i with
  | VarUnset => None
  | VarSet n _ => Some n
  end.

Definition Inv (i : ThreadName) : Prec :=
  fun s ρs => exists ρ, ρs = eq ρ /\
    countState s <> CounterUB /\
    (forall tkt,
      Some tkt = mytkt i s ->
      ctrval s <= tkt) /\
    ctrval s <= newtkt s /\
    (mytkt i s = Some (ctrval s) ->
      PState ρ = LockOwned i \/ PState ρ = LockUnowned) /\
    (newtkt s = ctrval s ->
      PState ρ = LockUnowned) /\
    (PState ρ = LockOwned i ->
      mytkt i s = Some (ctrval s)).

Definition Precs (i : ThreadName) {A} (m : LockSig A) : Prec :=
  fun s ρs => exists ρ, ρs = eq ρ /\
    match m with
    | Acq =>
        (PState ρ <> LockOwned i /\ PState ρ <> LockUB) ->
          Inv i s ρs
    | Rel =>
        PState ρ = LockOwned i ->
          Inv i s ρs
    end.

Definition Posts (i : ThreadName) {A} (m : LockSig A) : Post A :=
  fun _ s ρs t σs => forall ρ, ρs = eq ρ -> exists σ, σs = eq σ /\
    match m with
    | Acq =>
        (PState σ = LockOwned i /\
          PState ρ <> LockOwned i /\ PState ρ <> LockUB /\
          Inv i t σs) \/
        (PState σ = LockUB /\
          (PState ρ = LockOwned i \/ PState ρ = LockUB))
    | Rel =>
        (PState σ <> LockOwned i /\
          PState ρ = LockOwned i /\
          Inv i t σs) \/
        (PState σ = LockUB /\
          PState ρ <> LockOwned i)
    end.

Definition ManyInvokeReturn i : Relt :=
  RTC (fun s ρs t σs =>
    exists j, j <> i /\
      (InvokeAny ticketLockImpl j s ρs t σs \/
       ReturnAny ticketLockImpl j s ρs t σs)).

Definition Rely (i : ThreadName) : Relt :=
  fun s ρs t σs => forall ρ, ρs = eq ρ -> exists σ, σs = eq σ /\ (
    ManyInvokeReturn i s ρs t σs \/
    (countState s <> CounterUB ->
      countState t <> CounterUB) /\
    ((forall tkt, Some tkt = mytkt i s -> ctrval s <= tkt) ->
      forall tkt',
      Some tkt' = mytkt i t ->
      ctrval t <= tkt') /\
    (ctrval s <= newtkt s ->
      ctrval t <= newtkt t) /\
    ((mytkt i s = Some (ctrval s) -> PState ρ = LockOwned i \/ PState ρ = LockUnowned) ->
      mytkt i t = Some (ctrval t) ->
      PState σ = LockOwned i \/ PState σ = LockUnowned) /\
    ((newtkt s = ctrval s -> PState ρ = LockUnowned) ->
      newtkt t = ctrval t ->
      PState σ = LockUnowned) /\
    ((PState ρ = LockOwned i -> mytkt i s = Some (ctrval s)) ->
      PState σ = LockOwned i ->
      mytkt i t = Some (ctrval t)) /\
    (PState ρ = LockOwned i <-> PState σ = LockOwned i) /\
    (PState ρ = LockOwned i ->
      PState ρ = PState σ /\
      countState s = countState t) /\
    (PState ρ <> LockOwned i <-> PState σ <> LockOwned i) /\
    fst s i = fst t i /\
    (PState σ <> LockUB -> PState ρ <> LockUB) /\
    (PState σ = LockUB -> PState ρ <> LockOwned i ->
      PState ρ = LockUB) /\
    (PState ρ = LockUB ->
      PState σ = LockUB)
  ).

Definition Guar (i : ThreadName) : Relt :=
  fun s ρs t σs =>
    forall j, i <> j -> Rely j s ρs t σs.

Definition comInvPoss {F} {VF : Spec F} i (ρ : Poss VF) {A} (m : F A) (s : State VF) : Poss VF := {|
  PState := s;
  PCalls j := if i =? j then CallDone m else PCalls ρ j;
  PRets j := PRets ρ j
|}.


(* Tactics *)

Ltac decide_prop P :=
  let H := fresh in
  assert (H : P \/ ~P) by apply excluded_middle;
  destruct H.

Ltac set_ext x := extensionality x; apply propositional_extensionality.

(* Extra lemmas *)

Lemma not_and {P Q} :
  (~(P /\ Q)) = ~P \/ ~Q.
apply propositional_extensionality. split; intros.
decide_prop P. decide_prop Q.
exfalso. apply H. easy.
right. easy.
left. easy.
unfold not. intros. psimpl.
destruct H; contradiction.
Qed.

Lemma DNE {P} :
  (~~P) = P.
apply propositional_extensionality.
tauto.
Qed.

Lemma tollens {P Q : Prop} :
  ~Q -> (P -> Q) -> ~P.
tauto.
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

Lemma eq_inj_wk {A} :
  forall (x : A) (P : A -> Prop),
  eq x = P ->
  forall y, P y -> y = x.
intros. rewrite <- H in H0. easy.
Qed.

Lemma newtkt_eq :
  forall s t : @InterState E F VE,
  snd s = snd t ->
  newtkt s = newtkt t.
unfold newtkt. congruence.
Qed.

Lemma ctrval_eq :
  forall s t : @InterState E F VE,
  snd s = snd t ->
  ctrval s = ctrval t.
unfold ctrval, countState. intros.
rewrite H. easy.
Qed.

Lemma mytkt_eq i :
  forall s t : @InterState E F VE,
  snd s = snd t ->
  mytkt i s = mytkt i t.
unfold mytkt. intros.
rewrite H. easy.
Qed.

Lemma countState_eq :
  forall s t : @InterState E F VE,
  snd s = snd t ->
  countState s = countState t.
unfold countState. intros.
rewrite H. easy.
Qed.

Lemma cntSt_to_ctrval :
  forall s t : @InterState E F VE,
  countState s = countState t ->
  ctrval s = ctrval t.
unfold ctrval. intros.
rewrite H. easy.
Qed.

Lemma Invoke_pres_state {E F VE VF} {M : Impl E F} :
  forall A m i s ρ t σ,
  TInvoke (VE:=VE) (VF:=VF) M i A m s (eq ρ) t (eq σ) ->
  PState ρ = PState σ /\
  snd s = snd t /\
  differ_pointwise ρ.(PCalls) σ.(PCalls) i /\
  differ_pointwise ρ.(PRets) σ.(PRets) i.
unfold TInvoke, TIdle. intros. psimpl.
assert (σ = invPoss i ρ m).
rewrite H2. cbn. rewrite eqb_id.
exists ρ. repeat split; try (easy || apply differ_pointwise_trivial).
subst. cbn.
repeat split; (easy || apply differ_pointwise_trivial).
Qed.

Lemma Invoke_pres_Inv :
  forall A m i s ρ t σ,
  TInvoke (VE:=VE) (VF:=VF) ticketLockImpl i A m s (eq ρ) t (eq σ) ->
  Inv i s (eq ρ) -> Inv i t (eq σ).
intros. assert (H' := H). unfold TInvoke, TIdle in H. psimpl.
destruct H1. cbn in *.
assert (σ = invPoss i ρ m).
rewrite H3. cbn. rewrite eqb_id.
exists ρ. repeat split; try (easy || apply differ_pointwise_trivial).
subst. unfold Inv in *. psimpl.
apply eq_inj in H0. subst.
exists (invPoss i x m). split. easy.
apply Invoke_pres_state in H'. destruct_all.
cbn in *.
symmetry in H12.
repeat rewrite (countState_eq _ _ H12).
repeat rewrite (newtkt_eq _ _ H12).
repeat rewrite (mytkt_eq _ _ _ H12).
repeat rewrite (ctrval_eq _ _ H12).
easy.
Qed.

Lemma Invoke_pres_single {E F VE VF} {M : Impl E F} :
  forall A m i s ρ t σs,
  TInvoke (VE:=VE) (VF:=VF) M i A m s (eq ρ) t σs ->
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

Lemma noStateChange :
  forall i s ρs t σs,
  ManyInvokeReturn i s ρs t σs ->
  fst s i = fst t i /\
  snd s = snd t /\
  forall σ, σs σ ->
    exists ρ, ρs ρ /\
      PState ρ = PState σ.
intros.
induction H.
{
  split. easy.
  split. easy.
  intros. exists σ. easy.
}
{
  clear H0.
  destruct_all.
  destruct H3.
  {
    unfold InvokeAny, TInvoke, mapInvPoss in H3. psimpl.
    destruct H4. cbn in *.
    split. transitivity (fst t i). apply H6. easy. easy.
    split. transitivity (snd t); easy.
    intros. apply H2 in H7. clear H2. psimpl.
    exists x3. split. easy. congruence.
  }
  {
    unfold ReturnAny, TReturn, mapRetPoss in H3. psimpl.
    destruct H4. cbn in *.
    split. transitivity (fst t i). apply H6. easy. easy.
    split. transitivity (snd t); easy.
    intros. apply H2 in H9. psimpl.
    exists x5. split. easy. congruence.
  }
}
Qed.

Lemma Inv_stable :
  forall i, Stable (Rely i) (Inv i).
unfold Stable, stablePrec, sub, subPrec, Rely, Inv. intros.
psimpl.
specialize (H0 x1 eq_refl). destruct_all. subst.
exists x0. split. easy.
destruct H0.
{
  apply noStateChange in H. destruct_all.
  specialize (H7 x0 eq_refl). destruct_all. subst.
  rewrite <- H8. symmetry in H0.
  repeat rewrite (countState_eq _ _ H0).
  repeat rewrite (newtkt_eq _ _ H0).
  repeat rewrite (mytkt_eq _ _ _ H0).
  repeat rewrite (ctrval_eq _ _ H0).
  easy.
}
{
  destruct_all.
  repeat split; auto.
}
Qed.

Lemma Rely_pres_single :
  forall i s ρ t σs,
  Rely i s (eq ρ) t σs ->
  exists σ, σs = eq σ.
unfold Rely. intros.
specialize (H ρ eq_refl). psimpl.
exists x. easy.
Qed.

Lemma Rely_pres_not_owned :
  forall i s ρ t σ,
  Rely i s (eq ρ) t (eq σ) ->
  PState σ <> LockOwned i <->
  PState ρ <> LockOwned i.
unfold Rely. intros. specialize (H ρ eq_refl). psimpl.
apply eq_inj in H. subst.
destruct H0.
{
  apply noStateChange in H. psimpl.
  specialize (H1 x eq_refl). psimpl.
  rewrite H2. easy.
}
{
  psimpl. easy.
}
Qed.

Lemma Rely_pres_UB_backward :
  forall i s ρ t σ,
  Rely i s (eq ρ) t (eq σ) ->
  PState σ = LockUB ->
  PState ρ <> LockOwned i ->
  PState ρ = LockUB.
unfold Rely. intros.
specialize (H ρ eq_refl). psimpl.
apply eq_inj in H. subst.
destruct H2.
apply noStateChange in H. psimpl.
specialize (H3 x eq_refl). psimpl.
congruence.
psimpl.
apply H12; easy.
Qed.

Lemma Rely_pres_UB_forward :
  forall i s ρ t σ,
  Rely i s (eq ρ) t (eq σ) ->
  PState ρ = LockUB ->
  PState σ = LockUB.
unfold Rely. intros.
specialize (H ρ eq_refl). psimpl.
apply eq_inj in H. subst.
destruct H1.
apply noStateChange in H. psimpl.
specialize (H2 x eq_refl). psimpl.
congruence.
psimpl.
auto.
Qed.

Lemma Rely_pres_not_UB :
  forall i s ρ t σ,
  Rely i s (eq ρ) t (eq σ) ->
  PState σ <> LockUB ->
  PState ρ <> LockUB.
unfold Rely. intros. specialize (H ρ eq_refl). psimpl.
destruct H1.
{
  apply noStateChange in H1. psimpl. specialize (H3 σ eq_refl). psimpl.
  congruence.
}
{
  psimpl. apply eq_inj in H. subst.
  apply H11. easy.
}
Qed.

Lemma Rely_pres_owned :
  forall i s ρ t σ,
  Rely i s (eq ρ) t (eq σ) ->
  PState σ = LockOwned i <->
  PState ρ = LockOwned i.
unfold Rely. intros. specialize (H ρ eq_refl). psimpl.
apply eq_inj in H. subst.
destruct H0.
{
  apply noStateChange in H. psimpl.
  specialize (H1 x eq_refl). psimpl.
  rewrite H2. easy.
}
{
  psimpl. easy.
}
Qed.

Lemma mapPossInv_pres_single :
  forall i ρ σs A (m : F A),
  mapPoss (VF:=VF) (eq ρ) σs (mapInvPoss i m) ->
  exists σ, σs = eq σ.
unfold mapInvPoss. intros.
destruct H. specialize (H ρ eq_refl). destruct_all.
exists x. extensionality x1. apply propositional_extensionality.
split; intros.
{
  apply H0 in H8. clear H0. destruct_all. subst.
  destruct x, x0, x1. cbn in *.
  f_equal.
  { congruence. }
  {
    extensionality k.
    dec_eq_nats i k.
    congruence.
    etransitivity.
    apply H5. easy.
    symmetry. apply H12. easy.
  }
  {
    extensionality k.
    dec_eq_nats i k.
    congruence.
    etransitivity.
    apply H6. easy.
    symmetry. apply H13. easy.
  }
}
{
  subst. easy.
}
Qed.

Lemma mapPossRet_pres_single :
  forall i ρ σs A (m : F A) v,
  mapPoss (VF:=VF) (eq ρ) σs (mapRetPoss i m v) ->
  σs = eq (retPoss i ρ).
unfold mapRetPoss. intros. destruct H.
specialize (H ρ eq_refl). destruct_all.
extensionality x0. apply propositional_extensionality.
split; intros.
{
  apply H0 in H8. clear H0. psimpl.
  unfold retPoss. destruct x1, x0. psimpl.
  f_equal.
  extensionality j. dec_eq_nats i j.
  rewrite eqb_id. easy.
  rewrite eqb_nid. symmetry. apply H12; easy. easy.
  extensionality j. dec_eq_nats i j.
  rewrite eqb_id. easy.
  rewrite eqb_nid. symmetry. apply H13; easy. easy.
}
{
  subst. assert (H' := H).
  apply H0 in H'. clear H0. psimpl.
  assert (x = retPoss i x0).
  destruct x, x0. unfold retPoss. psimpl.
  f_equal.
  extensionality j. dec_eq_nats i j.
  rewrite eqb_id. easy.
  rewrite eqb_nid. apply H5. easy. easy.
  extensionality j. dec_eq_nats i j.
  rewrite eqb_id. easy.
  rewrite eqb_nid. apply H6. easy. easy.
  subst. easy.
}
Qed.

(* Program logic obligations *)

Lemma Rely_refl :
  forall i s ρ, Rely i s ρ s ρ.
unfold Rely. intros. subst.
exists ρ0. split. easy.
left. constructor.
Qed.

Lemma Rely_trans :
  forall i, Rely i ->> Rely i ==> Rely i.
unfold sub, subRelt. intros. pdestruct H.
unfold Rely in H. unfold Rely. intros. subst.
specialize (H ρ0 eq_refl). destruct_all. subst.
specialize (H0 x1 eq_refl). destruct_all. subst.
exists x0. split. easy.
destruct H0, H1.
{
  left. eapply rtcTrans. repeat eexists.
  exact H0. easy.
}
{
  right.
  apply noStateChange in H. destruct_all.
  move H13 at bottom. symmetry in H13.
  specialize (H14 x0 eq_refl). destruct_all. subst.
  symmetry in H15. move H15 at bottom.
  repeat rewrite (countState_eq _ _ H13) in *.
  repeat rewrite (ctrval_eq _ _ H13) in *.
  repeat rewrite (mytkt_eq _ _ _ H13) in *.
  repeat rewrite (newtkt_eq _ _ H13) in *.
  repeat rewrite H15 in *.
  rewrite H9.
  easy.
}
{
  right.
  apply noStateChange in H0. destruct_all.
  specialize (H2 x1 eq_refl). destruct_all. subst.
  (* symmetry in H1. move H1 at bottom. *)
  repeat rewrite (countState_eq _ _ H1) in *.
  repeat rewrite (ctrval_eq _ _ H1) in *.
  repeat rewrite (mytkt_eq _ _ _ H1) in *.
  repeat rewrite (newtkt_eq _ _ H1) in *.
  repeat rewrite H15 in *.
  rewrite H0.
  easy.
}
{
  right. destruct_all.
  split. auto.
  split. auto.
  split. auto.
  split. auto.
  split. auto.
  split. auto.
  split. rewrite H6. easy.
  split.
  {
    intros. assert (H25' := H25). apply H7 in H25. psimpl.
    rewrite H25' in H25. symmetry in H25. assert (H25'' := H25).
    apply H19 in H25. psimpl.
    rewrite H25', <- H25, H26. easy.
  }
  split. rewrite H8. easy.
  split. rewrite H9. easy.
  split. auto.
  split.
  {
    intros. apply H11. apply H23.
    easy. apply H8. easy.
    easy.
  }
  auto.
}
Qed.

Lemma Guar_in_Rely :
  forall i j : ThreadName, i <> j -> Guar i ==> Rely j.
unfold Guar, sub, subRelt. intros. destruct_all.
apply H0. easy.
Qed.

Lemma Inv_in_Rely :
  forall i j : ThreadName, i <> j -> InvokeAny ticketLockImpl i ==> Rely j.
unfold InvokeAny, TInvoke, Rely, sub, subRelt, TIdle. intros.
destruct_all. subst. destruct H2. cbn in *.
specialize (H5 ρ0 eq_refl). destruct_all.
exists (invPoss i ρ0 x0). split.
{
  extensionality σ. apply propositional_extensionality.
  split; intros; psimpl.
  destruct x1, σ. unfold invPoss. cbn in *.
  f_equal. easy.
  extensionality j0. dec_eq_nats i j0.
  rewrite eqb_id. easy.
  rewrite eqb_nid, H10; easy.
  extensionality j0. dec_eq_nats i j0.
  rewrite eqb_id. easy.
  rewrite eqb_nid, H11; easy.
  exists ρ0. cbn. rewrite eqb_id.
  repeat split; (easy || apply differ_pointwise_trivial).
}
{
  cbn.
  repeat rewrite (mytkt_eq _ _ _ H3).
  repeat rewrite (countState_eq _ _ H3).
  repeat rewrite (newtkt_eq _ _ H3).
  repeat rewrite (ctrval_eq _ _ H3).
  right. rewrite H2. 2: easy.
  easy.
}
Qed.

Lemma Ret_in_Rely :
  forall i j : ThreadName, i <> j -> ReturnAny ticketLockImpl i ==> Rely j.
unfold ReturnAny, TReturn, Rely, sub, subRelt, TIdle. intros.
destruct_all. subst. cbn in *.
exists (retPoss i ρ0). split.
{
  extensionality σ. apply propositional_extensionality.
  unfold mapRetPoss.
  split; intros; psimpl.
  {
    destruct x3, σ. unfold retPoss. cbn in *.
    f_equal. easy.
    extensionality j0. dec_eq_nats i j0.
    rewrite eqb_id. easy.
    rewrite eqb_nid, H10; easy.
    extensionality j0. dec_eq_nats i j0.
    rewrite eqb_id. easy.
    rewrite eqb_nid, H11; easy.
  }
  {
    exists x2. cbn. rewrite eqb_id.
    repeat split; (easy || apply differ_pointwise_trivial).
  }
}
{
  cbn. subst.
  repeat rewrite (mytkt_eq _ _ _ H3).
  repeat rewrite (countState_eq _ _ H3).
  repeat rewrite (newtkt_eq _ _ H3).
  repeat rewrite (ctrval_eq _ _ H3).
  right. repeat split; try easy.
  destruct H2. cbn in H1. rewrite H1; easy.
}
Qed.

Lemma init_in_Precs :
  forall i A (m : LockSig A), Precs i m (allIdle, Init VE) (eq initPoss).
unfold Precs. intros.
exists initPoss. split. easy.
destruct m.
simpl. intros.
exists initPoss. easy.
simpl. intros.
exists initPoss. easy.
Qed.

Lemma Precs_stable :
  forall i A (m : LockSig A), Stable (Rely i) (Precs i m).
unfold Stable, stablePrec, sub, subPrec, Precs. intros. psimpl.
assert (exists τ, ρ = eq τ).
eapply Rely_pres_single. exact H0. psimpl.
exists x0. split. easy.
destruct m.
{
  intros. psimpl.
  apply Inv_stable. psplit. 2: exact H0.
  apply H1.
  eapply (Rely_pres_not_owned _ _ _ _ _ H0) in H.
  eapply (Rely_pres_not_UB _ _ _ _ _ H0) in H2.
  easy.
}
{
  intros.
  apply Inv_stable. psplit. 2: exact H0.
  apply H1.
  eapply (Rely_pres_owned _ _ _ _ _ H0) in H. easy.
}
Qed.

Lemma Posts_stable :
  forall i A (m : LockSig A) v, Stable (Rely i) (Posts i m v).
unfold Stable, stablePost, stableRelt, sub, subRelt, Posts. destruct m.
intros. psimpl.
{
  specialize (H ρ0 eq_refl). psimpl.
  assert (exists τ, σ = eq τ).
  eapply Rely_pres_single. exact H1. psimpl.
  exists x0. split. easy.
  destruct H0; psimpl.
  {
    left. repeat split.
    eapply Rely_pres_owned. exact H1. easy.
    easy.
    easy.
    apply Inv_stable. psplit.
    exact H3. easy.
  }
  {
    right. split.
    eapply Rely_pres_UB_forward. exact H1.
    easy.
    easy.
  }
}
intros. psimpl.
{
  specialize (H ρ0 eq_refl). psimpl.
  assert (exists τ, σ = eq τ).
  eapply Rely_pres_single. exact H1. psimpl.
  exists x0. split. easy.
  destruct H0; psimpl.
  {
    left. repeat split.
    eapply Rely_pres_not_owned. exact H1. easy.
    easy.
    apply Inv_stable. psplit.
    exact H2. easy.
  }
  {
    right. split.
    eapply Rely_pres_UB_forward. exact H1. easy.
    easy.
  }
}
Qed.

Lemma ticketLockImpl_switch_code :
  forall i A (m1 : LockSig A) B (m2 : LockSig B) v,
  prComp (Precs i m1) (Posts i m1 v) <<- PrecToRelt (Returned i m1) <<-
  TReturn ticketLockImpl i m1 ==>
  Precs i m2.
unfold sub, subPrec, Precs, Posts. intros. destruct m1, m2.
{
  psimpl. specialize (H2 x5 eq_refl). psimpl.
  unfold TReturn, InterOStep in H0. psimpl. destruct x0.
  dependent destruction H0. cbn in *. dependent destruction H.
  symmetry in x1. unfold Returned in H1. apply H1 in x1.
  2: repeat econstructor. psimpl. clear H1.
  exists (retPoss i x1). split.
  {
    unfold mapRetPoss.
    extensionality σ. apply propositional_extensionality.
    split; intros; psimpl.
    {
      destruct x2, σ. unfold retPoss. cbn in *.
      f_equal; try easy.
      extensionality j. dec_eq_nats i j.
      rewrite eqb_id. easy.
      rewrite eqb_nid, H10; easy.
      extensionality j. dec_eq_nats i j.
      rewrite eqb_id. easy.
      rewrite eqb_nid, H11; easy.
    }
    {
      exists x1. cbn. rewrite eqb_id.
      repeat split; (easy || apply differ_pointwise_trivial).
    }
  }
  {
    cbn. intros. destruct H2; psimpl; contradiction.
  }
}
{
  psimpl. specialize (H2 x5 eq_refl). psimpl.
  unfold TReturn, InterOStep in H0. psimpl. destruct x0.
  dependent destruction H0. cbn in *. dependent destruction H.
  symmetry in x1. unfold Returned in H1. apply H1 in x1.
  2: repeat econstructor. psimpl. clear H1.
  exists (retPoss i x1). split.
  {
    unfold mapRetPoss.
    extensionality σ. apply propositional_extensionality.
    split; intros; psimpl.
    {
      destruct x2, σ. unfold retPoss. cbn in *.
      f_equal; try easy.
      extensionality j. dec_eq_nats i j.
      rewrite eqb_id. easy.
      rewrite eqb_nid, H10; easy.
      extensionality j. dec_eq_nats i j.
      rewrite eqb_id. easy.
      rewrite eqb_nid, H11; easy.
    }
    {
      exists x1. cbn. rewrite eqb_id.
      repeat split; (easy || apply differ_pointwise_trivial).
    }
  }
  {
    cbn. intros. destruct H2; destruct_all.
    2: { rewrite H in H1. discriminate. }
    clear H3. unfold Inv in *. psimpl.
    apply eq_inj in H3. subst.
    exists (retPoss i x2). split.
    unfold mapRetPoss.
    extensionality σ. apply propositional_extensionality.
    split; intros; psimpl.
    {
      destruct x1, σ. unfold retPoss. cbn in *.
      f_equal; try easy.
      extensionality j. dec_eq_nats i j.
      rewrite eqb_id. easy.
      rewrite eqb_nid, H17; easy.
      extensionality j. dec_eq_nats i j.
      rewrite eqb_id. easy.
      rewrite eqb_nid, H18; easy.
    }
    {
      exists x2. cbn. rewrite eqb_id.
      repeat split; (easy || apply differ_pointwise_trivial).
    }
    repeat rewrite (countState_eq _ _ H4) in *.
    repeat rewrite (newtkt_eq _ _ H4) in *.
    repeat rewrite (mytkt_eq _ _ _ H4) in *.
    repeat rewrite (ctrval_eq _ _ H4) in *.
    easy.
  }
}
{
  psimpl. specialize (H2 x5 eq_refl). psimpl.
  unfold TReturn, InterOStep in H0. psimpl. destruct x0.
  dependent destruction H0. cbn in *. dependent destruction H.
  symmetry in x1. unfold Returned in H1. apply H1 in x1.
  2: repeat econstructor. psimpl. clear H1.
  exists (retPoss i x1). split.
  {
    unfold mapRetPoss.
    extensionality σ. apply propositional_extensionality.
    split; intros; psimpl.
    {
      destruct x2, σ. unfold retPoss. cbn in *.
      f_equal; try easy.
      extensionality j. dec_eq_nats i j.
      rewrite eqb_id. easy.
      rewrite eqb_nid, H10; easy.
      extensionality j. dec_eq_nats i j.
      rewrite eqb_id. easy.
      rewrite eqb_nid, H11; easy.
    }
    {
      exists x1. cbn. rewrite eqb_id.
      repeat split; (easy || apply differ_pointwise_trivial).
    }
  }
  {
    cbn. intros. destruct H2; destruct_all.
    2: congruence.
    clear H3. unfold Inv in *. psimpl.
    apply eq_inj in H3. subst.
    exists (retPoss i x2). split.
    unfold mapRetPoss.
    extensionality σ. apply propositional_extensionality.
    split; intros; psimpl.
    {
      destruct x1, σ. unfold retPoss. cbn in *.
      f_equal; try easy.
      extensionality j. dec_eq_nats i j.
      rewrite eqb_id. easy.
      rewrite eqb_nid, H17; easy.
      extensionality j. dec_eq_nats i j.
      rewrite eqb_id. easy.
      rewrite eqb_nid, H18; easy.
    }
    {
      exists x2. cbn. rewrite eqb_id.
      repeat split; (easy || apply differ_pointwise_trivial).
    }
    repeat rewrite (countState_eq _ _ H4) in *.
    repeat rewrite (newtkt_eq _ _ H4) in *.
    repeat rewrite (mytkt_eq _ _ _ H4) in *.
    repeat rewrite (ctrval_eq _ _ H4) in *.
    easy.
  }
}
{
  psimpl. specialize (H2 x5 eq_refl). psimpl.
  unfold TReturn, InterOStep in H0. psimpl. destruct x0.
  dependent destruction H0. cbn in *. dependent destruction H.
  symmetry in x1. unfold Returned in H1. apply H1 in x1.
  2: repeat econstructor. psimpl. clear H1.
  exists (retPoss i x1). split.
  {
    unfold mapRetPoss.
    extensionality σ. apply propositional_extensionality.
    split; intros; psimpl.
    {
      destruct x2, σ. unfold retPoss. cbn in *.
      f_equal; try easy.
      extensionality j. dec_eq_nats i j.
      rewrite eqb_id. easy.
      rewrite eqb_nid, H10; easy.
      extensionality j. dec_eq_nats i j.
      rewrite eqb_id. easy.
      rewrite eqb_nid, H11; easy.
    }
    {
      exists x1. cbn. rewrite eqb_id.
      repeat split; (easy || apply differ_pointwise_trivial).
    }
  }
  {
    cbn. intros. destruct H2; destruct_all.
    congruence.
    rewrite H in H1. discriminate.
  }
}
Qed.

Lemma acq_correct i :
  VerifyProg i (Rely i) (Guar i) (prComp (Precs i Acq) (TInvoke ticketLockImpl i unit Acq) ->> Rely i) acq (fun v => Posts i Acq v ->> PrecToRelt (Returned i Acq)).
Admitted.

Lemma rel_correct i :
  VerifyProg i (Rely i) (Guar i) (prComp (Precs i Rel) (TInvoke ticketLockImpl i unit Rel) ->> Rely i) rel (fun v => Posts i Rel v ->> PrecToRelt (Returned i Rel)).
unfold rel. unfold Precs.
eapply weakenPrec with
  (P:=fun s ρs t σs =>
    exists ρ σ : Poss VF, ρs = eq ρ /\ σs = eq σ /\
      σ.(PCalls) i = CallPoss Rel /\
      σ.(PRets) i = RetIdle /\
      PState ρ = PState σ /\
      (PState σ = LockOwned i /\ Inv i t σs \/
       PState σ <> LockOwned i)).
2:{
  unfold sub, subRelt. intros. psimpl.
  decide_prop (PState x1 = LockOwned i).
  {

  }
  {

  }
}
eapply weakenPost.
eapply (lemCall
  (Q:=fun s ρs t σs =>
    exists ρ σ : Poss VF, ρs = eq ρ /\ σs = eq σ /\
      σ.(PCalls) i = CallDone Rel /\
      σ.(PRets) i = RetIdle /\
      (PState ρ = LockOwned i /\ PState σ = LockRelRan i /\ Inv i t σs \/
       PState ρ <> LockOwned i /\ PState σ = LockUB))
  (S:=fun _ s ρs t σs =>
    exists ρ σ : Poss VF, ρs = eq ρ /\ σs = eq σ /\
      σ.(PCalls) i = CallDone Rel /\
      σ.(PRets) i = RetPoss Rel tt /\
      (PState ρ = LockRelRan i /\ PState σ = LockUnowned /\ Inv i t σs \/
       PState ρ = LockUB /\ PState σ = LockUB))).
{
  admit.
}
{
  admit.
}
{
  eapply weakenCommitPre with
    (P:=fun _ _ t σs =>
      (exists σ : Poss VF, σs = eq σ /\
        σ.(PCalls) i = CallPoss Rel /\
        σ.(PRets) i = RetIdle /\
        PState σ = LockOwned i /\ Inv i t σs) \/
      (exists σ : Poss VF, σs = eq σ /\
        σ.(PCalls) i = CallPoss Rel /\
        σ.(PRets) i = RetIdle /\
        PState σ <> LockOwned i)).
  {
    unfold sub, subRelt. intros. psimpl.
    destruct H4; destruct_all.
    left. exists x0. easy.
    right. exists x0. easy.
  }
  apply disjCommit; unfold Commit; intros; psimpl.
  {
    destruct_all.
  }
  {
    exists (eq (comInvPoss i x1 Rel LockUB)).
    split. repeat econstructor.
    split.
    {
      intros. subst. exists x1. split. easy.
      econstructor.
      {
        eapply PCommitCall with (i:=i) (m:=Rel) (σ:= comInvPoss i x1 Rel LockUB). cbn.
        constructor. easy.
        cbn. rewrite eqb_id. easy.
        easy. easy.
      }
      intros. cbn. rewrite eqb_nid; easy.
      intros. cbn. easy.
      constructor.
    }
    split.
    {
      do 2 eexists.
      split. easy.
      split. easy.
      cbn. rewrite eqb_id.
      repeat split; try easy.
      right. easy.
    }
    {
      admit.
    }
  }
}
{

}
{
  unfold sub, subRelt, Posts, Returned. intros. psimpl.
  psplit.
  2:{
    split. 2: easy.
    intros. psimpl.
    exists x0. destruct v0. easy.
  }
  intros. subst.
  exists x4. split. easy.
  apply eq_inj in H, H0, H1. subst.
  destruct H5; destruct_all.
  {
    left. split. rewrite H0. easy.
    split. 2: easy.
    rewrite H13. destruct H9; destruct_all.
    easy.
    rewrite H5 in H. discriminate.
  }
  {
    right. split. easy.
    rewrite H13. destruct H9; destruct_all.
    rewrite H2 in H. discriminate.
    easy.
  }
}

Theorem ticketLockCorrect :
  VerifyImpl VE VF Rely Guar Precs ticketLockImpl Posts.
constructor.
apply Rely_refl.
apply Rely_trans.
apply Guar_in_Rely.
apply Inv_in_Rely.
apply Ret_in_Rely.
apply init_in_Precs.
apply Precs_stable.
apply Posts_stable.
apply ticketLockImpl_switch_code.
intros. destruct m; cbn.
apply acq_correct.
