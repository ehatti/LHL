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

Definition Precs {A T} R (m : ExchSig A R) : Prec T A :=
  fun s ρs => _.

Definition Posts {A T} R (m : ExchSig A R) : Post T A R :=
  fun _ _ _ => Precs R m.

Definition Guar {T A} (i : Name T) : Relt T A :=
  fun s ρs t σs => _.

Definition Rely {T A} (i : Name T) : Relt T A :=
  RTC (fun s ρs t σs =>
    exists j, i <> j /\ (
      Guar j s ρs t σs \/
      InvokeAny (exchImpl A) j s ρs t σs \/
      ReturnAny (exchImpl A) j s ρs t σs)).

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


(* Subsidiary proofs *)

Lemma Precs_stable {T A} :
  forall (i : Name T) R (m : F A R),
  Stable (Rely i) (Precs R m).
Qed.

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