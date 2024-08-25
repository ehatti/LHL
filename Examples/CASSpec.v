From LHL.Core Require Import
  Program
  Specs
  Logic
  LogicFacts
  Traces
  ProgramRules.

From LHL.Util Require Import
  Util.

Variant CASSig {A} : ESig :=
| CAS (v : option A) (v' : option A) : CASSig bool
| Get : CASSig (option A).
Arguments CASSig : clear implicits.

Record CASPend {T A} := MkCASPend {
  CASThread : Name T;
  CASRetTy : Type;
  CASName : CASSig A CASRetTy
}.
Arguments CASPend : clear implicits.
Arguments MkCASPend {T A} _ {_}.

Variant CASState {T A} :=
| CASDef (v : option A) (m : option (CASPend T A)). (* currently value and pending call *)
Arguments CASState : clear implicits.

Variant CASStep {T A} : CASState T A -> ThreadEvent T (CASSig A) -> CASState T A -> Prop :=
| CASCallCAS i a e n :
    CASStep
      (CASDef a None)
      (i, CallEv (CAS e n))
      (CASDef a (Some (MkCASPend i (CAS e n))))
| CASSucc i a e n :
    a = e ->
    CASStep
      (CASDef a (Some (MkCASPend i (CAS e n))))
      (i, RetEv (CAS e n) true)
      (CASDef n None)
| CASFail i a e n :
    a <> e ->
    CASStep
      (CASDef a (Some (MkCASPend i (CAS e n))))
      (i, RetEv (CAS e n) false)
      (CASDef a None)
| CASCallGet i a :
    CASStep
      (CASDef a None)
      (i, CallEv Get)
      (CASDef a (Some (MkCASPend i Get)))
| CASRetGet i a :
    CASStep
      (CASDef a (Some (MkCASPend i Get)))
      (i, RetEv Get a)
      (CASDef a None).

Program Definition casSpec {T A} : Spec T (CASSig A) := {|
  State := CASState T A;
  Step := CASStep;
  Init := CASDef None None
|}.

Admit Obligations.

Lemma lemCAS {T F A} {VF : Spec T F} {i : Name T}
  {M : Impl (CASSig A) F}
  (P R G : Relt casSpec VF)
  (e n : option A) :
  forall (RS RF : Prec casSpec VF),
  (R ->> R ==> R) ->
  (forall s xs t ys,
    R s xs t ys ->
    (exists a m,
      m <> None /\
      snd s = CASDef a m) ->
    snd s = snd t) ->
  (forall s xs t,
    InterStep M s (i, UEvent (Some (CallEv (CAS e n)))) t ->
    G s xs t xs) ->
  (forall s xs,
    ReltToPrec P s xs ->
    exists x, xs x) ->
  (forall ) ->
  VerifyProg i R G
    P
    (call (CAS e n))
    (fun v _ _ r zs =>
      exists t ys,
        (v = true  /\ RS t ys \/
         v = false /\ RF t ys) /\
        R t ys r zs).
intros RS RF.
intros R_trans R_pres G_step xs_nemp.
eapply weakenPost.
eapply (lemCall
  (Q:=fun s xs t ys =>
    ReltToPrec P s xs /\
    (exists a,
      snd s = CASDef a None /\
      snd t = CASDef a (Some (MkCASPend i (CAS e n)))))).
{
  unfold Stable, stableRelt, sub, subRelt.
  intros. psimpl.
  split.
  {
    exists x2, x3. easy.
  }
  {
    apply R_pres in H0.
    2:{
      eexists x1, _.
      split. 2: exact H2.
      easy.
    }
    exists x1.
    split. easy.
    congruence.
  }
}
{
  admit.
}
{
  unfold Commit. intros. psimpl.
  ddestruct H1. ddestruct H2.
  exists ρs. repeat split.
  {
    eapply xs_nemp.
    exists x1, x0.
    exact H.
  }
  {
    intros. exists σ.
    repeat (easy || constructor).
  }
  {
    exists x1, x0.
    easy.
  }
  {
    exists a. easy.
  }
  {
    eapply G_step.
    symmetry. exact x4.
    symmetry. exact x.
  }
}