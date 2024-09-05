From LHL.Core Require Import
  Program
  Specs
  Logic.

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
  (P R G : Relt (@casSpec T A) VF)
  (PS PF : PossSet VF -> PossSet VF -> Prop)
  e n :
  VerifyProg i R G
    P
    (call (CAS e n))
    (fun v s xs t ys =>
      (v = false /\
        snd s = snd t)).
Admitted.
