From LHL.Core Require Import
  Program
  ProgramFacts
  Specs
  Logic.

From LHL.Util Require Import
  Tactics
  TransUtil
  Util.

Variant NameSig {T} : ESig :=
| Self : NameSig (Name T).
Arguments NameSig : clear implicits.

Definition NameState T := option (Name T).

Variant NameStep {T} : NameState T -> ThreadEvent T (NameSig T) -> NameState T -> Prop :=
| CallSelf i : NameStep None (i, CallEv Self) (Some i)
| RetSelf i : NameStep (Some i) (i, RetEv Self i) None.

Program Definition nameSpec {T} : Spec T (NameSig T) := {|
  State := NameState T;
  Step := NameStep;
  Init := None
|}.

Admit Obligations.

Lemma lemBindSelf {T E F A} {VE : Spec T E} {VF : Spec T F}
  `{SigCoercion (NameSig T) E}
  {P R G : Relt VE VF} {Q : Post VE VF A} {C : Name T -> Prog E A} :
  forall i : Name T,
  VerifyProg i R G P (_ <- call Self; C i) Q ->
  VerifyProg i R G P (i' <- call Self; C i') Q.
intros. ddestruct H0.
{
  rewrite frobProgId with (p:=_;;_) in x.
  simpl in x. ddestruct x.
}
{
  rewrite frobProgId with (p:=_;;_) in x.
  simpl in x. ddestruct x.
  rewrite frobProgId at 1. cbn.
  eapply SafeBind with (QI:=QI) (QR:=QR).
  easy. easy. easy.
  intros. specialize (H3 i). destruct H3.
  split.
  {
    clear - H3.
    unfold Commit in *. intros.
    admit.
  }
  {
    admit.
  }
}
Admitted.