From LHL.Core Require Import
  Program
  Specs.

From LHL.Util Require Import
  TransUtil
  Tactics
  Util.

Variant SnapSig {A} : ESig :=
| WriteSnap (v : A) : SnapSig (option (set A)).
Arguments SnapSig : clear implicits.

Variant SnapState {T A} :=
| SnapDef (vs : set A) (m : Name T -> option A).
Arguments SnapState : clear implicits.

Variant SnapStep {T A} : SnapState T A -> ThreadEvent T (SnapSig A) -> SnapState T A -> Prop :=
| SnapCall i v vs m m' :
    m i = None ->
    m' i = Some v ->
    differ_pointwise m m' i ->
    SnapStep
      (SnapDef vs m)
      (i, CallEv (WriteSnap v))
      (SnapDef (insert v vs) m')
| SnapCallFail i v vs m m' :
    m i = None ->
    m' i = Some v ->
    differ_pointwise m m' i ->
    SnapStep
      (SnapDef vs m)
      (i, CallEv (WriteSnap v))
      (SnapDef vs m')
| SnapRetFail i v vs m m' :
    m i = Some v ->
    m' i = None ->
    differ_pointwise m m' i ->
    SnapStep
      (SnapDef vs m)
      (i, RetEv (WriteSnap v) None)
      (SnapDef vs m').

Program Definition snapSpec {T A} : Spec T (SnapSig A) := {|
  State := SnapState T A;
  Step := SnapStep;
  Init := SnapDef emp (fun _ => None)
|}.

Next Obligation.
Proof.
  generalize dependent p.
  pose (f (m : Name T -> option A) i :=
    match m i with
    | Some v => Some (existT _ _ (WriteSnap v))
    | None => None
    end : option {R & SnapSig A R}
  ).
  assert ( diff :
    forall m m' i,
      differ_pointwise m m' i ->
      differ_pointwise (f m) (f m') i
  ).
  {
    unfold differ_pointwise.
    intros. subst f. simpl.
    now rewrite H.
  }
  cut (
    forall p vs m,
      Steps SnapStep (SnapDef vs m) p s ->
      SeqConsistent (f m) p
  ).
  { intros. now apply H in H0. }
  intros p.
  induction p; intros;
  ddestruct H. constructor.
  ddestruct H.
  {
    eapply SCCall with
      (a':= f m').
    {
      subst f. simpl.
      now rewrite H.
    }
    {
      subst f. simpl.
      now rewrite H0.
    }
    { now apply diff. }
    {
      eapply IHp.
      exact H2.
    }
  }
  {
    eapply SCCall with
      (a':= f m').
    {
      subst f. simpl.
      now rewrite H.
    }
    {
      subst f. simpl.
      now rewrite H0.
    }
    { now apply diff. }
    {
      eapply IHp.
      exact H2.
    }
  }
  {
    eapply SCRet with
      (a':= f m').
    {
      subst f. simpl.
      now rewrite H.
    }
    {
      subst f. simpl.
      now rewrite H0.
    }
    { now apply diff. }
    {
      eapply IHp.
      exact H2.
    }
  }
Qed.