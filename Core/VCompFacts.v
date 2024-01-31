 From Paco Require Import paco.

From LHL.Core Require Import
  Program
  Specs
  Traces
  Eutt
  ProgramFacts.
From LHL.Util Require Import
  Util.

Lemma substIdImpl_is_id_l {M R} (p : Prog M R)
  : eutt ieq (substProg idImpl p) p.
Proof.
  enough (J : forall q p : Prog M R,
             (q = substProg (fun _ m => Bind m Return) p \/
              q = NoOp (substProg (fun _ m => Bind m Return) p)) ->
             eutt ieq q p).
  { apply J. left; reflexivity. }
  clear. pcofix SELF. intros q p.
  enough (J : paco2 (euttF ieq) r (substProg (fun _ m => Bind m Return) p) p).
  { intros []; subst; [ apply J | apply euttF_Noop_L, J ]. }
  pfold.
  destruct p.
  - rewrite (frobProgId (substProg _ _)). cbn. constructor.
    rewrite (frobProgId (bindSubstProg _ _ _)). cbn.
    constructor; [ constructor | ].
    intros x. right.
    rewrite (frobProgId (bindSubstProg _ _ _)). cbn.
    apply SELF. right. reflexivity.
  - rewrite (frobProgId (substProg _ _)). cbn. constructor.
  - rewrite (frobProgId (substProg _ _)). cbn. constructor.
    right. apply SELF. left. reflexivity.
Defined.

Lemma substIdImpl_is_id_r {E F} (impl : Impl E F)
  {R} (f : F R)
  : eutt ieq (substProg impl (idProg f)) (impl _ f).
Proof.
  rewrite (frobProgId (substProg _ _)). cbn.
  apply eutt_NoOp_l.
  remember (impl R f) as p eqn:E0. clear E0 f.
  revert p. pcofix SELF. intros p.
  pfold.
  destruct p;
    rewrite (frobProgId (bindSubstProg _ _ _)); cbn; constructor.
  - constructor.
  - right; auto.
  - rewrite (frobProgId (substProg _ _)); cbn; constructor.
  - right; auto.
Qed.

Theorem idImpl_is_identity_l {E F Ret} : 
    forall (impl : Impl E F) , 
    euttImpl (Ret := Ret) ieq (idImpl |> impl) impl.
Proof.
  intros. unfold euttImpl. intros.
  apply substIdImpl_is_id_l.
Qed.

Theorem idImpl_is_identity_r {E F Ret} : 
    forall (impl : Impl E F) , 
    euttImpl (Ret := Ret) ieq (impl |> idImpl) impl.
Proof.
  intros. unfold euttImpl. intros.
  apply substIdImpl_is_id_r.
Qed.