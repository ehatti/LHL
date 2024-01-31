 From Paco Require Import paco.

From LHL.Core Require Import
  Program
  Specs
  Traces
  Eutt
  ProgramFacts.
From LHL.Util Require Import
  Util.

(* Identity Laws for Program and Implementation Vertical Composition *)

Lemma substIdImpl_is_id_l {E R} (p : Prog E R)
  : eutt ieq (substProg idImpl p) p.
Proof.
  enough (J : forall q p : Prog E R,
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

Lemma substIdImpl_is_id_r {E F} (M : Impl E F)
  {R} (f : F R)
  : eutt ieq (substProg M (idProg f)) (M _ f).
Proof.
  rewrite (frobProgId (substProg _ _)). cbn.
  apply eutt_NoOp_l.
  remember (M R f) as p eqn:E0. clear E0 f.
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
    forall (M : Impl E F) , 
    euttImpl (Ret := Ret) ieq (idImpl |> M) M.
Proof.
  intros. unfold euttImpl. intros.
  apply substIdImpl_is_id_l.
Qed.

Theorem idImpl_is_identity_r {E F Ret} : 
    forall (M : Impl E F) , 
    euttImpl (Ret := Ret) ieq (M |> idImpl) M.
Proof.
  intros. unfold euttImpl. intros.
  apply substIdImpl_is_id_r.
Qed.

(* Associativity *)

Lemma substProg_assoc {E F G}
      (f : Impl F G) (g : Impl E F)
  : (ieq ==> eutt ieq)%isig
      (fun _ (p : Prog G _) => substProg g (substProg f p))
      (@substProg _ _ (fun _ (m : G _) =>
                         substProg g (f _ m))).
Proof.
  intros ? e _ [].
  enough (forall (p1 p2 : Prog E T),
    subst_subst_bisim f g p1 p2 ->
    eutt ieq p1 p2).
  { apply H; constructor. }
  clear. pcofix self; intros _ _ []; pfold.
  all:
    match goal with
    | [ |- _ ?p1 ?p2 ] => rewrite (frobProgId p1), (frobProgId p2)
    end;
    match goal with
    | [ p : Prog _ _ |- _ ] => destruct p; cbn
    end; constructor.
  all: try reflexivity.
  all: right; apply self; constructor.
Qed.

Theorem implVComp_assoc {E F G H Ret} :
  forall (MF : Impl E F) (MG : Impl F G) (MH : Impl G H),
  euttImpl (Ret := Ret) ieq (MF |> (MG |> MH)) ((MF |> MG) |> MH).
Proof.
  intros. unfold euttImpl. intros.
  apply substProg_assoc. reflexivity.
Qed.