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
  : eutt (substProg idImpl p) p.
Proof.
  enough (J : forall q p : Prog E R,
             (q = substProg (fun _ m => Vis m Return) p \/
              q = Tau (substProg (fun _ m => Vis m Return) p)) ->
             eutt q p).
  { apply J. left; reflexivity. }
  clear. pcofix SELF. intros q p.
  enough (J : paco2 euttF r (substProg (fun _ m => Vis m Return) p) p).
  { intros []; subst; [ apply J | apply euttF_Noop_L, J ]. }
  pfold.
  destruct p.
  - rewrite (frobProgId (substProg _ _)). cbn. constructor.
    rewrite (frobProgId (bindSubstProg _ _ _)). cbn.
    constructor.
    intros x. right.
    rewrite (frobProgId (bindSubstProg _ _ _)). cbn.
    apply SELF. right. reflexivity.
  - rewrite (frobProgId (substProg _ _)). cbn. constructor.
  - rewrite (frobProgId (substProg _ _)). cbn. constructor.
    right. apply SELF. left. reflexivity.
Qed.

Lemma substIdImpl_is_id_r {E F} (M : Impl E F)
  {R} (f : F R)
  : eutt (substProg M (idProg f)) (M _ f).
Proof.
  rewrite (frobProgId (substProg _ _)). cbn.
  apply eutt_Tau_l.
  remember (M R f) as p eqn:E0. clear E0 f.
  revert p. pcofix SELF. intros p.
  pfold.
  destruct p; rewrite frobProgId at 1; simpl; constructor.
  - intros. right. apply SELF.
  - fold (substProg (E:=E) (F:=F)).
    rewrite frobProgId at 1. simpl.
    constructor.
  - right. apply SELF.
Qed.

Theorem idImpl_is_identity_l {E F} : 
    forall (M : Impl E F) , 
    euttImpl (idImpl |> M) M.
Proof.
  intros. unfold euttImpl. intros.
  apply substIdImpl_is_id_l.
Qed.

Theorem idImpl_is_identity_r {E F} : 
    forall (M : Impl E F) , 
    euttImpl (M |> idImpl) M.
Proof.
  intros. unfold euttImpl. intros.
  apply substIdImpl_is_id_r.
Qed.

(* Associativity *)

Lemma substProg_assoc {E F G R} (f : Impl F G) (g : Impl E F) :
  forall p,
  eutt (substProg g (substProg f p)) (substProg (Ret:=R) (fun _ (m : G _) => substProg g (f _ m)) p).
Proof.
  intro p.
  enough (forall (p1 p2 : Prog E R),
    subst_subst_bisim f g p1 p2 ->
    eutt p1 p2).
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

Theorem implVComp_assoc {E F G H} :
  forall (MF : Impl E F) (MG : Impl F G) (MH : Impl G H),
  euttImpl (MF |> (MG |> MH)) ((MF |> MG) |> MH).
Proof.
  intros. unfold euttImpl. intros.
  apply substProg_assoc.
Qed.

Theorem obj_VComp_assoc {T E F G} :
  forall (spec : Spec T E) (impl : Impl E F) (impl' : Impl F G),
  ((spec :> impl) :|> impl') = (spec :> impl |> impl').
Proof.
    auto.
Qed.
