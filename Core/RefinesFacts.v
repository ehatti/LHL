From LHL.Util Require Import
  Util
  TransUtil
  Tactics.

From LHL.Core Require Import
  Program
  Specs
  Traces
  TracesFacts
  Eutt.

From Coq Require Import
  Program.Equality
  Relations.Relation_Operators
  Logic.PropExtensionality.

From Paco Require Import
  paco.

(* Basic Refinement Properties *)

Lemma layerRefines_trans {E1 E2 E3 F} :
  forall (lay1 : Layer E1 F) (lay2 : Layer E2 F) (lay3 : Layer E3 F),
    layerRefines lay1 lay2 -> layerRefines lay2 lay3 ->
    layerRefines lay1 lay3.
Proof.
  intros. unfold layerRefines, specRefines in *.
  eapply TransUtil.Incl_trans.
  apply H. apply H0.
Qed.

(* Eutt implies refinement *)

Theorem eutt_layerRefines {E F} : 
  forall (spec : Spec E) (impl impl' : Impl E F), 
  euttImpl ieq impl impl' -> 
  layerRefines (spec :> impl) (spec :> impl').
unfold euttImpl, layerRefines, specRefines, Incl, IsTraceOfSpec, Steps.
Admitted.

(* Crucial Refinement Properties *)

Lemma help {E F} :
  forall (p : Trace (ThreadLEvent E F)),
  projSilent (projUnder p) = projUnderThr p.
intros.
induction p.
easy.
destruct a, l, ev.
simpl.
rewrite IHp.
all: easy.
Qed.

Lemma projUnderSteps {E F} {lay : Layer E F} :
  forall s p t,
  BwdSteps (Step (overObj lay)) s p t ->
  exists q,
  BwdSteps (Step lay.(USpec)) (snd s) q (snd t).
intros.
generalize dependent t.
induction p.
intros.
dependent destruction H.
exists Start.
constructor.
intros.
dependent destruction H.
apply IHp in H.
simpl in H0.
destruct_all.
eexists.
eapply BwdSteps_app.
exact H.
rewrite decompUnderSteps in H0.
destruct_all.
rewrite <- H2.
apply Steps_iso in H0.
exact H0.
Qed.

Theorem mkLayer_monotonic {E F} :
  forall (spec spec' : Spec E) (impl : Impl E F),
  specRefines spec' spec -> 
  layerRefines (spec' :> impl) (spec :> impl).
unfold layerRefines, specRefines, Incl, IsTraceOfSpec.
intros.
destruct_all.
repeat rewrite decompOverObj in *.
destruct_all.
subst.
simpl in *.
eassert (exists st, Steps _ _ _ st).
exists (snd x).
exact H1.
apply H in H0.
destruct_all.
eexists (fst x, x1).
exists x0.
split.
easy.
simpl.
split.
easy.
easy.
Qed.

Theorem layerRefines_VComp_assoc {E F G} : 
  forall  (spec : Spec E) (impl : Impl E F) (impl' : Impl F G),
    layerRefines ((overObj (spec :> impl)) :> impl') ((spec :> impl) :|> impl').
unfold layerRefines, specRefines, Incl, IsTraceOfSpec.
Admitted.