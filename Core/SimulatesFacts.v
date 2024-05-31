From Coq Require Import 
  List
  Program.Equality.

From LHL.Util Require Import
  TransUtil
  Tactics.

From LHL.Core Require Import
  Program
  Specs
  Traces
  Simulates.

From LHL.Core Require Import
  TracesFacts.

Lemma simulate_isPathOf {E} {spec spec' : Spec E} : 
  forall t s1 s1' s2,
  Simulates spec spec' s1 s1' -> 
  Steps spec.(Step) s1 t s2 -> 
  exists s2', Steps spec'.(Step) s1' t s2'. 
induction t.
- intros; exists s1'; constructor.
- intros. inversion H0. subst.
  destruct H. apply (H a st'') in H3.
  destruct H3. destruct H1.
  destruct (IHt st'' x s2 H2 H5).
  exists x0. eapply StepsMore. apply H1. apply H3.
Qed.

Theorem simulates_refines {E} :
  forall (spec spec' : Spec E),
  Simulates spec spec' (Init spec) (Init spec') -> 
  specRefines spec spec'.
unfold specRefines, Incl, IsTraceOfSpec.
intros.
destruct_all.
eapply simulate_isPathOf.
exact H.
exact H0.
Qed.