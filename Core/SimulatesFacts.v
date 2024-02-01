From Coq Require Import 
    List.

From LHL.Util Require Import
    TransUtil.

From LHL.Core Require Import
    Program
    Specs
    Traces
    Simulates.

From LHL.Core Require Import
    TracesFacts.

Lemma simulate_isPathOf {E} {spec spec' : Spec E} : 
    forall t s1 s1' s2,
    Simulates_ spec spec' s1 s1' -> 
    IsPathOf s1 t s2 (Steps spec.(Step)) -> 
    exists s2', IsPathOf s1' t s2' (Steps spec'.(Step)).
Proof. 
    induction t.
    - intros; exists s1'; constructor.
    - intros. inversion H0. subst.
      destruct H. apply (H a st'') in H3.
      destruct H3. 
      destruct (IHt st'' x s2 H2 H5).
      exists x0. eapply StepsMore. apply H1. apply H3.
Qed.

Theorem simulates_refines {E} :
    forall (spec spec' : Spec E),
        Simulates spec spec' -> 
        specRefines spec spec'.
    Proof.
        unfold specRefines, Incl, IsTraceOfSpec in *. intros. 
        destruct H0; eapply simulate_isPathOf; eassumption.
Qed.