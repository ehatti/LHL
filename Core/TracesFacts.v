From LHL.Core Require Import
    Program
    Specs
    Traces.

Lemma nil_IsTraceOfSpec {E} :  
    forall (spec : Spec E),
    IsTraceOfSpec nil spec.
Proof.
    intros. exists spec.(Init). apply TransUtil.StepsNone.
Qed.

