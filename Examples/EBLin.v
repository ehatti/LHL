From LHL.Core Require Import
  Linearizability
  LogicFacts
  Traces
  Specs
  Program
  Tensor
  LinFacts.

From LHL.Examples Require Import
  CASSpec
  ExchangerSpec
  Exchanger
  ElimArray
  EBStack
  NameSpec
  RandomSpec
  WaitFreeStackSpec
  WaitFreeStack
  MemSpec
  AtomicStackSpec
  ArraySpec
  Array.
Import WriteRacyMem.

From LHL.Util Require Import
  Heap.

Fixpoint ntensorImpl {E F} (M : Impl E F) N
  : Impl (nsig E N) (nsig F N)
:=
  match N with
  | 0 => idImpl
  | S N => M :⊗: (ntensorImpl M N)
  end.

Definition LinkedEBSig T A :=
  (RandSig |+| nsig (NameSig T |+| CASSig (Offer T (option A))) T) |+| (CASSig Addr |+| MemSig (A * option Addr)).

Definition LinkedEBUnderlay T A : Spec T (LinkedEBSig T A) :=
  (randSpec ⊗ ntensor (nameSpec ⊗ casSpec) T) ⊗ (casSpec ⊗ memSpec).

Definition LinkedEBImpl T A : Impl (LinkedEBSig T A) (AtomicStackSig A) :=
  (idImpl :⊗: (ntensorImpl exchImpl T |> arrayImpl) |> elimArray T (option A)) :⊗: WFStack A |> EBStack A.

Lemma ntensorLin {T E F N} :
  forall (VE : Spec T E) (M : Impl E F) (VF : Spec T F),
  VE ▷ M ↝ VF ->
  ntensor VE N ▷ ntensorImpl M N ↝ ntensor VF N.
Proof.
  intros.
  induction N. easy.
  now apply hcomp_lin.
Qed.

Module EB_Lin(Import Params : WFS_PARAMS).

Module AtomicWFStackProof := AtomicWFStackProof(Params).
Import AtomicWFStack AtomicWFStackProof.

Theorem EBStack_lin :
  LinkedEBUnderlay T A ▷ LinkedEBImpl T A ↝ atomicStackSpec.
Proof.
  unfold LinkedEBUnderlay, LinkedEBImpl.
  apply vcomp_lin.
  eexists. split.
  2:{
    eapply soundness.
    apply EBStackCorrect.
  }
  apply hcomp_lin.
  {
    apply vcomp_lin.
    eexists. split.
    2:{
      eapply soundness.
      apply elimArrayCorrect.
    }
    apply hcomp_lin.
    { easy. }
    {
      apply vcomp_lin.
      eexists. split.
      2:{
        eapply soundness.
        apply arrayCorrect.
      }
      apply ntensorLin.
      eapply soundness.
      apply oneCellExchCorrect.
    }
  }
  {
    eapply soundness. cbn.
    apply WFStackCorrect.
  }
Qed.