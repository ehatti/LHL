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
  AtomicStackSpec
  ArraySpec
  Array.

Infix "⊗" := tensorSpec (at level 40).

Theorem ExchLin {T A} :
  Lin (T:=T)
    (overObj ((nameSpec ⊗ casSpec) :> exchImpl (A:=A)))
    exchSpec.
eapply soundness.
apply oneCellExchCorrect.
Qed.

Theorem ElimArrLin {T A} :
  Lin (T:=T)
    (overObj ((randSpec ⊗ arraySpec T exchSpec) :> elimArray T A)) exchSpec.
eapply soundness.
apply elimArrayCorrect.
Qed.

Definition arrEBImpl T A :
  Impl
    ((RandSig |+| ArraySig (CASSig (option A)) T) |+| WaitFreeStackSig A)
    (AtomicStackSig A)
:=
  tensorImpl
    (arrayImpl
    |> elimArray T (option A))
    idImpl 
  |> EBStack A.

Theorem EBLin {T A} :
  Lin (T:=T)
    (overObj
      (((ntensor (nameSpec ⊗ casSpec) T) ⊗ wfStackSpec) :>
      (tensorImpl (elimArray T A) idImpl |> EBStack A)))
    atomicStackSpec.