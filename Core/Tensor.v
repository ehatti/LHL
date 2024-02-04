From LHL.Core Require Import
  Program
  Specs.

Section Tensor.
  Context {EL ER}
          (specL : Spec EL)
          (specR : Spec ER).

  Definition StepTensor st (ev : ThreadEvent (Sum EL ER)) st' :=
    match ev with
      | CallEv m => inl ev' => specL.(EvalInstruction) instr' (fst st) a (fst st') /\ (snd st = snd st')
      | CallEv n => inr instr' => specR.(EvalInstruction) instr' (snd st) a (snd st') /\ (fst st = fst st')
    end.

  Definition pairSpec : Spec PairInstruction :=
    {|
      State := prod specL.(State) specR.(State);
      EvalInstruction := EvalPairInstruction;
      initialState := (specL.(initialState), specR.(initialState))
    |}.

End Pair.

Arguments PairInstruction : clear implicits.