From LHL.Core Require Import
  Program
  Specs.

Section Tensor.
  Context {EL ER}
          (specL : Spec EL)
          (specR : Spec ER).

  Definition StepTensor st (ev : ThreadEvent (EL |+| ER)) st' :=
    match ev with
      | (i, CallEv m) => 
          match m with
          |  inl m' => specL.(Step) (fst st) (i, CallEv m') (fst st') /\ (snd st = snd st')
          |  inr m' => specR.(Step) (snd st) (i, CallEv m') (snd st') /\ (fst st = fst st')
          end
      | (i, RetEv m n) => 
          match m with
          | inl m' => specL.(Step) (fst st) (i, RetEv m' n) (fst st') /\ (snd st = snd st')
          | inr m' => specR.(Step) (snd st) (i, RetEv m' n) (snd st') /\ (fst st = fst st')
          end
    end.

  Definition tensorSpec : Spec (EL |+| ER) :=
    {|
      State := specL.(State) * specR.(State);
      Step := StepTensor;
      Init := (specL.(Init), specR.(Init))
    |}.

End Tensor.