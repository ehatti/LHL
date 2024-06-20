From LHL.Core Require Import
  Program
  Specs.

Section Tensor.
  Context {TL TR EL ER}
          (specL : Spec TL EL)
          (specR : Spec TR ER).

  Definition StepTensor st (ev : ThreadEvent (TL + TR) (EL |+| ER)) st' :=
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

Definition tensorImpl 
  {EL FL} (ML : Impl EL FL) {ER FR} (MR : Impl ER FR) : Impl (EL |+| ER) (FL |+| FR) :=
  fun Ret m =>
    match m with
      | inl mL => mapProg (fun _ => inl) (ML Ret mL)
      | inr mR => mapProg (fun _ => inr) (MR Ret mR)
    end.

Definition tensorLayer
          {EL FL} (layL : Layer EL FL)
          {ER FR} (layR : Layer ER FR) :
  Layer (EL |+| ER) (FL |+| FR) :=
  {|
    USpec := tensorSpec layL.(USpec) layR.(USpec);
    LImpl := tensorImpl layL.(LImpl) layR.(LImpl)
  |}.