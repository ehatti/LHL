From LHL.Core Require Import
  Program
  Specs.

From LHL.Util Require Import
  Util
  TransUtil
  Tactics.

From Coq Require Import
  Program.Equality.

Definition TensorActive EL ER := ThreadName -> option ({A & (EL |+| ER) A}).

Record TensorState {EL ER} {specL : Spec EL} {specR : Spec ER} := MkTS {
  TActive : TensorActive EL ER;
  LState : specL.(State);
  RState : specR.(State)
}.
Arguments TensorState {EL ER} specL specR.

Section Tensor.

Context {EL ER}
        (specL : Spec EL)
        (specR : Spec ER).

Definition TensorStep st (ev : ThreadEvent (EL |+| ER)) st' :=
  match ev with
    | (i, CallEv m) => 
        match m with
        |  inl m' =>
          specL.(Step) st.(LState) (i, CallEv m') st'.(LState) /\
          st.(TActive) i = None /\ st'.(TActive) i = Some (existT _ _ m) /\
          differ_pointwise st.(TActive) st'.(TActive) i /\
          st.(RState) = st'.(RState)
        |  inr m' =>
          specR.(Step) st.(RState) (i, CallEv m') st'.(RState) /\
          st.(TActive) i = None /\ st'.(TActive) i = Some (existT _ _ m) /\
          differ_pointwise st.(TActive) st'.(TActive) i /\
          st.(LState) = st'.(LState)
        end
    | (i, RetEv m n) => 
        match m with
        | inl m' =>
          specL.(Step) st.(LState) (i, RetEv m' n) st'.(LState) /\
          st.(TActive) i = Some (existT _ _ m) /\ st'.(TActive) i = None /\
          differ_pointwise st.(TActive) st'.(TActive) i /\
          st.(RState) = st'.(RState)
        | inr m' =>
          specR.(Step) st.(RState) (i, RetEv m' n) st'.(RState) /\
          st.(TActive) i = Some (existT _ _ m) /\ st'.(TActive) i = None /\
          differ_pointwise st.(TActive) st'.(TActive) i /\
          st.(LState) = st'.(LState)
        end
  end.

Program Definition tensorSpec : Spec (EL |+| ER) :=
  {|
    State := TensorState specL specR;
    Step := TensorStep;
    Init := {|
      TActive _ := None;
      LState := Init specL;
      RState := Init specR
    |}
  |}.

Next Obligation.
generalize dependent (fun _ : ThreadName => @None {A : Type & (EL |+| ER) A}).
generalize dependent (Init specL). generalize dependent (Init specR).
induction p; cbn; intros.
{
  constructor.
}
{
  dependent destruction H. destruct st''.
  destruct a, e, m; cbn in *; destruct_all;
  eapply IHp in H0; clear IHp.
  econstructor. easy. exact H2. easy.
  econstructor. easy. exact H2. easy.
  econstructor. easy. exact H2. easy.
  econstructor. easy. exact H2. easy.
}
Qed.

End Tensor.

Arguments MkTS {EL ER specL specR}.

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