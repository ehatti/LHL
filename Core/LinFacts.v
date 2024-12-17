From LHL.Core Require Import
  Program
  ProgramFacts
  Specs
  Traces
  Linearizability
  VCompFacts
  TensorFacts
  RefinesFacts
  Tensor
  TensorFacts.

From LHL.Util Require Import
  TransUtil
  Tactics.

(* Observational Refinement *)
Theorem lin_obs_ref {T E F} : 
  forall (spec' spec : Spec T E) (impl : Impl E F) ,
  spec' ↝ spec -> 
  (spec' ▷ impl) ⊑ (spec ▷ impl).
Proof.
  intros.
  apply (mkLayer_monotonic _ _ impl) in H.
  assert (H' := layerRefines_VComp_assoc spec idImpl impl).
  rewrite obj_VComp_assoc in H'.
  assert (ID_EUTT := idImpl_is_identity_l impl).
  assert (H'' := eutt_layerRefines spec _ _ ID_EUTT).
  eapply layerRefines_trans. eapply layerRefines_trans.
  apply H. apply H'. apply H''.
Qed.

(* Locality *)
Theorem locality {T E F} :
  forall (specE specE' : Spec T E) (specF specF' : Spec T F) ,
  specE' ↝ specE /\ specF' ↝ specF <->
  specE' ⊗ specF' ↝ (specE ⊗ specF).
Proof.
  intros.
  unfold Lin, KConc.
  constructor.
  - intros. destruct H.  
    assert (H1 := tensor_monotonic _ _ _ _ H H0).
    assert (H2 := tensor_layer_funct_l specE specF idImpl idImpl).
    unfold tensorLayer in H2. simpl in H2.
    assert (H3 := implEq_refines _ _ _ (tensorSpec specE specF) _ _ (@tensor_neutral E F)).
    eapply specRefines_trans. eapply specRefines_trans. 
    apply H1. apply H2. apply H3.
  - intros. 
    eapply tensor_monotonic_inv.
    assert (H1 := implEq_refines _ _ _ (tensorSpec specE specF) _ _ (implEqSym _ _ _ _ (@tensor_neutral E F))).
    assert (H2 := tensor_layer_funct_r specE specF idImpl idImpl); unfold tensorLayer in H2; simpl in H2. 
    eapply specRefines_trans. eapply specRefines_trans.
    apply H. apply H1. apply H2. 
Qed.

Theorem vcomp_lin {T E F G} :
  forall (VE : Spec T E) (VG : Spec T G),
  forall (MF : Impl E F) (MG : Impl F G),
  (exists VF : Spec T F,
    VE ▷ MF ↝ VF /\
    VF ▷ MG ↝ VG) ->
  VE ▷ (MF |> MG) ↝ VG.
Proof.
  unfold Lin, KConc. intros.
  destruct H as [VF [linMF linMG]].
  eapply specRefines_trans.
  eapply specRefines_trans.
  apply layerRefines_VComp_assoc_inv.
  2: exact linMG. now apply lin_obs_ref.
Qed.

Definition mapThs {E E' F F'}
  (f : forall A, E A -> E' A)
  (g : forall A, F A -> F' A)
  (s : ThreadState E F)
: ThreadState E' F' :=
  match s with
  | Idle => Idle
  | Cont om p => Cont (g _ om) (mapProg f p)
  | UCall om um k => UCall (g _ om) (f _ um) (fun x => mapProg f (k x))
  end.

Theorem hcomp_lin {T EL ER FL FR} :
  forall (VEL : Spec T EL) (VER : Spec T ER),
  forall (VFL : Spec T FL) (VFR : Spec T FR),
  forall (ML : Impl EL FL) (MR : Impl ER FR),
  VEL ▷ ML ↝ VFL ->
  VER ▷ MR ↝ VFR ->
  (VEL ⊗ VER) ▷ (ML :⊗: MR) ↝ (VFL ⊗ VFR).
Proof.
  intros.
  eapply specRefines_trans
    with (spec2:=?[spec2]).
  2:{
    change (_ ⊑ KConc (VFL ⊗ VFR))
    with (?spec2 ↝ (VFL ⊗ VFR)).
    apply locality.
    split. exact H. exact H0.
  }
  apply tensor_layer_funct_r.
Qed.