From LHL.Core Require Import
  LogicFacts
  Traces
  Specs
  Logic.

Definition SPrec {T E F} (VE : Spec T E) (VF : Spec T F) :=
  InterState F VE ->
  Poss VF ->
  Prop.

Definition SRelt {T E F} (VE : Spec T E) (VF : Spec T F) :=
  InterState F VE ->
  Poss VF ->
  InterState F VE ->
  Poss VF ->
  Prop.

Definition LiftSPrec {T E F} {VE : Spec T E} {VF : Spec T F} (P : SPrec VE VF) : Prec VE VF :=
  fun s xs =>
    exists x, xs = eq x /\
      P s x.
Coercion LiftSPrec : SPrec >-> Prec.

Definition LiftSRelt {T E F} {VE : Spec T E} {VF : Spec T F} (R : SRelt VE VF) : Relt VE VF :=
  fun s xs t ys =>
    forall x, xs = eq x ->
      exists y, ys = eq y /\
        R s x t y.
Coercion LiftSRelt : SRelt >-> Relt.

Definition SPrecCompose {T E F} {VE : Spec T E} {VF : Spec T F} (P : SPrec VE VF) (R : SRelt VE VF) : SPrec VE VF :=
  fun t σ => exists s ρ, P s ρ /\ R s ρ t σ.

Notation "R <<S G" := (SPrecCompose R G) (left associativity, at level 37).

Definition SReltCompose {T E F} {VE : Spec T E} {VF : Spec T F} (R G : SRelt VE VF) : SRelt VE VF :=
  fun s ρ r τ => exists t σ, R s ρ t σ /\ G t σ r τ.
Notation "R S>> G" := (SReltCompose R G) (right associativity, at level 39).

Class HasSSub A :=
  ssub : A -> A -> Prop.
Notation "P S=> Q" := (ssub P Q) (right associativity, at level 41).

Global Instance subSPrec {T E F} {VE : Spec T E} {VF : Spec T F} : HasSSub (SPrec VE VF) :=
  fun P Q => forall s ρ, P s ρ -> Q s ρ.

Global Instance subSRelt {T E F} {VE : Spec T E} {VF : Spec T F} : HasSSub (SRelt VE VF) :=
  fun P Q => forall s ρ t σ, P s ρ t σ -> Q s ρ t σ.

Class HasSStable {T E F} {VE : Spec T E} {VF : Spec T F} A :=
  SStable : SRelt VE VF -> A -> Prop.

Global Instance stableSRelt {T E F} {VE : Spec T E} {VF : Spec T F} : HasSStable (SRelt VE VF) :=
  fun R Q => (Q S>> R S=> Q).

Global Instance stableSPrec {T E F} {VE : Spec T E} {VF : Spec T F} : HasSStable (SPrec VE VF) :=
  fun R P => P <<S R S=> P.

Lemma liftSPrecStable {T E F} {VE : Spec T E} {VF : Spec T F} :
  forall (R : SRelt VE VF) (P : SPrec VE VF),
  SStable R P ->
  Stable R (LiftSPrec P).
unfold SStable, stableSPrec, Stable, stablePrec.
unfold sub, ssub, subSPrec, subPrec.
unfold LiftSPrec, LiftSRelt in *.
intros. psimpl. specialize (H1 x1 eq_refl).
psimpl. exists x0. split. easy.
apply H. exists x, x1. easy.
Qed.

Lemma liftSReltStable {T E F} {VE : Spec T E} {VF : Spec T F} :
  forall (R : SRelt VE VF) (Q : SRelt VE VF),
  SStable R Q ->
  Stable R (LiftSRelt Q).
unfold SStable, stableSRelt, Stable, stableRelt.
unfold sub, ssub, subSRelt, subRelt.
unfold LiftSRelt in *. intros. psimpl.
specialize (H0 x eq_refl). psimpl.
specialize (H2 x2 eq_refl). psimpl.
exists x1. split. easy.
apply H. exists x0, x2. easy.
Qed.

Inductive SRTC {T E F} {VE : Spec T E} {VF : Spec T F} (R : SRelt VE VF) : SRelt VE VF :=
| RTCRefl s ρ : SRTC R s ρ s ρ
| RTCStep s ρ t σ r τ :
    R s ρ t σ ->
    SRTC R t σ r τ ->
    SRTC R s ρ r τ.


Ltac psimpl :=
repeat lazymatch goal with
| [ H : prComp ?P ?R ?s ?ρ ?t ?σ |- _ ] => destruct H
| [ H : ReltCompose ?P ?Q ?s ?ρ ?t ?σ |- _] => destruct H
| [ H : PrecCompose ?P ?Q ?s ?ρ |- _] => destruct H
| [ H : SReltCompose ?P ?Q ?s ?ρ ?t ?σ |- _] => destruct H
| [ H : SPrecCompose ?P ?Q ?s ?ρ |- _] => destruct H
| [ H : ?P /\ ?Q |- _ ] => destruct H
| [ H : exists x, ?P |- _ ] => destruct H
| [ H : ReltToPrec ?R ?s ?ρ |- _ ] => destruct H
| [ H : PrecToRelt ?R ?s ?ρ ?t ?σ |- _ ] => destruct H
end;
simpl in *;
subst;
repeat lazymatch goal with
| [ H : ?A, H' : ?A |- _] => clear H'
end.

Ltac psplit :=
match goal with
| [ |- ReltCompose ?P ?Q ?s ?ρ ?t ?σ ] =>
    do 2 eexists; split
| [ |- PrecCompose ?P ?Q ?s ?ρ ] =>
    do 2 eexists; split
| [ |- SReltCompose ?P ?Q ?s ?ρ ?t ?σ ] =>
    do 2 eexists; split
| [ |- SPrecCompose ?P ?Q ?s ?ρ ] =>
    do 2 eexists; split
| [ |- prComp ?P ?Q ?s ?p ?t ?q ] =>
  split
| [ |- _ ] => fail "Cannot split on this goal"
end.
