From LHL Require Import
  Logic
  LogicTactics
  Specs
  Traces.

Lemma stableRight {E VE F} {R Q : @Relt E VE F} : Stable R Q -> (Q >> R) ==> Q.
unfold Stable, stableRelt.
easy.
Qed.

Lemma stableLeft {E VE F} {R Q : @Relt E VE F} : Stable R Q -> (R >> Q) ==> Q.
unfold Stable, stableRelt.
easy.
Qed.

Lemma precCompStable {E VE F} {R : @Relt E VE F} {P Q} :
  Stable R P ->
  Stable R Q ->
  Stable R (P << Q).
intros.
unfold Stable, stablePrec, impl, implPrec.
intros.
do 2 pdestruct H1.
psplit.
exact H1.
stable.
right.
psplit.
exact H3.
easy.
Qed.

Lemma reltCompStable {E VE F} {R : @Relt E VE F} {Q S} :
  Stable R Q ->
  Stable R S ->
  Stable R (Q >> S).
intros.
unfold Stable, stableRelt, impl, implRelt.
split.
intros.
pdestruct H1.
pdestruct H2.
psplit.
stable.
left.
psplit.
exact H1.
exact H2.
easy.
intros.
do 2 pdestruct H1.
psplit.
exact H1.
stable.
right.
psplit.
exact H3.
easy.
Qed.

Theorem soundness {E F} (lay : Layer E F) VF :
  (exists R G P Q, VerifyImpl lay.(USpec) VF R G P lay.(LImpl) Q) ->
  specRefines VF (overObj lay).
Admitted.