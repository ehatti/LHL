From LHL Require Import
  Logic.

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
unfold Stable, stablePrec, impl, implPrec, PrecCompose.
intros.
do 6 destruct H1.
do 2 eexists.
split.
exact H1.
eapply stableRight.
exact H0.
do 2 eexists.
split.
exact H3.
easy.
Qed.

Lemma reltCompStable {E VE F} {R : @Relt E VE F} {Q S} :
  Stable R Q ->
  Stable R S ->
  Stable R (Q >> S).
intros.
unfold Stable, stableRelt, impl, implRelt.
intros.
split.
intros.
do 3 destruct H1.
do 3 destruct H2.
do 2 eexists.
split.
eapply stableLeft.
exact H.
do 2 eexists.
split.
exact H1.
exact H2.
easy.
intros.
do 6 destruct H1.
do 2 eexists.
split.
exact H1.
eapply stableRight.
exact H0.
do 2 eexists.
split.
exact H3.
easy.
Qed.