From LHL.Core Require Import
  Logic
  LogicFacts
  Traces.

From LHL.Util Require Import
  TransUtil.

From Coq Require Import
  Lists.List.
Import ListNotations.

Definition wp {E VE F} impl i (R G Q : Relt E VE F) ev : Prec E VE F :=
  fun rs rρ =>
    forall s ρ t σ,
      R rs rρ s ρ ->
      InterStep (impl:=impl) i s (i, liftUEv ev) t ->
      Q s ρ t σ /\
      G s ρ t σ.

Lemma wpWeakest E VE F VF impl i R (G : Relt E VE F) Q ev :
  id ==> R ->
  Commit VF i impl G (wp impl i R G Q ev) ev Q.
intro Rid.
unfold Commit, wp.
intros.
destruct H as [σ].
exists σ.
eapply H0 in H1.
destruct H1.
split.
exact H1.
split.
easy.
exists nil.
split.
constructor.
rewrite app_nil_r.
easy.
apply Rid.
unfold id.
easy.
Qed.

Lemma wpStable E VE F impl i (R : Relt E VE F) G Q ev :
  R >> R ==> R ->
  Stable R (wp impl i R G Q ev).
intro Rtrans.
unfold Stable, stablePrec, sub, subPrec, wp.
intros.
pdestruct H.
eapply H in H1.
destruct H1.
split.
exact H1.
easy.
apply Rtrans.
psplit.
exact H2.
easy.
Qed.