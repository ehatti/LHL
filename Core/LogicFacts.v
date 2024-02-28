From LHL Require Import
  Logic
  Specs
  Traces
  Linearizability
  Program.

From LHL.Util Require Import
  TransUtil.

From Coq Require Import
  Program.Equality
  Lists.List
  Relations.Relation_Operators.

Import ListNotations.
Open Scope list_scope.

Ltac psplit :=
match goal with
| [ |- ReltCompose ?P ?Q ?s ?ρ ?t ?σ ] =>
    do 2 eexists; split
| [ |- PrecCompose ?P ?Q ?s ?ρ ] =>
    do 2 eexists; split
| [ |- ?G ] => fail "Cannot split on this goal"
end.

Ltac pdestruct H :=
match type of H with
| ReltCompose ?P ?Q ?s ?ρ ?t ?σ => do 3 destruct H
| PrecCompose ?P ?Q ?s ?ρ => do 3 destruct H
| TIdle ?i ?s ?ρ => destruct H
| TInvoke ?impl ?i ?Ret ?m ?s ?ρ ?t ?σ => do 2 destruct H
| InvokeAny ?impl ?i ?s ?ρ ?t ?σ => do 2 destruct H
| _ => fail "Cannot destruct this hypothesis"
end.

Ltac psimpl :=
repeat lazymatch goal with
| [ H : ReltCompose ?P ?Q ?s ?ρ ?t ?σ |- ?G] => destruct H
| [ H : PrecCompose ?P ?Q ?s ?ρ |- ?G] => destruct H
| [ H : ?P /\ ?Q |- ?G ] => destruct H
| [ H : exists x, ?P |- ?G ] => destruct H
| [ H : TInvoke ?impl ?i ?A ?l ?s ?ρ ?t ?σ |- ?G ] => destruct H
| [ H : ReltToPrec ?R ?s ?ρ |- ?G ] => destruct H
end;
simpl in *;
subst;
repeat lazymatch goal with
| [ H : ?A, H' : ?A |- ?G] => clear H'
end.

Ltac steps :=
repeat match goal with
| [ H : InterStep ?i ?st ?e ?st' |- ?G ] => dependent destruction H
| [ H : Step ?impl ?st ?ev ?st' |- ?G ] => simpl in H; dependent destruction H
end.

Lemma precCompStable {E VE F} {R : @Relt E VE F} {P Q} :
  Stable R P ->
  Stable R Q ->
  Stable R (P <<- Q).
intros.
unfold Stable, stablePrec, sub, subPrec.
intros.
do 2 pdestruct H1.
psplit.
exact H1.
destruct H0.
apply H4.
psplit.
exact H3.
easy.
Qed.

Lemma reltCompStable {E VE F} {R : @Relt E VE F} {Q S} :
  Stable R Q ->
  Stable R S ->
  Stable R (Q ->> S).
intros.
unfold Stable, stableRelt, sub, subRelt.
split.
intros.
destruct H.
destruct H0.
pdestruct H1.
pdestruct H4.
psplit.
apply H.
psplit.
exact H1.
exact H4.
easy.
intros.
do 2 pdestruct H1.
psplit.
exact H1.
destruct H0.
apply H4.
psplit.
exact H3.
easy.
Qed.

Lemma reltStableHelp {E VE F} {R : @Relt E VE F} {Q} :
    Stable R Q ->
    forall s ρ t σ,
    (((R ->> Q) s ρ t σ) \/ ((Q ->> R) s ρ t σ)) ->
    Q s ρ t σ.
intros.
destruct H.
destruct H0.
apply H.
easy.
apply H1.
easy.
Qed.

Lemma rtcTrans {E VE F} {R : Relt E VE F} : (RTC R ->> RTC R) ==> RTC R.
unfold sub, subRelt.
intros.
pdestruct H.
induction H.
easy.
econstructor.
exact H.
apply IHRTC.
easy.
Qed.

Lemma precStabilizedStable {E VE F} {R : Relt E VE F} {P} :
  (R ->> R ==> R) ->
  Stable R (P <<- R).
intros.
unfold Stable, stablePrec, sub, subPrec.
intros.
do 2 pdestruct H0.
psplit.
exact H0.
apply H.
psplit.
exact H2.
easy.
Qed.

Lemma rtpStable {E VE F} {R} {Q : Relt E VE F} :
  Stable R Q ->
  Stable R (ReltToPrec Q).
unfold Stable, stableRelt, stablePrec, ReltToPrec.
intros.
unfold sub, subPrec.
intros.
psimpl.
exists x1, x2.
apply H1.
psplit.
exact H0.
easy.
Qed.

Ltac stable :=
lazymatch goal with
| [ H : ?R ->> ?R ==> ?R |- @Stable _ _ _ _ stableRelt ?R (?P <<- ?R) ] =>
    apply (precStabilizedStable H)
| [ |- @Stable _ _ _ _ stablePrec ?R (?P <<- ?Q) ] =>
    eapply precCompStable; stable
| [ |- @Stable _ _ _ _ stableRelt ?R (?Q ->> ?S) ] =>
    eapply reltCompStable; stable
| [ H : @Stable _ _ _ _ stablePrec ?R ?P |- ?P ?s ?ρ ] =>
    apply H
| [ H : @Stable _ _ _ _ stableRelt ?R ?Q |- ?Q ?s ?ρ ?t ?σ ] =>
    apply (reltStableHelp H)
| _ => idtac
end.

Lemma newPossRefl {F} : forall (ρ : Trace (ThreadEvent F)), ρ --> ρ.
intros.
exists nil.
split.
constructor.
rewrite app_nil_r.
exists nil, nil.
split.
constructor.
split.
constructor.
apply rt_refl.
Qed.

(* Lemma safeBind {E F VF VE impl i R G P A B} {S : Post E VE F B} {m : E A} {k : A -> Prog E B} :
  forall PR PK,
  Stable R QI ->
  Commit VF i impl G P (CallEv m) QI ->
  Stable R QR ->
  (forall v,
    Commit VF i impl G QI (RetEv m v) QR /\
    VerifyProg VF i impl R G QR (k v) S) ->
  VerifyProg VF i impl R G P (Bind m k) S.
intros.
psimpl.
eapply SafeBind.
exact H.
exact H1.
easy.
easy.
Qed. *)

Create HintDb rely_lemmas.

Definition sp {E VE F} impl i VF (R : Relt E VE F) (P : Prec E VE F) ev : Relt E VE F :=
  fun s ρ t σ =>
    exists rs rρ,
      R s ρ rs rρ /\
      P rs rρ /\
      exists rt rσ,
        InterStep (impl:=impl) i rs (i, liftUEv ev) rt /\
        IsTraceOfSpec rσ VF /\
        LinRw rρ rσ /\
        R rt rσ t σ.

Lemma spStrongest E VE F VF impl i (R G : Relt E VE F) P ev :
  id ==> R ->
  sp impl i VF R P ev ==> G ->
  Commit VF i impl G P ev (sp impl i VF R P ev).
intros Rid Gsub.
unfold Commit, sp.
intros.
do 2 destruct H.
exists x.
split.
do 2 eexists.
split.
apply Rid.
unfold id.
easy.
split.
easy.
do 2 eexists.
split.
exact H1.
split.
exact H.
split.
easy.
apply Rid.
unfold id.
easy.
split.
apply Gsub.
unfold sp.
do 2 eexists.
split.
apply Rid.
unfold id.
easy.
split.
easy.
do 2 eexists.
split.
exact H1.
split.
exact H.
split.
easy.
apply Rid.
unfold id.
easy.
exists nil.
split.
constructor.
rewrite app_nil_r.
easy.
Qed.

Lemma spStable E VE F VF impl i (R : Relt E VE F) P ev :
  R ->> R ==> R ->
  Stable R (sp impl i VF R P ev).
intros Rtrans.
unfold Stable, stableRelt, sub, subRelt, sp.
split.
intros.
{
  psimpl.
  do 2 eexists.
  split.
  apply Rtrans.
  psplit.
  exact H.
  exact H0.
  split.
  easy.
  do 2 eexists.
  split.
  exact H2.
  split.
  exact H3.
  easy.
}
{
  intros.
  psimpl.
  do 2 eexists.
  split.
  exact H.
  split.
  easy.
  do 2 eexists.
  split.
  exact H2.
  split.
  exact H3.
  split.
  easy.
  apply Rtrans.
  psplit.
  exact H5.
  easy.
}
Qed.

Lemma strongBind {E F VF VE impl i R G P A B} {S : Post E VE F B} {m : E A} {k : A -> Prog E B} :
  id ==> R ->
  R ->> R ==> R ->
  sp impl i VF R P (CallEv m) ==> G ->
  (forall v,
    sp impl i VF R (sp impl i VF R P (CallEv m)) (RetEv m v) ==> G) ->
  (forall v,
    VerifyProg VF i impl R G
      (sp impl i VF R
        (sp impl i VF R P (CallEv m)) (RetEv m v))
      (k v)
      S) ->
  VerifyProg VF i impl R G P (Bind m k) S.
intros Rid Rtrans Gsub1 Gsub2. intros.
apply SafeBind with
  (QI:= sp impl i VF R P (CallEv m))
  (QR:= fun v => sp impl i VF R (sp impl i VF R P (CallEv m)) (RetEv m v)).
apply spStable.
easy.
unfold Stable, stablePost.
intros.
apply spStable.
easy.
apply spStrongest.
easy.
easy.
intros.
split.
apply spStrongest.
easy.
easy.
apply H.
Qed.

Ltac strongBind := eapply strongBind; eauto with rely_lemmas.

Axiom undef : forall a, a.

Lemma weakenPrec E F A VE VF i impl (R : Relt E VE F) G P P' Q (C : Prog E A) :
  VerifyProg VF i impl R G P C Q ->
  P' ==> P ->
  VerifyProg VF i impl R G P' C Q.
intros.
destruct C.
dependent destruction H.
apply SafeBind with (QI:=QI) (QR:=QR).
easy.
easy.
unfold Commit.
intros.
apply H1.
easy.
apply H3.
easy.
easy.
easy.
dependent destruction H.
constructor.
intros.
apply H.
apply H0.
easy.
Admitted.

Theorem soundness {E F} (lay : Layer E F) VF :
  (exists R G P Q, VerifyImpl lay.(USpec) VF R G P lay.(LImpl) Q) ->
  specRefines (overObj lay) VF.
Admitted.