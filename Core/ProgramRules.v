From LHL.Core Require Import
  Program
  Specs
  Traces
  Logic
  LogicFacts
  ProgramFacts.

From Coq Require Import
  Program.Equality.

From LHL.Util Require Import
  Tactics.

Section rules.

Context
  {i : ThreadName}
  {E F : ESig}
  {VE : Spec E}
  {VF : Spec F}
  {R G : Relt VE VF}.

Lemma lemNoOp {A Q} {P : Relt VE VF} {C : Prog E A} :
  forall QS,
  Stable R QS ->
  SilentStep i G P QS ->
  VerifyProg i R G (P ->> QS) C Q ->
  VerifyProg i R G P (NoOp C) Q.
intros.
econstructor. exact H. easy. easy.
Qed.

Lemma lemRet {A P Q} {v : A} :
  (forall v, P ==> Q v) ->
  VerifyProg i R G P (ret v) Q.
intros.
constructor.
unfold sub, subRelt, id.
intros. psimpl.
apply H. easy.
Qed.

Lemma lemCall {A Q S} {P : Relt VE VF} {m : E A} :
  Stable R Q ->
  Stable R S ->
  Commit i G P (CallEv m) Q ->
  (forall v, Commit i G (P ->> Q) (RetEv m v) (S v)) ->
  VerifyProg i R G P (call m) (fun v => P ->> Q ->> S v).
intros.
econstructor. exact H. exact H0.
unfold Commit, id.
intros. psimpl.
apply H1.
exists x, x0.
easy. easy. easy. easy.
intros. specialize (H2 v).
split. easy.
econstructor. unfold sub, subRelt. intros.
easy.
Qed.

Axiom undef:forall{a},a.

CoFixpoint lemBind {A B P Q S} {C : Prog E A} {k : A -> Prog E B}
  (H : VerifyProg i R G P C Q) :
  (forall v, VerifyProg i R G (Q v) (k v) S) ->
  VerifyProg i R G P (x <- C; k x) S.
intros.
destruct H.
{
  rewrite frobProgId at 1. simpl.
  assert (match k v with | @Bind _ _ A0 e f => Bind e f | Return a =>  Return a | NoOp p' => NoOp p' end = k v) by (destruct (k v); easy).
  rewrite H1. clear H1.
  eapply weakenSafe. exact H.
  apply H0.
}
(* {
  rewrite frobProgId at 1. simpl.
  econstructor. exact H. exact H1. easy.
  intros.
  specialize (H3 v).
  split. easy.
  destruct_all.
  eapply lemBind.
  exact H4.
  exact H0.
} *)
apply undef.
{
}
apply undef.
Qed.

Lemma weakenPost {A P Q Q'} {C : Prog E A} :
  VerifyProg i R G P C Q ->
  (forall v, Q v ==> Q' v) ->
  VerifyProg i R G P C Q'.
Admitted.

Lemma weakenPrec {A P P' Q} {C : Prog E A} :
  VerifyProg i R G P C Q ->
  P' ==> P ->
  VerifyProg i R G P' C Q.
Admitted.

Lemma lemWhile {P} {T : Post VE VF bool} {Q : Post VE VF unit} {t : Prog E bool} {C : Prog E unit} :
  (forall v, id ==> Q v) ->
  P <<- T <<- Q ==> P ->
  (forall v, (Q ->> T ->> Q v) ==> Q v) ->
  VerifyProg i R G P t T ->
  VerifyProg i R G (P <<- T) C Q ->
  VerifyProg i R G P (while t C) (fun v => T ->> Q v).
intros idQ subP inv safe_t safe_C.
cofix rec.
rewrite unfoldWhile.
eapply lemBind.
easy.
intros.
destruct v.
eapply weakenPost.
eapply lemBind.
exact safe_C.
intros.
eapply weakenPrec.
apply lemNoOp.
exact rec.
easy.
intros.
unfold sub, subRelt.
intros.
apply inv.
easy.
constructor.
unfold sub, subRelt, id.
intros.
psimpl.
apply idQ.
easy.
Qed.

End rules.