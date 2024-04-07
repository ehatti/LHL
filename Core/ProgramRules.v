From LHL.Core Require Import
  Program
  Specs
  Traces
  Logic
  LogicFacts.

From Coq Require Import
  Program.Equality.


Unset Guard Checking.
Section rules.

Context
  {i : ThreadName}
  {E F : ESig}
  {VE : Spec E}
  {VF : Spec F}
  {R G : Relt VE VF}.

Lemma lemNoOp {A P Q} {C : Prog E A} :
  VerifyProg i R G P C Q ->
  VerifyProg i R G P (NoOp C) Q.
intros.
constructor.
exact H.
Qed.

Lemma lemRet {A P Q} {v : A} :
  (forall s ρ t σ, P s ρ -> Q v s ρ t σ) ->
  VerifyProg i R G P (ret v) Q.
intros.
constructor.
unfold sub, subRelt, id.
intros.
psimpl.
apply H.
easy.
Qed.

Lemma lemCall {A P Q S} {m : E A} :
  Stable R Q ->
  Stable R S ->
  Commit i G P (CallEv m) Q ->
  (forall v, Commit i G (prComp P id ->> Q) (RetEv m v) (S v)) ->
  VerifyProg i R G P (call m) (fun v => Q ->> S v).
intros.
econstructor.
exact H.
exact H0.
unfold Commit, id.
intros.
psimpl.
apply H1.
easy.
easy.
easy.
easy.
split.
apply H2.
constructor.
unfold sub, subRelt, id.
intros.
psimpl.
psplit.
exact H4.
easy.
Qed.

Lemma lemBind {A B P Q S} {C : Prog E A} {k : A -> Prog E B} :
  VerifyProg i R G P C Q ->
  (forall v, VerifyProg i R G (P <<- Q) (k v) S) ->
  VerifyProg i R G P (x <- C; k x) (fun v => Q ->> S v).
intros.
Admitted.

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

Lemma unfoldWhile {x : Prog E bool} {C : Prog E unit} :
  while x C = (t <- x; if t then _ <- C; NoOp (while x C) else ret tt).
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
Set Guard Checking.