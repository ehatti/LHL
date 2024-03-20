From LHL.Core Require Import
  Program
  Specs
  Syntax
  Logic
  LogicFacts
  Traces.

From Coq Require Import
  Program.Equality.

From Paco Require Import
  paco.

Section lemmas.

Context
  {E F : ESig}
  {VE : Spec E} {VF : Spec F}
  {i : ThreadName}
  {impl : Impl E F}
  {R G : Relt VE VF}.

Lemma lemRet {A P Q} {v : A} :
  prComp P R ==> Q v ->
  VerifyProg i impl R G P (ret v) Q.
intros.
constructor.
easy.
Qed.

Lemma evalBindNoOp {A B} (C : Prog E A) (k : A -> Prog E B) :
  bind (NoOp C) k = NoOp (bind C k).
Admitted.

Lemma evalBindRet {A B} (v : A) (k : A -> Prog E B) :
  bind (ret v) k = k v.
Admitted.

Lemma evalBindBind {A B C} (m : E A) (k1 : A -> Prog E B) (k2 : B -> Prog E C) :
  bind (Bind m k1) k2 = Bind m (fun v => bind (k1 v) k2).
Admitted.

Lemma lemBind {A B P Q S} (C : Prog E A) (k : A -> Prog E B) :
  VerifyProg i impl R G P C Q ->
  (forall v, VerifyProg i impl R G Q (k v) S) ->
  VerifyProg i impl R G P (bind C k) S.
Admitted.

Lemma lemCall {A} {P : Prec VE VF} (m : E A) :
  forall (Q : Post VE VF A),
  prComp (prComp P R) (sp (CallEv m) impl i R) ==> G ->
  (forall v,   
    prComp (prComp P R ->> sp (CallEv m) impl i R) (sp (RetEv m v) impl i R) ==> G) ->
  (forall v,
    prComp P R ->> sp (CallEv m) impl i R ->> sp (RetEv m v) impl i R ==> Q v) ->
  VerifyProg i impl R G P (call m) Q.
intros.
eapply SafeBind.
eapply spStable.
unfold Stable, stablePost.
intros.
eapply spStable.
eapply spStrong.
easy.
intros.
specialize (H0 v).
specialize (H1 v).
split.
eapply spStrong.
easy.
constructor.
easy.
Qed.

End lemmas.