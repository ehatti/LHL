From LHL.Core Require Import
  Specs
  Program
  Logic.

From Coq Require Import
  Program.Equality
  Logic.PropExtensionality.

From LHL.Util Require Import
  Tactics.

From Paco Require Import paco.

Inductive paco_safeF {T E F A} {VE : Spec T E} {VF : Spec T F} i (R G : Relt VE VF) (Q : Post VE VF A) (om : F A) (rec : Relt VE VF -> Prog E A -> Prop) : Relt VE VF -> Prog E A -> Prop :=
| SafeReturn v (P : Relt VE VF) P' :
    ReturnStep i G P om v (P' v) ->
    P' v ==> Q v ->
    paco_safeF i R G Q om rec P (Return v)
| SafeBind A (P : Relt VE VF) QI QR (m : E A) k :
    Stable R QI ->
    Stable R QR ->
    Commit i G P (CallEv m) QI ->
    (forall v,
      Commit i G (P ->> QI) (RetEv m v) (QR v) /\
      rec (P ->> QI ->> QR v) (k v)) ->
    paco_safeF i R G Q om rec P (Bind m k)
| SafeNoOp (P : Relt VE VF) QS C :
    Stable R QS ->
    SilentStep i G P QS ->
    rec (P ->> QS) C ->
    paco_safeF i R G Q om rec P (NoOp C)
.

Definition paco_safe {T E F A} {VE : Spec T E} {VF : Spec T F} i (R G P : Relt VE VF) (om : F A) (C : Prog E A) (Q : Post VE VF A) : Prop := paco2 (paco_safeF i R G Q om) bot2 P C.

Lemma safe_monotone {T E F A} {VE : Spec T E} {VF : Spec T F} (i : Name T) (R G : Relt VE VF) (Q : Post VE VF A) (om : F A) :
  monotone2 (paco_safeF i R G Q om).
unfold monotone2. intros.
destruct IN.
econstructor. exact H. easy.
econstructor. exact H. exact H0. easy.
intros. specialize (H2 v).
split. easy.
apply LE. easy.
econstructor. exact H. easy.
apply LE. easy.
Qed.
Hint Resolve safe_monotone : paco.

CoFixpoint paco_eqv_help {T E F A} {m : F A} {VE : Spec T E} {VF : Spec T F} (i : Name T) (R G : Relt VE VF) (Q : Post VE VF A) (P : Relt VE VF) (C : Prog E A) :
  paco_safe i R G P m C Q -> SafeProg i R G P m C Q.
intros.
punfold H.
dependent destruction H.
econstructor. exact H. easy.
econstructor. exact H. exact H0. easy.
intros. specialize (H2 v). destruct_all.
split. easy.
destruct H3.
apply paco_eqv_help. easy.
destruct H3.
destruct H1.
econstructor. exact H. easy.
apply paco_eqv_help. easy.
destruct H1.
Qed.

Lemma paco_eqv {T E F A} {VE : Spec T E} {VF : Spec T F} (i : Name T) {m : F A} (R G : Relt VE VF) (Q : Post VE VF A) (P : Relt VE VF) (C : Prog E A):
  SafeProg i R G P m C Q = paco_safe i R G P m C Q.
apply propositional_extensionality.
split; intros.
{
  generalize dependent C. generalize dependent P.
  pcofix rec. intros. pfold.
  destruct H0.
  econstructor. exact H. easy.
  econstructor. exact H. exact H0. easy.
  intros. specialize (H2 v). destruct_all.
  split. easy.
  right. apply rec. easy.
  econstructor. exact H. easy.
  right. apply rec. easy.
}
apply paco_eqv_help. easy.
Qed.
