From Coq Require Import
  Lists.List.
Import ListNotations.

From LHL.Core Require Import
  Program
  LogicFacts
  Traces
  Specs
  Logic.

From LHL.Util Require Import
  Util
  TransUtil.

Variant VisPossStep {T F} {VF : Spec T F} : Poss VF -> ThreadEvent T F -> Poss VF -> Prop :=
| VPCommitCall i A (m : F A) (x y : Poss VF) :
  VF.(Step) x.(PState) (i, CallEv m) y.(PState) ->
  x.(PCalls) i = CallPoss m ->
  y.(PCalls) i = CallDone m ->
  x.(PRets) i = RetIdle ->
  y.(PRets) i = RetIdle ->
  VisPossStep x (i, CallEv m) y
| VPCommitRet i A (m : F A) v (x y : Poss VF) :
  VF.(Step) x.(PState) (i, RetEv m v) y.(PState) ->
  x.(PCalls) i = CallDone m ->
  y.(PCalls) i = CallDone m ->
  x.(PRets) i = RetIdle ->
  y.(PRets) i = RetPoss m v ->
  VisPossStep x (i, RetEv m v) y.

Inductive VisPossSteps {T F} {VF : Spec T F} : Poss VF -> Trace (ThreadEvent T F) -> Poss VF -> Prop :=
| VRefl x :
    VisPossSteps x [] x
| VStep x y z i e p :
    VisPossStep x (i, e) y ->
    differ_pointwise (PCalls x) (PCalls y) i ->
    differ_pointwise (PRets x) (PRets y) i ->
    VisPossSteps y p z ->
    VisPossSteps x ((i, e) :: p) z.

Lemma erase_vis {T F} {VF : Spec T F} :
  forall (x y : Poss VF) p,
  VisPossSteps x p y ->
  PossSteps x y.
intros. induction H. constructor.
cut (PossStep i x y).
{
  intros. econstructor.
  exact H3.
  intros. now rewrite H0.
  intros. now rewrite H1.
  easy.
}
clear - H. ddestruct H.
{
  eapply PCommitCall.
  exact H. all: easy.
}
{
  eapply PCommitRet.
  exact H. all: easy.
}
Qed.

Definition comInvPoss {T F} {VF : Spec T F} i (ρ : Poss VF) {A} (m : F A) (s : State VF) : Poss VF := {|
  PState := s;
  PCalls j := if i =? j then CallDone m else PCalls ρ j;
  PRets j := PRets ρ j
|}.

Definition comRetPoss {T F} {VF : Spec T F} i (ρ : Poss VF) {A} (m : F A) (s : State VF) v : Poss VF := {|
  PState := s;
  PCalls := PCalls ρ;
  PRets j := if i =? j then RetPoss m v else PRets ρ j
|}.


Lemma psteps_trans {T F} {VF : Spec T F} :
  forall (x y z : Poss VF) p q,
  VisPossSteps x p y ->
  VisPossSteps y q z ->
  VisPossSteps x (p ++ q) z.
intros. induction H. easy.
eapply VStep with (i:=i).
4: now apply IHVisPossSteps.
all: easy.
Qed.

Lemma retStep {T F} {VF : Spec T F} :
  forall i (x z : Poss VF) p A (m : F A) v (y : State VF),
  VisPossSteps x p z ->
  (PCalls z i = CallDone m /\
   PRets z i = RetIdle /\
   VF.(Step) (PState z) (i, RetEv m v) y) ->
  VisPossSteps x (p ++ [(i, RetEv m v)]) (comRetPoss i z m y v).
intros.
eapply psteps_trans.
exact H.
eapply VStep with
  (i:=i). 4: constructor.
psimpl.
eapply VPCommitRet with
  (m:=m) (v:=v).
all: try easy.
cbn. now rewrite eqb_id.
apply differ_pointwise_trivial.
Qed.

Lemma callStep {T F} {VF : Spec T F} :
  forall i (x z : Poss VF) p A (m : F A) (y : State VF),
  VisPossSteps x p z ->
  (PCalls z i = CallPoss m /\
   PRets z i = RetIdle /\
   VF.(Step) (PState z) (i, CallEv m) y) ->
  VisPossSteps x (p ++ [(i, CallEv m)]) (comInvPoss i z m y).
intros.
eapply psteps_trans.
exact H.
eapply VStep with
  (i:=i). 4: constructor.
psimpl.
eapply VPCommitCall with
  (m:=m).
all: try easy.
cbn. now rewrite eqb_id.
apply differ_pointwise_trivial.
Qed.

Record Waiting {T A} {F : ESig} {VF : Spec T F} (i : Name T) (m : F A)
  (x : Poss VF)
:= {
  call_waiting : PCalls x i = CallPoss m;
  ret_waiting : PRets x i = RetIdle;
}.

Record Done {T A} {F : ESig} {VF : Spec T F} (i : Name T) (m : F A) (v : A)
  (x : Poss VF)
:= {
  call_done : PCalls x i = CallDone m;
  ret_done : PRets x i = RetPoss m v
}.

Notation UnderStep s i e t := (PointStep UnderThreadStep s (i, Some e) t).

Ltac destruct_big_steps :=
repeat (match goal with
| [ H : VisPossSteps ?x ?p ?y |- _ ] =>
    ddestruct H
| [ H : VisPossStep ?x ?e ?y |- _ ] =>
    ddestruct H
| [ H : UnderStep ?s ?i ?e ?t |- _] =>
    ddestruct H
| [ H : UnderThreadStep ?s ?e ?t |- _ ] =>
    ddestruct H
end; cbn in *).