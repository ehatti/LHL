From LHL.Core Require Import
  Program
  Specs
  Logic
  LogicFacts
  Tensor
  Traces
  SingConds
  VisPoss
  UBLayer
  ProgramRules
  Linearizability.

From LHL.Util Require Import
  TransUtil
  Tactics
  Util.

From LHL.Examples Require Import
  ArraySpec.

Definition UnitSig : ESig :=
    fun _ => Empty_set.

Program Definition unitSpec {T} : Spec T UnitSig := {|
  State := unit;
  Step _ e _ := False;
  Init := tt
|}.

Next Obligation.
ddestruct H.
constructor.
easy.
Qed.

Fixpoint E (U : ESig) N :=
  match N with
  | 0 => UnitSig
  | S N => U |+| E U N
  end.

Fixpoint VE {T U} (V : Spec T U) N : Spec T (E U N) :=
  match N with
  | 0 => unitSpec
  | S N => tensorSpec V (VE V N)
  end.

Definition F U N := ArraySig U N.

Definition VF {T U} (V : Spec T U) N : Spec T (F U N) :=
  arraySpec N V.

From Equations Require Import Equations.
Require Import Lia.

Equations getIndex {U N R} (i : Index N) (m : U R) : E U N R :=
getIndex (N:= S N) (@exist _ _ 0 p) m := inl m;
getIndex (N:= S N) (@exist _ _ (S i) p) m := inr (getIndex (@exist _ _ i _) m);
getIndex (N:= 0) (@exist _ _ i p) m := _.

Next Obligation. lia. Qed.
Next Obligation. lia. Qed.

Section indexVE.

Context {T U} {V : Spec T U}.

Equations indexVE {N} (i : Index N) (s : (VE V N).(State))
  : V.(State) by wf (proj1_sig i) lt :=
indexVE (N:= S N) (@exist _ _ 0 p) s := LState s;
indexVE (N:= S N) (@exist _ _ (S i) p) s := indexVE (@exist _ _ i _) s;
indexVE (N:= 0) (@exist _ _ i p) s := _.

Next Obligation. lia. Qed.
Next Obligation. lia. Qed.

Definition index {U N R} (i : Index N) (m : U R) : Prog (E U N) R :=
  Bind (getIndex i m)
  Return.

Definition arrayImpl {U N} : Impl (E U N) (ArraySig U N) :=
  fun _ m => match m with
  | At i m => index i m
  end.

Variant StRel {T U} {V : Spec T U} {N} :
  ThreadState (E U N) (F U N) -> PCall (F U N) -> PRet (F U N) -> Prop :=
| StIdle :
  StRel Idle CallIdle RetIdle
| StOCall i R (m : U R) :
  StRel (Cont (At i m) (index i m)) (CallPoss (At i m)) RetIdle
| StUCall i R (m : U R) :
  StRel (UCall (At i m) (getIndex i m) Return) (CallDone (At i m)) RetIdle
| StURet i R (m : U R) v :
  StRel (Cont (At i m) (Return v)) (CallDone (At i m)) (RetPoss (At i m) v).

Record Inv {T U} {V : Spec T U} {N}
  (s : InterState (F U N) (VE V N)) (ρ : Poss (VF V N))
:= {
  st_cons : forall i, PState ρ i = indexVE i (snd s)
}.

Theorem arrayCorrect :
  VerifyImpl