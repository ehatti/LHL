From LHL.Core Require Import
  Program
  Specs
  Traces
  Linearizability.

From Coq Require Import
  Lists.List
  Logic.FunctionalExtensionality
  Logic.PropExtensionality
  Relations.Relation_Operators.

From LHL.Util Require Import
  Util.

Variant PCall {F : ESig} :=
| CallIdle
| CallPoss {A} (m : F A)
| CallDone {A} (m : F A) (* committed *).
Arguments PCall : clear implicits.

Variant PRet {F : ESig} :=
| RetIdle
| RetPoss {A} (m : F A) (v : A).
Arguments PRet : clear implicits.

Record Poss {T F} {VF : Spec T F} := MkPoss {
  PState : VF.(State);
  PCalls : Name T -> PCall F;
  PRets : Name T -> PRet F
}.
Arguments Poss {T F} VF.

Definition PossSet {T F} (VF : Spec T F) :=
  Poss VF -> Prop.

Definition Prec {T E F} (VE : Spec T E) (VF : Spec T F) :=
  InterState F VE ->
  PossSet VF ->
  Prop.

Definition Relt {T E F} (VE : Spec T E) (VF : Spec T F) :=
  InterState F VE ->
  PossSet VF ->
  InterState F VE ->
  PossSet VF ->
  Prop.

Definition Post {T E F} (VE : Spec T E) (VF : Spec T F) A :=
  A -> Relt VE VF.

Inductive RTC {T E F} {VE : Spec T E} {VF : Spec T F} (R : Relt VE VF) : Relt VE VF :=
| RTCRefl s ρ : RTC R s ρ s ρ
| RTCStep s ρ t σ r τ :
    R s ρ t σ ->
    RTC R t σ r τ ->
    RTC R s ρ r τ.

Definition prComp {T E F} {VE : Spec T E} {VF : Spec T F} (P : Prec VE VF) (R : Relt VE VF) : Relt VE VF :=
  fun s ρ t σ => P s ρ /\ R s ρ t σ.

Definition ReltToPrec {T E F} {VE : Spec T E} {VF : Spec T F} (R : Relt VE VF) : Prec VE VF :=
  fun t σ => exists s ρ, R s ρ t σ.
Coercion ReltToPrec : Relt >-> Prec.

Definition PrecToRelt {T E F} {VE : Spec T E} {VF : Spec T F} (P : Prec VE VF) : Relt VE VF :=
  fun s ρ t σ =>
    P s ρ /\
    s = t /\
    ρ = σ.

Definition PostToRelt {T E F} {VE : Spec T E} {VF : Spec T F} {A} (Q : Post VE VF A) : Relt VE VF :=
  fun s ρ t σ => exists v, Q v s ρ t σ.
Coercion PostToRelt : Post >-> Relt.

Definition PrecCompose {T E F} {VE : Spec T E} {VF : Spec T F} (P : Prec VE VF) (R : Relt VE VF) : Prec VE VF :=
  fun t σ => exists s ρ, P s ρ /\ R s ρ t σ.

Notation "R <<- G" := (PrecCompose R G) (left associativity, at level 37).

Definition ReltCompose {T E F} {VE : Spec T E} {VF : Spec T F} (R G : Relt VE VF) : Relt VE VF :=
  fun s ρ r τ => exists t σ, R s ρ t σ /\ G t σ r τ.
Notation "R ->> G" := (ReltCompose R G) (right associativity, at level 39).

Class HasSub A :=
  sub : A -> A -> Prop.
Notation "P ==> Q" := (sub P Q) (right associativity, at level 41).

Global Instance subPrec {T E F} {VE : Spec T E} {VF : Spec T F} : HasSub (Prec VE VF) :=
  fun P Q => forall s ρ, P s ρ -> Q s ρ.

Global Instance subRelt {T E F} {VE : Spec T E} {VF : Spec T F} : HasSub (Relt VE VF) :=
  fun P Q => forall s ρ t σ, P s ρ t σ -> Q s ρ t σ.

Class HasStable {T E F} {VE : Spec T E} {VF : Spec T F} A :=
  Stable : Relt VE VF -> A -> Prop.

Global Instance stableRelt {T E F} {VE : Spec T E} {VF : Spec T F} : HasStable (Relt VE VF) :=
  fun R Q => (Q ->> R ==> Q).

Global Instance stablePrec {T E F} {VE : Spec T E} {VF : Spec T F} : HasStable (Prec VE VF) :=
  fun R P => P <<- R ==> P.

Global Instance stablePost {T E F} {VE : Spec T E} {VF : Spec T F} {A} : HasStable (Post VE VF A) :=
  fun R Q => forall v, stableRelt R (Q v).

Definition id {T E F VE VF} : @Relt T E F VE VF :=
  fun s ρ t σ => s = t /\ ρ = σ.

Definition ptop {T E F VE VF} : @Prec T E F VE VF :=
  fun _ _ => True.
Definition rtop {T E F VE VF} : @Relt T E F VE VF :=
  fun _ _ _ _ => True.

Variant PossStep {T F} {VF : Spec T F} i (ρ σ : Poss VF) : Prop :=
| PCommitCall A (m : F A) :
  VF.(Step) ρ.(PState) (i, CallEv m) σ.(PState) ->
  ρ.(PCalls) i = CallPoss m ->
  σ.(PCalls) i = CallDone m ->
  ρ.(PRets) i = RetIdle ->
  σ.(PRets) i = RetIdle ->
  PossStep i ρ σ
| PCommitRet A (m : F A) v :
  VF.(Step) ρ.(PState) (i, RetEv m v) σ.(PState) ->
  ρ.(PCalls) i = CallDone m ->
  σ.(PCalls) i = CallDone m ->
  ρ.(PRets) i = RetIdle ->
  σ.(PRets) i = RetPoss m v ->
  PossStep i ρ σ.

Inductive PossSteps {T F} {VF : Spec T F} : Poss VF -> Poss VF -> Prop :=
| PossStepsRefl ρ :
    PossSteps ρ ρ
| PossStepsStep i ρ σ τ :
    PossStep i ρ σ ->
    (forall j, i <> j -> PCalls ρ j = PCalls σ j) ->
    (forall j, i <> j -> PRets ρ j = PRets σ j) ->
    PossSteps σ τ ->
    PossSteps ρ τ.



Definition Commit {T E F} {VE : Spec T E} {VF : Spec T F} i
  (G : Relt VE VF)
  (P : Prec VE VF)
  (ev : Event E)
  (Q : Relt VE VF) :=
  forall s ρs t,
  P s ρs ->
  Util.differ_pointwise (fst s) (fst t) i ->
  UnderThreadStep (fst s i) (Some ev) (fst t i) ->
  VE.(Step) (snd s) (i, ev) (snd t) ->
    exists σs,
      (exists σ, σs σ) /\
      (forall σ,
        σs σ ->
        exists ρ,
          ρs ρ /\
          PossSteps ρ σ) /\
      Q s ρs t σs /\
      G s ρs t σs.

Definition SilentStep {T E F} {VE : Spec T E} {VF : Spec T F} i
  (G : Relt VE VF)
  (P : Prec VE VF)
  (Q : Relt VE VF) :=
  forall s ths ρs tht,
  P (ths, s) ρs ->
  Util.differ_pointwise ths tht i ->
  UnderThreadStep (ths i) None (tht i) ->
    Q (ths, s) ρs (tht, s) ρs /\
    G (ths, s) ρs (tht, s) ρs.

Definition mapRetPoss {T F VF A} i (m : F A) v (ρ σ : @Poss T F VF) :=
  σ.(PCalls) i = CallIdle /\ ρ.(PCalls) i = CallDone m /\
  σ.(PRets) i = RetIdle /\ ρ.(PRets) i = RetPoss m v /\
  Util.differ_pointwise ρ.(PCalls) σ.(PCalls) i /\
  Util.differ_pointwise ρ.(PRets) σ.(PRets) i /\
  σ.(PState) = ρ.(PState).

Definition Returned {T E F VE VF} (i : Name T) {A} (m : F A) v : @Prec T E F VE VF :=
  fun s ρs =>
    fst s i = Cont m (Return v) ->
      forall ρ, ρs ρ ->
        ρ.(PRets) i = RetPoss m v /\
        ρ.(PCalls) i = CallDone m.

Definition ReturnStep {T E F} {VE : Spec T E} {VF : Spec T F} i
  (G : Relt VE VF)
  (P : Prec VE VF)
  {A} (m : F A) v
  (Q : Relt VE VF) :=
  forall s ρs,
  P s ρs ->
  fst s i = Cont m (Return v) ->
  exists σs,
    (exists σ, σs σ) /\
    (forall σ,
      σs σ ->
      exists ρ,
        ρs ρ /\
        PossSteps ρ σ) /\
    (forall σ, σs σ ->
      σ.(PRets) i = RetPoss m v /\
      σ.(PCalls) i = CallDone m) /\
    Q s ρs
      (fun j => if i =? j then Idle else fst s j, snd s)
      (fun τ => exists σ, σs σ /\ mapRetPoss i m v σ τ) /\
    G s ρs
      (fun j => if i =? j then Idle else fst s j, snd s)
      (fun τ => exists σ, σs σ /\ mapRetPoss i m v σ τ).

Definition initPoss {T F VF} : @Poss T F VF := {|
  PState := VF.(Init);
  PCalls _ := CallIdle;
  PRets _ := RetIdle;
|}.

CoInductive SafeProg {T E F} {VE : Spec T E} {VF : Spec T F} i : Relt VE VF -> Relt VE VF -> forall (A : Type), Relt VE VF -> Prog E A -> Post VE VF A -> Prop :=
| SafeReturn A v R G (P : Relt VE VF) Q :
    P ==> Q v ->
    SafeProg i R G A P (Return v) Q
| SafeBind A B R G (P : Relt VE VF) QI QR Q (m : E A) k :
    Stable R QI ->
    Stable R QR ->
    Commit i G P (CallEv m) QI ->
    (forall v,
      Commit i G ((P ->> QI)) (RetEv m v) (QR v) /\
      SafeProg i R G B (P ->> QI ->> QR v) (k v) Q) ->
    SafeProg i R G B P (Bind m k) Q
| SafeNoOp R G A (P : Relt VE VF) QS C Q :
    Stable R QS ->
    SilentStep i G P QS ->
    SafeProg i R G A (P ->> QS) C Q ->
    SafeProg i R G A P (NoOp C) Q
.

Arguments SafeProg {T E F VE VF} i R G {A} P C Q.

Definition TIdle {T E F VE VF} (i : Name T) : @Prec T E F VE VF :=
  fun s ρs =>
    fst s i = Idle /\
    forall ρ, ρs ρ ->
      ρ.(PCalls) i = CallIdle /\
      ρ.(PRets) i = RetIdle.

Definition mapPoss {T F} {VF : Spec T F} (ρs σs : PossSet VF) (P : Poss VF -> Poss VF -> Prop) :=
  (forall ρ, ρs ρ -> exists σ, σs σ /\ P ρ σ) /\
  (forall σ, σs σ -> exists ρ, ρs ρ /\ P ρ σ).

Definition mapInvPoss {T F VF A} i (m : F A) (ρ σ : @Poss T F VF) :=
  ρ.(PCalls) i = CallIdle /\ σ.(PCalls) i = CallPoss m /\
  ρ.(PRets) i = RetIdle /\ σ.(PRets) i = RetIdle /\
  Util.differ_pointwise ρ.(PCalls) σ.(PCalls) i /\
  Util.differ_pointwise ρ.(PRets) σ.(PRets) i /\
  ρ.(PState) = σ.(PState).

Definition TInvoke {T E F VE VF} impl (i : Name T) Ret (m : F Ret) : @Relt T E F VE VF :=
  fun s ρs t σs =>
    TIdle i s ρs /\
    InterOStep impl i (fst s) (CallEv m) (fst t) /\
    snd s = snd t /\
    σs = (fun σ =>
      exists ρ, ρs ρ /\
        σ.(PState) = ρ.(PState) /\
        σ.(PCalls) i = CallPoss m /\
        σ.(PRets) i = RetIdle /\
        Util.differ_pointwise ρ.(PCalls) σ.(PCalls) i /\
        Util.differ_pointwise ρ.(PRets) σ.(PRets) i).

Definition InvokeAny {T E F VE VF} impl i : @Relt T E F VE VF :=
  fun s ρ t σ =>
    exists Ret (m : F Ret), TInvoke impl i Ret m s ρ t σ.

Definition TReturn {T E F VE VF} (impl : Impl E F) (i : Name T) {Ret} (m : F Ret) v : @Relt T E F VE VF :=
  fun s ρs t σs =>
    Returned i m v s ρs /\
    InterOStep impl i (fst s) (RetEv m v) (fst t) /\
    snd s = snd t /\
    σs = (fun σ => exists ρ, ρs ρ /\ mapRetPoss i m v ρ σ).

Definition ReturnAny {T E F VE VF} impl i : @Relt T E F VE VF :=
  fun s ρ t σ =>
    exists Ret (m : F Ret) v, TReturn impl i m v s ρ t σ.

Definition VerifyProg {T E F VE VF A} i
  (R G : @Relt T E F VE VF)
  (P : Relt VE VF)
  (C : Prog E A)
  (Q : Post VE VF A)
  : Prop :=
  SafeProg i R G P C Q.

Record VerifyImpl
  {T E F}
  {VE : Spec T E}
  {VF : Spec T F}
  {R G : Name T -> Relt VE VF}
  {P : Name T -> forall Ret, F Ret -> Prec VE VF}
  {impl : Impl E F}
  {Q : Name T -> forall Ret, F Ret -> Post VE VF Ret}
  {Cs : Name T -> forall Ret, F Ret -> Post VE VF Ret}
: Prop := {
  R_refl : forall i s ρ,
    R i s ρ s ρ;
  R_trans : forall i,
    R i ->> R i ==> R i;
  G_in_R : forall i j,
    i <> j -> G i ==> R j;
  Inv_in_R : forall i j,
    i <> j -> InvokeAny impl i ==> R j;
  Ret_in_R : forall i j,
    i <> j -> ReturnAny impl i ==> R j;
  init_in_P : forall i A m,
    P i A m (allIdle, VE.(Init)) (eq initPoss);
  P_stable : forall i A m,
    Stable (R i) (P i A m);
  switch_code : forall i A m1 B m2 v,
    prComp (P i _ m1) (Q i A m1 v) <<- Cs i A m1 v ==> P i B m2;
  all_verified : forall i A m,
    VerifyProg i (R i) (G i)
      (prComp (P i A m) (TInvoke impl i _ m) ->> R i)
      (impl _ m)
      (Q i A m);
  all_return : forall i A (m : F A) v,
    ReturnStep i (G i) (Q i A m v) m v (Cs i A m v)
}.
Arguments VerifyImpl {T E F} VE VF R G P impl Q.