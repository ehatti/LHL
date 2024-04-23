From LHL.Core Require Import
  Program
  Specs
  Traces
  Linearizability.
From Coq Require Import
  Lists.List
  Init.Nat
  Logic.FunctionalExtensionality
  Logic.PropExtensionality
  Relations.Relation_Operators.

Record Poss {F} {VF : Spec F} := MkPoss {
  PState : VF.(State);
  PCalls : ThreadName -> option {A : Type & F A};
  PRets : ThreadName -> option {A : Type & A}
}.
Arguments Poss {F} VF.

Definition PossSet {F} (VF : Spec F) :=
  Poss VF -> Prop.

Definition Prec {E F} (VE : Spec E) (VF : Spec F) :=
  @InterState E F VE ->
  PossSet VF ->
  Prop.

Definition Relt {E F} (VE : Spec E) (VF : Spec F) :=
  @InterState E F VE ->
  PossSet VF ->
  @InterState E F VE ->
  PossSet VF ->
  Prop.

Definition Post {E F} (VE : Spec E) (VF : Spec F) A :=
  A -> Relt VE VF.

Definition StRelt {E} (VE : Spec E) F :=
  @InterState E F VE ->
  @InterState E F VE ->
  Prop.

Inductive RTC {E F} {VE : Spec E} {VF : Spec F} (R : Relt VE VF) : Relt VE VF :=
| RTCRefl s ρ : RTC R s ρ s ρ
| RTCStep s ρ t σ r τ :
    R s ρ t σ ->
    RTC R t σ r τ ->
    RTC R s ρ r τ.

Definition prComp {E F} {VE : Spec E} {VF : Spec F} (P : Prec VE VF) (R : Relt VE VF) : Relt VE VF :=
  fun s ρ t σ => P s ρ /\ R s ρ t σ.

Definition ReltToPrec {E F} {VE : Spec E} {VF : Spec F} (R : Relt VE VF) : Prec VE VF :=
  fun t σ => exists s ρ, R s ρ t σ.
Coercion ReltToPrec : Relt >-> Prec.

Definition PrecToRelt {E F} {VE : Spec E} {VF : Spec F} (P : Prec VE VF) : Relt VE VF :=
  fun s ρ t σ =>
    P s ρ /\
    s = t /\
    ρ = σ.

Definition PostToRelt {E F} {VE : Spec E} {VF : Spec F} {A} (Q : Post VE VF A) : Relt VE VF :=
  fun s ρ t σ => exists v, Q v s ρ t σ.
Coercion PostToRelt : Post >-> Relt.

Definition StReltToRelt {E F} {VE : Spec E} {VF : Spec F} (Q : StRelt VE F) : Relt VE VF :=
  fun s ρ t σ =>
    Q s t /\
    ρ = σ.
Coercion StReltToRelt : StRelt >-> Relt.

Definition PrecCompose {E F} {VE : Spec E} {VF : Spec F} (P : Prec VE VF) (R : Relt VE VF) : Prec VE VF :=
  fun t σ => exists s ρ, P s ρ /\ R s ρ t σ.

Notation "R <<- G" := (PrecCompose R G) (left associativity, at level 37).

Definition ReltCompose {E F} {VE : Spec E} {VF : Spec F} (R G : Relt VE VF) : Relt VE VF :=
  fun s ρ r τ => exists t σ, R s ρ t σ /\ G t σ r τ.
Notation "R ->> G" := (ReltCompose R G) (right associativity, at level 39).

Class HasSub A :=
  sub : A -> A -> Prop.
Notation "P ==> Q" := (sub P Q) (right associativity, at level 41).

Global Instance subPrec {E F} {VE : Spec E} {VF : Spec F} : HasSub (Prec VE VF) :=
  fun P Q => forall s ρ, P s ρ -> Q s ρ.

Global Instance subRelt {E F} {VE : Spec E} {VF : Spec F} : HasSub (Relt VE VF) :=
  fun P Q => forall s ρ t σ, P s ρ t σ -> Q s ρ t σ.

Class HasStable {E F} {VE : Spec E} {VF : Spec F} A :=
  Stable : Relt VE VF -> A -> Prop.

Global Instance stableRelt {E F} {VE : Spec E} {VF : Spec F} : HasStable (Relt VE VF) :=
  fun R Q => (R ->> Q ==> Q) /\ (Q ->> R ==> Q).

Global Instance stablePrec {E F} {VE : Spec E} {VF : Spec F} : HasStable (Prec VE VF) :=
  fun R P => P <<- R ==> P.

Global Instance stablePost {E F} {VE : Spec E} {VF : Spec F} {A} : HasStable (Post VE VF A) :=
  fun R Q => forall v, stableRelt R (Q v).

Definition id {E F VE VF} : @Relt E F VE VF :=
  fun s ρ t σ => s = t /\ ρ = σ.

Definition ptop {E F VE VF} : @Prec E F VE VF :=
  fun _ _ => True.
Definition rtop {E F VE VF} : @Relt E F VE VF :=
  fun _ _ _ _ => True.

Variant PossStep {F} {VF : Spec F} (ρ σ : Poss VF) : Prop :=
| PCommitCall i A (m : F A) :
  VF.(Step) ρ.(PState) (i, CallEv m) σ.(PState) ->
  ρ.(PCalls) i = Some (existT _ A m) /\
  σ.(PCalls) i = None ->
  σ.(PRets) = ρ.(PRets) ->
  PossStep ρ σ
| PCommitRet i A (m : F A) v :
  VF.(Step) ρ.(PState) (i, RetEv m v) σ.(PState) ->
  σ.(PCalls) = ρ.(PCalls) ->
  ρ.(PRets) i = None ->
  σ.(PRets) i = Some (existT _ A v) ->
  PossStep ρ σ.

Definition PossSteps {F} {VF : Spec F} (ρ σ : Poss VF) : Prop :=
  clos_refl_trans _ PossStep ρ σ.

Definition Commit {E F} {VE : Spec E} {VF : Spec F} i
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
      (forall σ,
        σs σ ->
        exists ρ,
          ρs ρ /\
          PossSteps ρ σ) /\
      Q s ρs t σs /\
      G s ρs t σs.

CoInductive SafeProg {E F} {VE : Spec E} {VF : Spec F} i : Relt VE VF -> Relt VE VF -> forall (A : Type), Relt VE VF -> Prog E A -> Post VE VF A -> Prop :=
| SafeReturn A v R G P Q :
    P ==> Q v ->
    SafeProg i R G A P (Return v) Q
| SafeBind A B R G (P : Relt VE VF) QI QR Q (m : E A) k :
    Stable R QI ->
    Stable R QR ->
    Commit i G P (CallEv m) QI ->
    (forall v,
      Commit i G (P ->> QI) (RetEv m v) (QR v) /\
      SafeProg i R G B (P ->> QI ->> QR v) (k v) Q) ->
    SafeProg i R G B P (Bind m k) Q
| SafeNoOp R G A P C Q :
    SafeProg i R G A P C Q ->
    SafeProg i R G A P (NoOp C) Q
.

Arguments SafeProg {E F VE VF} i R G {A} P C Q.

Definition VerifyProg {E F VE VF A} i
  (R G : @Relt E F VE VF)
  (P : Prec VE VF)
  (C : Prog E A)
  (Q : Post VE VF A)
  : Prop :=
  SafeProg i R G (prComp P id) C Q.

Definition TIdle {E F VE VF} (i : ThreadName) : @Prec E F VE VF :=
  fun s ρs =>
    fst s i = Idle /\
    forall ρ,
      ρs ρ ->
      ρ.(PCalls) i = None /\
      ρ.(PRets) i = None.

Definition TInvoke {E F VE VF} impl (i : ThreadName) Ret (m : F Ret) : @Relt E F VE VF :=
  fun s ρs t σs =>
    TIdle i s ρs /\
    InterOStep impl i (fst s) (CallEv m) (fst t) /\
    (forall ρ σ,
      ρs ρ ->
      σs σ ->
      σ.(PState) = ρ.(PState)) /\
    (forall ρ,
      ρs ρ ->
      ρ.(PCalls) i = None) /\
    (forall σ,
      σs σ ->
      σ.(PCalls) i = Some (existT _ _ m)) /\
    (forall ρ σ,
      ρs ρ ->
      σs σ ->
      σ.(PRets) = ρ.(PRets)).

Definition InvokeAny {E F VE VF} impl i : @Relt E F VE VF :=
  fun s ρ t σ =>
    exists Ret (m : F Ret), TInvoke impl i Ret m s ρ t σ.

Definition Returned {E F VE VF} (i : ThreadName) {Ret} (m : F Ret) : @Prec E F VE VF :=
  fun s ρs =>
    (* TODO: check nonempty *)
    forall ρ (v : Ret),
      fst s i = Cont m (Return v) /\
      ρs ρ /\
      ρ.(PRets) i = Some (existT _ _ v).

Definition TReturn {E F VE VF} (impl : Impl E F) (i : ThreadName) {Ret} (m : F Ret) : @Relt E F VE VF :=
  fun s ρs t σs =>
    exists (v : Ret),
      InterOStep impl i (fst s) (RetEv m v) (fst t) /\
      (forall ρ σ,
        ρs ρ ->
        σs σ ->
        σ.(PState) = ρ.(PState)) /\
      (forall ρ σ,
        ρs ρ ->
        σs σ ->
        σ.(PCalls) = ρ.(PCalls)) /\
      (* TODO: should be σ? *)
      (exists ρ,
        ρs ρ /\
        ρ.(PRets) i = Some (existT _ _ v)) /\
      (forall σ,
        σs σ ->
        σ.(PRets) i = None).

Definition ReturnAny {E F VE VF} impl i : @Relt E F VE VF :=
  fun s ρ t σ =>
    exists Ret (m : F Ret), TReturn impl i m s ρ t σ.

Definition initPoss {F VF} : @Poss F VF := {|
  PState := VF.(Init);
  PCalls _ := None;
  PRets _ := None;
|}.

Definition VerifyImpl
  {E F}
  (VE : Spec E)
  (VF : Spec F)
  (R G : ThreadName -> Relt VE VF)
  (P : ThreadName -> forall Ret, F Ret -> Prec VE VF)
  (impl : Impl E F)
  (Q : ThreadName -> forall Ret, F Ret -> Post VE VF Ret) : Prop :=
  (* Side conditions *)
  (forall i j, i <> j -> G i ==> R j) /\
  (forall i Ret (m : F Ret) v,
    P i Ret m (allIdle, VE.(Init)) (eq initPoss) /\
    Stable (R i) (P i Ret m) /\
    Stable (R i) (Q i Ret m v)) /\
  (forall i Ret1 (m1 : F Ret1) Ret2 (m2 : F Ret2) v,
    P i Ret1 m1 <<- TInvoke impl i Ret1 m1 <<- Q i Ret1 m1 v <<- PrecToRelt (Returned i m1) <<- TReturn impl i m1 ==> P i Ret2 m2) /\
  (* Verification task *)
  (forall i Ret (m : F Ret),
    VerifyProg i (R i) (G i)
      (P i Ret m <<- TInvoke impl i Ret m)
      (impl Ret m)
      (fun v => Q i Ret m v ->> PrecToRelt (Returned i m))).