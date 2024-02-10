From LHL.Core Require Import
  Program
  Specs
  Traces
  Linearizability.
From Coq Require Import
  Lists.List
  Init.Nat
  Logic.FunctionalExtensionality
  Logic.PropExtensionality.

Definition Prec {E} VE F :=
  @InterState E F VE ->
  Trace (ThreadEvent F) ->
  Prop.

Definition Relt {E} VE F :=
  @InterState E F VE -> Trace (ThreadEvent F) ->
  @InterState E F VE -> Trace (ThreadEvent F) ->
  Prop.

Definition PrecCompose {E VE F} (P : @Prec E VE F) (R : Relt VE F) : Prec VE F :=
  fun t σ => exists s ρ, P s ρ /\ R s ρ t σ.

Notation "R << G" := (PrecCompose R G) (left associativity, at level 38).

Definition ReltCompose {E VE F} (R G : @Relt E VE F) : Relt VE F :=
  fun s ρ r τ => exists t σ, R s ρ t σ /\ G t σ r τ.
Notation "R >> G" := (ReltCompose R G) (right associativity, at level 39).

Class HasImpl A :=
  impl : A -> A -> Prop.
Notation "P ==> Q" := (impl P Q) (right associativity, at level 41).

Global Instance implPrec E VE F : HasImpl (@Prec E VE F) :=
  fun P Q => forall s ρ, P s ρ -> Q s ρ.

Global Instance implRelt E VE F : HasImpl (@Relt E VE F) :=
  fun P Q => forall s ρ t σ, P s ρ t σ -> Q s ρ t σ.

Class HasStable {E VE F} A :=
  Stable : @Relt E VE F -> A -> Prop.

Global Instance stableRelt {E VE F} : HasStable (@Relt E VE F) :=
  fun R Q => (R >> Q ==> Q) /\ (Q >> R ==> Q).

Global Instance stablePrec {E VE F} : HasStable (@Prec E VE F) :=
  fun R P => P << R ==> P.

Definition id {E VE F} : @Relt E VE F :=
  fun s ρ t σ => s = t /\ ρ = σ.

Definition ptop {E VE F} : @Prec E VE F :=
  fun _ _ => True.
Definition rtop {E VE F} : @Relt E VE F :=
  fun _ _ _ _ => True.

Notation "ρ --> σ" := (exists t, AllRetEv t /\ LinRw (ρ ++ t) σ)
  (at level 20).

Definition Commit {E VE F} VF i (impl : Impl E F)
  (R G : @Relt E VE F)
  (P : @Prec E VE F)
  (ev : @Event E)
  (Q : @Relt E VE F) :=
  forall s ρ t,
  LinToSpec ρ VF ->
  P s ρ ->
  InterStep (impl:=impl) i s (i, liftUEv ev) t ->
    exists σ,
      Q s ρ t σ /\
      G s ρ t σ /\
      ρ --> σ.

Definition VerifyPrim {E VE F} VF i (impl : Impl E F)
  (R G : @Relt E VE F)
  (P : @Prec E VE F)
  (ev : @Event E)
  (Q : @Relt E VE F) :=
  Stable R P /\
  Stable R Q /\
  Commit VF i impl R G P ev Q.

CoInductive VerifyProg {E VE F} VF i (impl : Impl E F) : @Relt E VE F -> @Relt E VE F -> forall (A: Type), @Prec E VE F -> Prog E A -> @Relt E VE F -> Prop :=
| SafeReturn A v :
    VerifyProg VF i impl rtop id A ptop (Return v) id
| SafeBind A B R G P QI QR S (m : E A) (k : A -> Prog E B) :
    VerifyPrim VF i impl R G P (CallEv m) QI ->
    (forall v,
      VerifyPrim VF i impl R G (P << QI) (RetEv m v) QR /\
      VerifyProg VF i impl R G B (P << QI << QR) (k v) S) ->
    VerifyProg VF i impl R G B P (Bind m k) (QI >> QR >> S)
| SafeNoOp A R G P C Q :
    VerifyProg VF i impl R G A P C Q ->
    VerifyProg VF i impl R G A P (NoOp C) Q
| SafeWeaken {A} {C : Prog E A} R R' G G' P P' Q Q' :
    VerifyProg VF i impl R G A P C Q ->
    Stable R' P' ->
    Stable R' Q' ->
    P' ==> P ->
    R' ==> R ->
    G ==> G' ->
    Q ==> Q' ->
    VerifyProg VF i impl R' G' A P' C Q'
.
Arguments VerifyProg {E VE F} VF i impl R G {A} P C Q.

Definition TIdle {E VE F} (i : ThreadName) : @Prec E VE F :=
  fun s ρ =>
    fst s i = Idle /\
    true = even (length (@projAgent (@LEvent E F) i (map (fun e => (fst e, liftOEv (snd e))) ρ))).

Definition TInvoke {E VE F} impl (i : ThreadName) Ret (m : F Ret) : @Relt E VE F :=
  fun s ρ t σ =>
    TIdle i s ρ /\
    σ = app ρ (cons (i, CallEv m) nil) /\
    InterStep (impl:=impl) i s (i, OCallEv m) t.

Inductive ReltRTC {E VE F} {R : @Relt E VE F} : @Relt E VE F :=
| RTCRefl s ρ : ReltRTC s ρ s ρ
| RTCStep s ρ t σ : R s ρ t σ -> ReltRTC s ρ t σ
| RTCTrans s ρ t σ r τ :
    ReltRTC s ρ t σ ->
    ReltRTC t σ r τ ->
    ReltRTC s ρ r τ.
Arguments ReltRTC {E VE F} R.

Definition InvokeAny {E VE F} impl : @Relt E VE F :=
  fun s ρ t σ => exists i Ret (m : F Ret), TInvoke impl i Ret m s ρ t σ.

Definition InvokeMany {E VE F} impl :=
  ReltRTC (@InvokeAny E VE F impl).

Definition Returned {E VE F} (i : ThreadName) {Ret} (m : F Ret) : @Relt E VE F :=
  fun s ρ t σ =>
    s = t /\ ρ = σ /\
    exists (v : Ret), 
      fst t i = Cont m (Return v) /\
      exists r,
        projAgent i σ = app r (cons (i, RetEv m v) nil).

Definition TReturn {E VE F} (impl : Impl E F) (i : ThreadName) {Ret} (m : F Ret) : @Relt E VE F :=
  fun s ρ t σ =>
    fst t i = Idle /\
    σ = ρ /\
    exists (v : Ret) r,
      projAgent i σ = app r (cons (i, RetEv m v) nil) /\
      InterStep (impl:=impl) i s (i, ORetEv m v) t.

Definition ReturnAny {E VE F} impl : @Relt E VE F :=
  fun s ρ t σ => exists i Ret (m : F Ret), TReturn impl i m s ρ t σ.

Definition ReturnMany {E VE F} impl :=
  ReltRTC (@ReturnAny E VE F impl).

Definition VerifyImpl
  {E F}
  (VE : Spec E)
  (VF : Spec F)
  (R G : ThreadName -> @Relt E VE F)
  (P : ThreadName -> forall Ret, F Ret -> @Prec E VE F)
  (impl : Impl E F)
  (Q : ThreadName -> forall Ret, F Ret -> @Relt E VE F) : Prop :=
  (forall i Ret (m : F Ret),
    VerifyProg VF i impl (R i) (G i)
      (P i Ret m << TInvoke impl i Ret m)
      (impl Ret m)
      (Q i Ret m >> Returned i m)) /\
  (forall i Ret (m : F Ret),
    P i Ret m (allIdle, VE.(Init)) nil /\
    P i Ret m ==> TIdle i /\
    Stable (R i) (P i Ret m) /\
    Stable (R i) (Q i Ret m)) /\
  (forall i, G i ==> R i) /\
  (forall i Ret1 (m1 : F Ret1) Ret2 (m2 : F Ret2),
    P i Ret1 m1 << TInvoke impl i Ret1 m1 << Q i Ret1 m1 << Returned i m1 << TReturn impl i m1 ==> P i Ret2 m2).