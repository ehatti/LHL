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

Definition Prec E VE F :=
  @InterState E F VE ->
  Trace (ThreadEvent F) ->
  Prop.

Definition Relt E VE F :=
  @InterState E F VE -> Trace (ThreadEvent F) ->
  @InterState E F VE -> Trace (ThreadEvent F) ->
  Prop.

Definition Post E VE F A :=
  A -> Relt E VE F.

Inductive RTC {E VE F} {R : Relt E VE F} : Relt E VE F :=
| RTCRefl s ρ : RTC s ρ s ρ
| RTCTrans s ρ t σ r τ :
    R s ρ t σ ->
    RTC t σ r τ ->
    RTC s ρ r τ.
Arguments RTC {E VE F} R.

Definition ReltToPrec {E VE F} (R : Relt E VE F) : Prec E VE F :=
  fun t σ => exists s ρ, R s ρ t σ.
Coercion ReltToPrec : Relt >-> Prec.

Definition PrecCompose {E VE F} (P : Prec E VE F) (R : Relt E VE F) : Prec E VE F :=
  fun t σ => exists s ρ, P s ρ /\ R s ρ t σ.

Notation "R <<- G" := (PrecCompose R G) (left associativity, at level 37).

Definition ReltCompose {E VE F} (R G : Relt E VE F) : Relt E VE F :=
  fun s ρ r τ => exists t σ, R s ρ t σ /\ G t σ r τ.
Notation "R ->> G" := (ReltCompose R G) (right associativity, at level 39).

Class HasSub A :=
  sub : A -> A -> Prop.
Notation "P ==> Q" := (sub P Q) (right associativity, at level 41).

Global Instance subPrec E VE F : HasSub (@Prec E VE F) :=
  fun P Q => forall s ρ, P s ρ -> Q s ρ.

Global Instance subRelt E VE F : HasSub (Relt E VE F) :=
  fun P Q => forall s ρ t σ, P s ρ t σ -> Q s ρ t σ.

Class HasStable {E VE F} A :=
  Stable : Relt E VE F -> A -> Prop.

Global Instance stableRelt {E VE F} : HasStable (Relt E VE F) :=
  fun R Q => (R ->> Q ==> Q) /\ (Q ->> R ==> Q).

Global Instance stablePrec {E VE F} : HasStable (@Prec E VE F) :=
  fun R P => P <<- R ==> P.

Global Instance stablePost {E VE F A} : HasStable (Post E VE F A) :=
  fun R Q => forall v, stableRelt R (Q v).

Definition id {E VE F} : Relt E VE F :=
  fun s ρ t σ => s = t /\ ρ = σ.

Definition ptop {E VE F} : @Prec E VE F :=
  fun _ _ => True.
Definition rtop {E VE F} : Relt E VE F :=
  fun _ _ _ _ => True.

Notation "ρ --> σ" := (exists t, AllRetEv t /\ LinRw (ρ ++ t) σ)
  (at level 20).

Definition Commit {E VE F} VF i (impl : Impl E F)
  (G : Relt E VE F)
  (P : @Prec E VE F)
  (ev : @Event E)
  (Q : Relt E VE F) :=
  forall s ρ t,
  LinToSpec ρ VF ->
  P s ρ ->
  InterStep (impl:=impl) i s (i, liftUEv ev) t ->
    exists σ,
      Q s ρ t σ /\
      G s ρ t σ /\
      ρ --> σ.

CoInductive VerifyProg {E VE F} VF i (impl : Impl E F) : Relt E VE F -> Relt E VE F -> forall (A: Type), @Prec E VE F -> Prog E A -> Post E VE F A -> Prop :=
| SafeReturn A v R G P Q :
    (forall s ρ t σ, P s ρ -> Q v s ρ t σ) ->
    VerifyProg VF i impl R G A P (Return v) Q
| SafeBind A B R G P QI QR S (m : E A) (k : A -> Prog E B) :
    Stable R QI ->
    Stable R QR ->
    Commit VF i impl G P (CallEv m) QI ->
    (forall v,
      Commit VF i impl G QI (RetEv m v) (QR v) /\
      VerifyProg VF i impl R G B (QR v) (k v) S) ->
    VerifyProg VF i impl R G B P (Bind m k) S
| SafeNoOp A R G P C Q :
    VerifyProg VF i impl R G A P C Q ->
    VerifyProg VF i impl R G A P (NoOp C) Q
.
Arguments VerifyProg {E VE F} VF i impl R G {A} P C Q.
  
Inductive TraceIdle i {F} : Trace (ThreadEvent F) -> Prop :=
| NilIdle : TraceIdle i nil
| SkipIdle {j e ρ} :
    i <> j ->
    TraceIdle i ρ ->
    TraceIdle i (cons (j, e) ρ)
| ConsIdle {A m v ρ} :
    TraceIdle i ρ ->
    TraceIdle i (cons (i, CallEv m) (cons (i, RetEv (Ret:=A) m v) ρ)).

Definition TIdle {E VE F} (i : ThreadName) : @Prec E VE F :=
  fun s ρ =>
    fst s i = Idle /\
    TraceIdle i ρ.

Definition TInvoke {E VE F} impl (i : ThreadName) Ret (m : F Ret) : Relt E VE F :=
  fun s ρ t σ =>
    TIdle i s ρ /\
    σ = app ρ (cons (i, CallEv m) nil) /\
    InterStep (impl:=impl) i s (i, OCallEv m) t.

Definition InvokeAny {E VE F} impl i : Relt E VE F :=
  fun s ρ t σ =>
    exists Ret (m : F Ret), TInvoke impl i Ret m s ρ t σ.

Definition Returned {E VE F} (i : ThreadName) {Ret} (m : F Ret) : Relt E VE F :=
  fun s ρ t σ =>
    s = t /\
    ρ = σ /\
    exists (v : Ret), 
      fst t i = Cont m (Return v) /\
      exists r,
        projAgent i σ = app r (cons (i, RetEv m v) nil).

Definition TReturn {E VE F} (impl : Impl E F) (i : ThreadName) {Ret} (m : F Ret) : Relt E VE F :=
  fun s ρ t σ =>
    fst t i = Idle /\
    σ = ρ /\
    exists (v : Ret) r,
      projAgent i σ = app r (cons (i, RetEv m v) nil) /\
      InterStep (impl:=impl) i s (i, ORetEv m v) t.

Definition ReturnAny {E VE F} impl i : Relt E VE F :=
  fun s ρ t σ =>
    exists Ret (m : F Ret), TReturn impl i m s ρ t σ.

Definition VerifyImpl
  {E F}
  (VE : Spec E)
  (VF : Spec F)
  (R G : ThreadName -> Relt E VE F)
  (P : ThreadName -> forall Ret, F Ret -> @Prec E VE F)
  (impl : Impl E F)
  (Q : ThreadName -> forall Ret, F Ret -> Post E VE F Ret) : Prop :=
  (* Side conditions *)
  (forall i j, i <> j -> G i ==> R j) /\
  (forall i Ret (m : F Ret) v,
    P i Ret m (allIdle, VE.(Init)) nil /\
    P i Ret m ==> TIdle i /\
    Stable (R i) (P i Ret m) /\
    Stable (R i) (Q i Ret m v)) /\
  (forall i Ret1 (m1 : F Ret1) Ret2 (m2 : F Ret2) v,
    P i Ret1 m1 <<- TInvoke impl i Ret1 m1 <<- Q i Ret1 m1 v <<- Returned i m1 <<- TReturn impl i m1 ==> P i Ret2 m2) /\
  (* Verification task *)
  (forall i Ret (m : F Ret),
    VerifyProg VF i impl (R i) (G i)
      (P i Ret m <<- TInvoke impl i Ret m)
      (impl Ret m)
      (fun v s ρ t σ =>
        Q i Ret m v s ρ t σ /\
        Returned i m t σ t σ)).