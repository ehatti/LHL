From LHL.Core Require Import
  Program
  Specs
  Traces.
From Coq Require Import
  Lists.List
  Init.Nat.

Module Type OBJECT.
  Parameter E F : ESig.
  Parameter VF : Spec F.
  Parameter VE : Spec E.
End OBJECT.

Module Predicates(O : OBJECT).
  Import O.

  Definition Prec := @InterState E VE -> Trace (ThreadEvent F) -> Prop.

  Definition Relt :=
    @InterState E VE -> Trace (ThreadEvent F) ->
    @InterState E VE -> Trace (ThreadEvent F) ->
    Prop.

  Definition Post A := A -> Relt.

  Definition Prec_to_Relt (P : Prec) : Relt :=
    fun s ρ t σ => s = t /\ ρ = σ /\ P t σ.
  Coercion Prec_to_Relt : Prec >-> Relt.
  Definition Relt_to_Prec (R : Relt) : Prec :=
    fun t σ => exists s ρ, R s ρ t σ.
  Coercion Relt_to_Prec : Relt >-> Prec.

  Definition Relt_compose (R G : Relt) : Relt :=
    fun s ρ r τ => exists t σ, R s ρ t σ /\ G t σ r τ.
  Notation "R ; G" := (Relt_compose R G) (right associativity, at level 39).

  Class HasImpl A :=
    impl : A -> A -> A.
  Notation "P ==> Q" := (impl P Q) (right associativity, at level 35).
  
  Global Instance impl_Prec : HasImpl Prec :=
    fun P Q s ρ => P s ρ -> Q s ρ.
  
  Global Instance impl_Relt : HasImpl Relt :=
    fun P Q s ρ t σ => P s ρ t σ -> Q s ρ t σ.
  
  Class HasStable A :=
    Stable : Relt -> A -> Prop.
  
  Global Instance stable_Relt : HasStable Relt :=
    fun R Q => forall s ρ t σ, (R; Q ==> Q) s ρ t σ /\ (Q; R ==> Q) s ρ t σ.
  
  Global Instance stable_Prec : HasStable Prec :=
    fun R P => forall s ρ, ((fun t σ => exists s ρ, P s ρ /\ R s ρ t σ) ==> P) s ρ.
End Predicates.

Module Logic(O : OBJECT).
  Module Ps := Predicates(O).
  Import Ps.
  Import O.

  Definition Commit i (impl : Impl E F) (G : Relt) (P : Prec) (ev : @Event E) (Q : Relt) :=
    forall s ρ t r evs evs' evs'',
    P s ρ ->
      InterStep (impl:=impl) i s (i, liftUEv ev) t /\
      InterSteps (impl:=impl) t evs' r /\
      evs'' = app evs (cons (i, liftUEv ev) evs') /\
        exists σ,
        Q s ρ t σ /\
        G s ρ t σ.
 
  Definition VerifyPrim i (impl : Impl E F) (R G : Relt) (P : Prec) (ev : @Event E) (Q : Relt) :=
    Stable R P /\
    Stable R Q /\
    Commit i impl G P ev Q.

  Inductive VerifyProg i (impl : Impl E F) (R G : Relt) : forall (A: Type), Prec -> Prog E A -> Relt -> Prop :=
  | SafeReturn {A} P Q v :
      VerifyPrim i impl R G P (RetEv v) Q ->
      VerifyProg i impl R G A P (Return v) Q
  | SafeBind {A B} P Q S (m : E A) (k : A -> Prog E B) :
      VerifyPrim i impl R G P (CallEv m) Q ->
      (forall x, VerifyProg i impl R G B (P; Q) (k x) S) ->
      VerifyProg i impl R G B P (Bind m k) (Q; S)
  .
  Arguments VerifyProg i impl R G {A} P C Q.

  Definition TIdle (i : ThreadName) : Prec :=
    fun s ρ =>
      fst s i = Idle /\
      true = even (length (@projAgent (@LEvent E F) i (map (fun e => (fst e, liftOEv (snd e))) ρ))).

  Definition Invoke (i : ThreadName) Ret (m : F Ret) : Relt :=
    fun s ρ t σ =>
      TIdle i s ρ /\
      σ = app ρ (cons (i, CallEv m) nil) /\
      exists (C : Prog E Ret),
        fst s i = Cont C.

  Definition Returned (i : ThreadName) (Ret : Type) : Relt :=
    fun s ρ t σ =>
      s = t /\ ρ = σ /\
      exists (v : Ret), 
        fst t i = Cont (Return v) /\
        exists r,
          projAgent i σ = app r (cons (i, RetEv v) nil).

  Definition Return (i : ThreadName) (Ret : Type) : Relt :=
    fun s ρ t σ =>
      σ = ρ /\
      fst t i = Idle /\
      exists (v : Ret) r,
        fst s i = Cont (Return v) /\
        projAgent i σ = app r (cons (i, RetEv v) nil).

  Definition VerifyImpl
    (R G : Relt)
    (P : forall Ret, F Ret -> Prec)
    (impl : Impl E F)
    (Q : forall Ret, F Ret -> Relt) : Prop :=
    (forall i Ret (m : F Ret),
      P Ret m (allIdle, VE.(Init)) nil /\
      (forall s ρ, (P Ret m ==> TIdle i) s ρ) /\
      Stable R (P Ret m) /\
      Stable R (Q Ret m) /\
      VerifyProg i impl R G
        (P Ret m; Invoke i Ret m)
        (impl Ret m)
        (Q Ret m; Returned i Ret)) /\
    (forall i Ret1 (m1 : F Ret1) Ret2 (m2 : F Ret2) s ρ t σ,
      (P Ret1 m1; Invoke i Ret1 m1; Q Ret1 m1; Returned i Ret1; Return i Ret1 ==> P Ret2 m2) s ρ t σ).
End Logic.