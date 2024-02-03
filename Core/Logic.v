From LHL.Core Require Import
  Program
  Specs
  Traces
  Linearizability.
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

  Class HasAll A :=
    All : A -> Prop.
  
  Global Instance all_Relt : HasAll Relt :=
    fun R => forall s ρ t σ, R s ρ t σ.
  
  Global Instance all_Prec : HasAll Prec :=
    fun P => forall s ρ, P s ρ.
  
  Definition id : Relt :=
    fun s ρ t σ => s = t /\ ρ = σ.
  
  Definition ptop : Prec :=
    fun _ _ => True.
  Definition rtop : Relt :=
    fun _ _ _ _ => True.
End Predicates.

Module Logic(O : OBJECT).
  Module Ps := Predicates(O).
  Import Ps.
  Import O.

  Inductive AllRetEv : Trace (@ThreadEvent F) -> Prop :=
  | NilAllRet : AllRetEv nil
  | ConsAllRet {Ret s i} {v : F Ret} :
      AllRetEv s ->
      AllRetEv (cons (i, RetEv v) s).

  Notation LinToVF ρ := (exists l, IsTraceOfSpec l VF /\ LinRw ρ l).

  Notation "ρ --> σ" := (exists t, AllRetEv t /\ LinRw (ρ ++ t) σ)
    (at level 20).

  Definition Commit i (impl : Impl E F)
    (G : Relt)
    (P : Prec)
    (ev : @Event E)
    (Q : Relt) :=
    forall s ρ t,
    LinToVF ρ ->
    P s ρ ->
      InterStep (impl:=impl) i s (i, liftUEv ev) t /\
      exists σ,
        Q s ρ t σ /\
        G s ρ t σ /\
        ρ --> σ.
 
  Definition VerifyPrim i (impl : Impl E F) (R G : Relt) (P : Prec) (ev : @Event E) (Q : Relt) :=
    Stable R P /\
    Stable R Q /\
    Commit i impl G P ev Q.

  CoInductive VerifyProg i (impl : Impl E F) : Relt -> Relt -> forall (A: Type), Prec -> Prog E A -> Relt -> Prop :=
  | SafeReturn A v :
      VerifyProg i impl rtop id A ptop (Return v) id
  | SafeBind A B R G P QI QR S (m : E A) (k : A -> Prog E B) :
      VerifyPrim i impl R G P (CallEv m) QI ->
      (forall v,
        VerifyPrim i impl R G (P; QI) (RetEv v) QR /\
        VerifyProg i impl R G B (P; QI; QR) (k v) S) ->
      VerifyProg i impl R G B P (Bind m k) (QI; QR; S)
  | SafeNoOp A R G P C Q :
      VerifyProg i impl R G A P C Q ->
      VerifyProg i impl R G A P (NoOp C) Q
  | SafeWeaken A C R R' G G' P P' Q Q' :
      Stable R' P' ->
      Stable R' Q' ->
      All (P' ==> P) ->
      All (R' ==> R) ->
      All (G ==> G') ->
      All (Q ==> Q') ->
      VerifyProg i impl R G A P C Q ->
      VerifyProg i impl R' G' A P' C Q'
  .
  Arguments VerifyProg i impl R G {A} P C Q.

  Definition TIdle (i : ThreadName) : Prec :=
    fun s ρ =>
      fst s i = Idle /\
      true = even (length (@projAgent (@LEvent E F) i (map (fun e => (fst e, liftOEv (snd e))) ρ))).

  Definition Invoke impl (i : ThreadName) Ret (m : F Ret) : Relt :=
    fun s ρ t σ =>
      TIdle i s ρ /\
      σ = app ρ (cons (i, CallEv m) nil) /\
      InterStep (impl:=impl) i s (i, OCallEv m) t.

  Definition Returned (i : ThreadName) (Ret : Type) : Relt :=
    fun s ρ t σ =>
      s = t /\ ρ = σ /\
      exists (v : Ret), 
        fst t i = Cont (Return v) /\
        exists r,
          projAgent i σ = app r (cons (i, RetEv v) nil).

  Definition Return (impl : Impl E F) (i : ThreadName) (Ret : Type) : Relt :=
    fun s ρ t σ =>
      fst t i = Idle /\
      σ = ρ /\
      exists (v : Ret) r,
        projAgent i σ = app r (cons (i, RetEv v) nil) /\
        InterStep (impl:=impl) i s (i, ORetEv v) t.

  Definition VerifyImpl
    (R G : Relt)
    (P : forall Ret, F Ret -> Prec)
    (impl : Impl E F)
    (Q : forall Ret, F Ret -> Relt) : Prop :=
    All (G ==> R) /\
    (forall i Ret (m : F Ret),
      P Ret m (allIdle, VE.(Init)) nil /\
      All (P Ret m ==> TIdle i) /\
      Stable R (P Ret m) /\
      Stable R (Q Ret m) /\
      VerifyProg i impl R G
        (P Ret m; Invoke impl i Ret m)
        (impl Ret m)
        (Q Ret m; Returned i Ret)) /\
    (forall i Ret1 (m1 : F Ret1) Ret2 (m2 : F Ret2),
      All (P Ret1 m1; Invoke impl i Ret1 m1; Q Ret1 m1; Returned i Ret1; Return impl i Ret1 ==> P Ret2 m2)).
  
  (* Theorem soundness (lay : Layer E F) :
    (exists R G P Q, VerifyImpl R G P lay.(LImpl) Q) ->
    specRefines VF (overObj lay).
  intros.
  destruct H as [R].
  destruct H as [G].
  destruct H as [P].
  destruct H as [Q].
  unfold VerifyImpl, specRefines, TransUtil.Incl in *.
  destruct H.
  destruct H0.
  intros.
  unfold IsTraceOfSpec, TransUtil.IsPathOf, TransUtil.Steps in *.
  destruct H2 as [st].
  Admitted. *)
End Logic.