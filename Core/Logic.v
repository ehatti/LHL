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

  Definition Prec :=
    @InterState E F VE ->
    Trace (ThreadEvent F) ->
    Prop.

  Definition Relt :=
    @InterState E F VE -> Trace (ThreadEvent F) ->
    @InterState E F VE -> Trace (ThreadEvent F) ->
    Prop.

  Definition PrecToRelt (P : Prec) : Relt :=
    fun s ρ t σ => s = t /\ ρ = σ /\ P t σ.
  Coercion PrecToRelt : Prec >-> Relt.
  Definition ReltToPrec (R : Relt) : Prec :=
    fun t σ => exists s ρ, R s ρ t σ.
  Coercion ReltToPrec : Relt >-> Prec.

  Definition ReltCompose (R G : Relt) : Relt :=
    fun s ρ r τ => exists t σ, R s ρ t σ /\ G t σ r τ.
  Notation "R ; G" := (ReltCompose R G) (right associativity, at level 39).

  Class HasImpl A :=
    impl : A -> A -> A.
  Notation "P ==> Q" := (impl P Q) (right associativity, at level 41).
  
  Global Instance implPrec : HasImpl Prec :=
    fun P Q s ρ => P s ρ -> Q s ρ.
  
  Global Instance implRelt : HasImpl Relt :=
    fun P Q s ρ t σ => P s ρ t σ -> Q s ρ t σ.
  
  Class HasStable A :=
    Stable : Relt -> A -> Prop.
  
  Global Instance stableRelt : HasStable Relt :=
    fun R Q => forall s ρ t σ, (R; Q ==> Q) s ρ t σ /\ (Q; R ==> Q) s ρ t σ.
  
  Global Instance stablePrec : HasStable Prec :=
    fun R P => forall s ρ, ((fun t σ => exists s ρ, P s ρ /\ R s ρ t σ) ==> P) s ρ.

  Class HasAll A :=
    All : A -> Prop.
  
  Global Instance allRelt : HasAll Relt :=
    fun R => forall s ρ t σ, R s ρ t σ.
  
  Global Instance allPrec : HasAll Prec :=
    fun P => forall s ρ, P s ρ.
  
  Definition id : Relt :=
    fun s ρ t σ => s = t /\ ρ = σ.
  
  Definition ptop : Prec :=
    fun _ _ => True.
  Definition rtop : Relt :=
    fun _ _ _ _ => True.

  Lemma stableRight {R Q : Relt} : Stable R Q -> All ((Q; R) ==> Q).
  unfold Stable, stableRelt, All, allRelt.
  intros.
  specialize (H s ρ t σ).
  destruct H.
  easy.
  Qed.

  Lemma stableLeft {R Q : Relt} : Stable R Q -> All ((R; Q) ==> Q).
  unfold Stable, stableRelt, All, allRelt.
  intros.
  specialize (H s ρ t σ).
  destruct H.
  easy.
  Qed.

  Lemma compStable {R Q S : Relt} :
    Stable R Q ->
    Stable R S ->
    Stable R (Q; S).
  intros.
  unfold Stable, stableRelt, impl, implRelt.
  intros.
  split.
  intros.
  do 3 destruct H1.
  do 3 destruct H2.
  do 2 eexists.
  split.
  eapply stableLeft.
  easy.
  do 2 eexists.
  split.
  exact H1.
  exact H2.
  easy.
  intros.
  do 6 destruct H1.
  do 2 eexists.
  split.
  exact H1.
  eapply stableRight.
  easy.
  do 2 eexists.
  split.
  exact H3.
  easy.
  Qed.

End Predicates.

Module Logic(O : OBJECT).
  Module Ps := Predicates(O).
  Import Ps.
  Import O.

  Notation "ρ --> σ" := (exists t, AllRetEv t /\ LinRw (ρ ++ t) σ)
    (at level 20).

  Definition Commit i (impl : Impl E F)
    (R G : Relt)
    (P : Prec)
    (ev : @Event E)
    (Q : Relt) :=
    forall s ρ t,
    LinToSpec ρ VF ->
    P s ρ ->
    InterStep (impl:=impl) i s (i, liftUEv ev) t ->
      exists σ,
        Q s ρ t σ /\
        G s ρ t σ /\
        ρ --> σ.
  
  Definition VerifyPrim i (impl : Impl E F)
    (R G : Relt)
    (P : Prec)
    (ev : @Event E)
    (Q : Relt) :=
    Stable R P /\
    Stable R Q /\
    Commit i impl R G P ev Q.

  CoInductive VerifyProg i (impl : Impl E F) : Relt -> Relt -> forall (A: Type), Prec -> Prog E A -> Relt -> Prop :=
  | SafeReturn A v :
      VerifyProg i impl rtop id A ptop (Return v) id
  | SafeBind A B R G P QI QR S (m : E A) (k : A -> Prog E B) :
      VerifyPrim i impl R G P (CallEv m) QI ->
      (forall v,
        VerifyPrim i impl R G (P; QI) (RetEv m v) QR /\
        VerifyProg i impl R G B (P; QI; QR) (k v) S) ->
      VerifyProg i impl R G B P (Bind m k) (QI; QR; S)
  | SafeNoOp A R G P C Q :
      VerifyProg i impl R G A P C Q ->
      VerifyProg i impl R G A P (NoOp C) Q
  .
  Arguments VerifyProg i impl R G {A} P C Q.

  Lemma SafeWeaken {i impl A} {C : Prog E A} R R' G G' P P' Q Q' :
    VerifyProg i impl R G P C Q ->
    Stable R' P' ->
    Stable R' Q' ->
    All (P' ==> P) ->
    All (R' ==> R) ->
    All (G ==> G') ->
    All (Q ==> Q') ->
    VerifyProg i impl R' G' P' C Q'.
  Admitted.

  Lemma SafeWeakenPost {i impl A} {C : Prog E A} R G P Q Q' :
    VerifyProg i impl R G P C Q ->
    Stable R Q' ->
    VerifyProg i impl R G P C Q'.
  Admitted.

  Definition TIdle (i : ThreadName) : Prec :=
    fun s ρ =>
      fst s i = Idle /\
      true = even (length (@projAgent (@LEvent E F) i (map (fun e => (fst e, liftOEv (snd e))) ρ))).

  Definition Invoke impl (i : ThreadName) Ret (m : F Ret) : Relt :=
    fun s ρ t σ =>
      TIdle i s ρ /\
      σ = app ρ (cons (i, CallEv m) nil) /\
      InterStep (impl:=impl) i s (i, OCallEv m) t.
  
  Definition InvokeAny impl i : Relt :=
    fun s ρ t σ => exists Ret (m : F Ret), Invoke impl i Ret m s ρ t σ.

  Definition Returned (i : ThreadName) {Ret} (m : F Ret) : Relt :=
    fun s ρ t σ =>
      s = t /\ ρ = σ /\
      exists (v : Ret), 
        fst t i = Cont m (Return v) /\
        exists r,
          projAgent i σ = app r (cons (i, RetEv m v) nil).

  Definition Return (impl : Impl E F) (i : ThreadName) {Ret} (m : F Ret) : Relt :=
    fun s ρ t σ =>
      fst t i = Idle /\
      σ = ρ /\
      exists (v : Ret) r,
        projAgent i σ = app r (cons (i, RetEv m v) nil) /\
        InterStep (impl:=impl) i s (i, ORetEv m v) t.

  Definition ReturnAny impl i : Relt :=
    fun s ρ t σ => exists Ret (m : F Ret), Return impl i m s ρ t σ.

  Definition VerifyImpl
    (R G : ThreadName -> Relt)
    (P : ThreadName -> forall Ret, F Ret -> Prec)
    (impl : Impl E F)
    (Q : ThreadName -> forall Ret, F Ret -> Relt) : Prop :=
    (forall i Ret (m : F Ret),
      VerifyProg i impl (R i) (G i)
        (P i Ret m; Invoke impl i Ret m)
        (impl Ret m)
        (Q i Ret m; Returned i m)) /\
    (forall i Ret (m : F Ret),
      P i Ret m (allIdle, VE.(Init)) nil /\
      All (P i Ret m ==> TIdle i) /\
      Stable (R i) (P i Ret m) /\
      Stable (R i) (Q i Ret m)) /\
    (forall i, All (G i ==> R i)) /\
    (forall i Ret1 (m1 : F Ret1) Ret2 (m2 : F Ret2),
      All (P i Ret1 m1; Invoke impl i Ret1 m1; Q i Ret1 m1; Returned i m1; Return impl i m1 ==> P i Ret2 m2)).
  
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