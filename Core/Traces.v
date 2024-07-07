From Coq Require Import
  List
  Relations
  Init.Nat
  Program.Equality
  Logic.FunctionalExtensionality.

From LHL.Util Require Import
  Util
  ListUtil
  TransUtil
  Tactics.

From LHL.Core Require Import
  Program
  Specs
  Eutt.

(* Traces *)

Definition Trace (T : Type) : Type := list T.

Definition PrefixOf {T} (ρ σ : Trace T) : Prop :=
  exists τ, σ = app ρ τ.

Definition projAgentEv {A} i (ev : nat * A) : option (nat * A) :=
  if eqb (fst ev) i then
    Some ev
  else
    None.

Definition projOverEv {E F : ESig} (ev : @ThreadLEvent E F) : option (ThreadEvent F) := 
  match ev with
  | (i, OEvent ev) => Some (i, ev)
  | _ => None
  end.

Definition projUnderEv {E F : ESig} (ev : @ThreadLEvent E F) : option (nat * option (Event E)) := 
  match ev with
  | (i, UEvent ev) => Some (i, ev)
  | _ => None
  end.

Fixpoint projUnderThr {E F} (p : Trace (ThreadLEvent E F)) : Trace (ThreadEvent E) :=
  match p with
  | nil => nil
  | cons (i, UEvent (Some ev)) q => cons (i, ev) (projUnderThr q)
  | cons _ q => projUnderThr q
  end.

Fixpoint projSilent {E} (p : Trace (ThreadName * option (Event E))) : Trace (ThreadEvent E) :=
  match p with
  | nil => nil
  | cons (i, None) q => projSilent q
  | cons (i, Some e) q => cons (i, e) (projSilent q)
  end.

Definition liftUEv {E F} (ev : @Event E) : @LEvent E F :=
  UEvent (Some ev).

Definition liftOEv {E F} (ev : @Event F) : @LEvent E F :=
  OEvent ev.

Notation projOver := (mapfilter projOverEv).
Notation projUnder := (mapfilter projUnderEv).
Definition projAgent {A} i : 
  Trace (ThreadName * A) -> Trace (ThreadName * A) := 
    (mapfilter (projAgentEv i)).
Notation liftU := (map liftUEv).
Notation liftO := (map liftOEv).

(* Implementation Transition System *)

Inductive ThreadState {E F : ESig} : Type :=
| Idle
| Cont {A} (m : F A) (p : Prog E A) 
| UCall {A B} (om : F B) (um : E A) (k : A -> Prog E B).
Arguments ThreadState : clear implicits.

Definition ThreadsSt (E F : ESig) : Type := ThreadName -> ThreadState E F.

Definition updt_thst (E F : ESig) := 
  @updt_istate ThreadName (ThreadState E F) eqb.

Definition allIdle {E F : ESig} : ThreadsSt E F := fun n => Idle.

Variant OverThreadStep {E F : ESig} (M : Impl E F) :
  ThreadState E F -> Event F -> ThreadState E F -> Prop :=
| OCallThreadStep th th' A (m : F A) :
  th = Idle ->
  th' = Cont m (M _ m) ->
  OverThreadStep M th (CallEv m) th'
| ORetThreadStep th th' A (m : F A) v :
  th = Cont m (Return v) ->
  th' = Idle ->
  OverThreadStep M th (RetEv m v) th'.

Variant UnderThreadStep {E F : ESig} :
  ThreadState E F -> option (Event E) -> ThreadState E F -> Prop :=
| UCallThreadStep A B th th' (um : E A) (om : F B) k :
  th = Cont om (Bind um k) ->
  th' = UCall om um k ->
  UnderThreadStep th (Some (CallEv um)) th'
| URetThreadStep A B th th' (um : E A) (om : F B) k v :
  th = UCall om um k ->
  th' = Cont om (k v) ->
  UnderThreadStep th (Some (RetEv um v)) th'
| USilentThreadStep A th th' om (p : Prog E A) :
  th = Cont om (NoOp p) ->
  th' = Cont om p ->
  UnderThreadStep th None th'.

Definition ThreadStep {E F : ESig} (M : Impl E F) (s : ThreadState E F) (e : LEvent E F) (t : ThreadState E F) :=
  match e with
  | UEvent e => UnderThreadStep s e t
  | OEvent e => OverThreadStep M s e t
  end.

Definition ThreadsStep {E F} (M : Impl E F)
  : ThreadsSt E F -> ThreadLEvent E F -> ThreadsSt E F -> Prop :=
  PointStep (ThreadStep (E := E) M).

(* Trace Semantics *)

Definition IsTraceOfImpl {E F : ESig} (t : Trace (ThreadLEvent E F)) (M : Impl E F) : Prop :=
  exists thst, Steps (ThreadsStep M) allIdle t thst.
  
Definition IsTraceOfSpec {E : ESig} (t : Trace (ThreadEvent E)) (spec : Spec E) : Prop := 
  exists st, Steps spec.(Step) spec.(Init) t st.

Definition IsTraceOfSpecBwd {E : ESig} (t : bwd_list (ThreadEvent E)) (spec : Spec E) : Prop :=
  exists st, BwdSteps spec.(Step) spec.(Init) t st.

(* Interactions *)

Definition InterState {E : ESig} F (spec : Spec E) : Type :=
  ThreadsSt E F * spec.(State).

Definition StateStep {E F : ESig} {spec : Spec E} (s : State spec) (ev : ThreadLEvent E F) (t : State spec) :=
  match snd ev with
  | UEvent (Some e) => spec.(Step) s (fst ev, e) t
  | _ => s = t
  end.

Definition InterStep {E F : ESig} {spec : Spec E} (impl : Impl E F)
  (s : InterState F spec)
  (ev : ThreadLEvent E F)
  (t : InterState F spec) :=
  ThreadsStep impl (fst s) ev (fst t) /\
  StateStep (snd s) ev (snd t).

Definition SelfSteps {E F : ESig} {spec : Spec E} i (impl : Impl E F)
  (s : InterState F spec)
  (p : Trace (LEvent E F))
  (t : InterState F spec) :=
  Steps (fun s ev t => InterStep impl s (i, ev) t) s p t.

Definition OtherSteps {E F : ESig} {spec : Spec E} i (impl : Impl E F)
  (s : InterState F spec)
  (p : Trace (ThreadLEvent E F))
  (t : InterState F spec) :=
  Steps (fun s ev t => fst ev <> i /\ InterStep impl s ev t) s p t.

Definition InterUStep {E F : ESig} {spec : Spec E} (i : ThreadName)
  (s : InterState F spec)
  (ev : option (Event E))
  (t : InterState F spec) :=
  PointStep UnderThreadStep (fst s) (i, ev) (fst t) /\
  match ev with
  | Some ev => spec.(Step) (snd s) (i, ev) (snd t)
  | None => snd s = snd t
  end.

Definition InterOStep {E F : ESig} (impl : Impl E F) (i : ThreadName)
  (s : ThreadsSt E F)
  (ev : Event F)
  (t : ThreadsSt E F) :=
  PointStep (OverThreadStep impl) s (i, ev) t.

Definition InterUSteps {E : ESig} F (spec : Spec E) :
  InterState F spec -> Trace (ThreadName * option (Event E)) -> InterState F spec -> Prop := 
  Steps (fun s ev t => InterUStep (fst ev) s (snd ev) t).

Definition InterOSteps {E : ESig} F (impl : Impl E F) : 
  ThreadsSt E F -> Trace (ThreadEvent F) -> ThreadsSt E F -> Prop := 
  Steps (fun s ev t => InterOStep impl (fst ev) s (snd ev) t).

Definition InterSteps {E F : ESig} {spec : Spec E} (impl : Impl E F) :=
  Steps (InterStep (spec:=spec) impl).

Lemma InterUSteps_pres {E F} {spec : Spec E} :
  forall t i A (m : F A) p s,
  InterUSteps F spec s p t ->
  ((exists p, fst s i = Cont m p) \/
   (exists B um k, fst s i = UCall (A:=B) m um k)) ->
  ((exists p, fst t i = Cont m p) \/
   (exists B um k, fst t i = UCall (A:=B) m um k)).
intros. generalize dependent s.
induction p; cbn; intros.
{
  dependent destruction H. easy.
}
{
  dependent destruction H. destruct a. cbn in *. apply IHp in H0. easy.
  destruct H. destruct o; cbn in *. destruct e; cbn in *;
  dependent destruction H; dependent destruction H;
  cbn in *.
  dec_eq_nats i t0.
  {
    rewrite <- x0 in H3. rewrite <- x.
    destruct H3; destruct_all; dependent destruction H.
    right. repeat econstructor.
  }
  {
    rewrite H0 in H3; easy.
  }
  dec_eq_nats i t0.
  {
    rewrite <- x0 in H3. rewrite <- x.
    destruct H3; destruct_all; dependent destruction H.
    left. repeat econstructor.
  }
  {
    rewrite H0 in H3; easy.
  }
  do 2 dependent destruction H. cbn in *.
  dec_eq_nats i t0.
  {
    rewrite <- x0 in H3. rewrite <- x.
    destruct H3; destruct_all; dependent destruction H.
    left. repeat econstructor.
  }
  {
    rewrite H0 in H3; easy.
  }
}
Qed.

Lemma InterUSteps_pres_idle {E F} {spec : Spec E} :
  forall i t p s,
  InterUSteps F spec s p t ->
  fst s i = Idle ->
  fst t i = Idle.
unfold InterUSteps. intros.
generalize dependent s. induction p; cbn; intros.
{
  dependent destruction H. easy.
}
{
  dependent destruction H. unfold InterUStep in H. destruct_all.
  dependent destruction H. cbn in *.
  destruct s, a. cbn in *.
  apply IHp in H1. easy.
  destruct st''. cbn in *.
  dependent destruction H.
  dec_eq_nats i t1. congruence. rewrite <- H0; easy.
  dec_eq_nats i t1. congruence. rewrite <- H0; easy.
  dec_eq_nats i t1. congruence. rewrite <- H0; easy.
}
Qed.

Program Definition overObj {E F : ESig} (lay : @Layer E F) : Spec F := 
  {|
    State := InterState F lay.(USpec);
    Step thst ev thst'' :=
      exists ths',
        InterOStep lay.(LImpl) (fst ev) (fst thst) (snd ev) ths' /\
        exists p,
          InterUSteps F lay.(USpec) (ths', snd thst) p thst'';
    Init := (allIdle, lay.(USpec).(Init))
  |}.

Definition overObjActiveMap {E F} (s : ThreadsSt E F) : ActiveMap F :=
  fun i => match s i with
  | Idle => None
  | Cont m _ => Some (existT _ _ m)
  | UCall m _ _ => Some (existT _ _ m)
  end.

Next Obligation.
change (fun _ : ThreadName => @None {A & F A})
with (overObjActiveMap (@allIdle E F)).
generalize dependent (@allIdle E F).
generalize dependent (Init (USpec lay)).
induction p; cbn; intros.
{
  constructor.
}
{
  dependent destruction H. destruct_all.
  destruct st'', H, a, e. cbn in *; dependent destruction H.
  {
    eapply SCCall with (a':=fun i => if i =? t1 then Some (existT _ _ m) else overObjActiveMap t0 i); unfold overObjActiveMap.
    rewrite <- x1. easy.
    rewrite eqb_id. easy.
    {
      unfold differ_pointwise. intros.
      rewrite eqb_nid, H2; try easy.
      remember (x0 j). destruct t2.
      eapply InterUSteps_pres_idle with (i:=j) in H1.
      cbn in *. rewrite H1. easy.
      easy.
      move H1 at bottom.
      eapply InterUSteps_pres with (m:=m0) (i:=j) in H1.
      destruct H1; destruct_all; cbn in *.
      rewrite H1. easy.
      rewrite H1. easy.
      cbn. rewrite <- Heqt2. left. repeat econstructor.
      eapply InterUSteps_pres with (m:=om) (i:=j) in H1.
      destruct H1; destruct_all; cbn in *.
      rewrite H1. easy.
      rewrite H1. easy.
      cbn. rewrite <- Heqt2. right. repeat econstructor.
    }
    apply IHp in H0.
    assert (overObjActiveMap t0 = (fun i : ThreadName =>
      if i =? t1 then
      Some
        (existT (fun A0 : Type => F A0) A m)
      else match t0 i with
      | Idle => None
      | @Cont _ _ A0 m0 _ =>
          Some (existT (fun A1 : Type => F A1) A0 m0)
      | @UCall _ _ _ B m0 _ _ =>
          Some (existT (fun A1 : Type => F A1) B m0)
      end)).
    unfold overObjActiveMap. extensionality i. dec_eq_nats i t1.
    {
      rewrite eqb_id.
      eapply InterUSteps_pres with (A:=A) (i:=t1) (m:=m) in H1.
      destruct H1; destruct_all; cbn in *.
      rewrite H. easy.
      rewrite H. easy.
      cbn. rewrite <- x. left. repeat econstructor.
    }
    {
      rewrite eqb_nid; easy.
    }
    symmetry in H. rewrite H. easy.
  }
  {
    cbn in *. dependent destruction H.
    eapply SCRet with (a':=fun i => if i =? t1 then None else overObjActiveMap t0 i); unfold overObjActiveMap.
    rewrite <- x1. easy.
    rewrite eqb_id. easy.
    {
      unfold differ_pointwise. intros.
      rewrite eqb_nid, H2; try easy.
      remember (x0 j). destruct t2.
      eapply InterUSteps_pres_idle with (i:=j) in H1.
      cbn in *. rewrite H1. easy.
      easy.
      move H1 at bottom.
      eapply InterUSteps_pres with (m:=m0) (i:=j) in H1.
      destruct H1; destruct_all; cbn in *.
      rewrite H1. easy.
      rewrite H1. easy.
      cbn. rewrite <- Heqt2. left. repeat econstructor.
      eapply InterUSteps_pres with (m:=om) (i:=j) in H1.
      destruct H1; destruct_all; cbn in *.
      rewrite H1. easy.
      rewrite H1. easy.
      cbn. rewrite <- Heqt2. right. repeat econstructor.
    }
    apply IHp in H0.
    assert (overObjActiveMap t0 = (fun i : ThreadName =>
      if i =? t1 then
      None
      else match t0 i with
      | Idle => None
      | @Cont _ _ A0 m0 _ =>
          Some (existT (fun A1 : Type => F A1) A0 m0)
      | @UCall _ _ _ B m0 _ _ =>
          Some (existT (fun A1 : Type => F A1) B m0)
      end)).
    unfold overObjActiveMap. extensionality i. dec_eq_nats i t1.
    {
      rewrite eqb_id.
      eapply InterUSteps_pres_idle with (i:=t1) in H1.
      cbn in *. rewrite H1. easy. easy.
    }
    {
      rewrite eqb_nid; easy.
    }
    rewrite <- H. easy.
  }
}
Qed.

(* Refinement *)

Definition specRefines {E : ESig} (spec : Spec E) (spec': Spec E) : Prop := 
  Incl (fun t => IsTraceOfSpec t spec) (fun t => IsTraceOfSpec t spec'). 

Definition layerRefines {E E' F} (lay : @Layer E F) (lay': @Layer E' F)  := 
  specRefines (overObj lay) (overObj lay').

(* Extra projections *)

Fixpoint projUnderThrSeq {E F} (p : Trace (LEvent E F)) : Trace (Event E) :=
  match p with
  | nil => nil
  | cons (UEvent (Some e)) p => cons e (projUnderThrSeq p)
  | cons _ p => projUnderThrSeq p
  end.

Fixpoint projOverSeq {E F} (p : Trace (LEvent E F)) : Trace (Event F) :=
  match p with
  | nil => nil
  | cons (OEvent e) p => cons e (projOverSeq p)
  | cons _ p => projOverSeq p
  end.