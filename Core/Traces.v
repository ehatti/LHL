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
| UCall {A B} (m : F A) (k : A -> Prog E B).
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
| UCallThreadStep A th th' (um : E A) om k :
  th = Cont om (Bind um k) ->
  th' = UCall om k ->
  UnderThreadStep th (Some (CallEv um)) th'
| URetThreadStep A th th' um om k v :
  th = UCall om k ->
  th' = Cont (A:=A) om (k v) ->
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

Definition overObj {E F : ESig} (lay : @Layer E F) : Spec F := 
  {|
    State := InterState F lay.(USpec);
    Step thst ev thst'' :=
      exists thst' p,
        InterUSteps F lay.(USpec) thst p thst' /\
        InterOStep lay.(LImpl) (fst ev) (fst thst') (snd ev) (fst thst'') /\
        snd thst' = snd thst'';
    Init := (allIdle, lay.(USpec).(Init))
  |}.

(* Refinement *)

Definition specRefines {E : ESig} (spec : Spec E) (spec': Spec E) : Prop := 
  Incl (fun t => IsTraceOfSpec t spec) (fun t => IsTraceOfSpec t spec'). 

Definition layerRefines {E E' F} (lay : @Layer E F) (lay': @Layer E' F)  := 
  specRefines (overObj lay) (overObj lay').

(* Interleaving *)

Inductive Interleave {E F} : (nat -> Trace (LEvent E F)) -> Trace (ThreadLEvent E F) -> Prop :=
| InterleaveNil qc :
    (forall i, qc i = nil) ->
    Interleave qc nil
| InterleaveCons i e q qc p :
    qc i = e :: q ->
    Interleave (fun j => if i =? j then q else qc j) p ->
    Interleave qc ((i, e) :: p).

Lemma uninterleave {E F} :
  forall qc p,
  @Interleave E F qc p ->
  forall i,
    qc i = projPoint i eqb p.
intros.
generalize dependent qc.
induction p; intros; dependent destruction H.
rewrite H.
easy.
simpl.
assert (i = i0 \/ i <> i0) by apply excluded_middle.
destruct H1.
subst.
rewrite H.
rewrite eqb_id.
f_equal.
apply IHp in H0.
rewrite eqb_id in H0.
easy.
rewrite eqb_nid.
2: easy.
apply IHp in H0.
rewrite eqb_nid in H0.
2: easy.
easy.
Qed.

Inductive set_list : list nat -> Type :=
| SLNil : set_list nil
| SLCons i is :
  ~In i is ->
  set_list is ->
  set_list (i :: is).

Axiom classicT : forall P, {P}+{~P}.

Fixpoint dedup (is : list nat) : list nat :=
  match is with
  | nil => nil
  | cons i is =>
      if classicT (List.In i is) then
        dedup is
      else
        cons i (dedup is)
  end.

Lemma dedup_correct :
  forall i is, List.In i is <-> List.In i (dedup is).
firstorder.
induction is.
contradiction.
simpl.
destruct (classicT (In a is)).
simpl in *.
destruct H.
subst.
apply IHis.
easy.
apply IHis.
easy.
simpl in *.
destruct H.
left.
easy.
right.
apply IHis.
easy.
induction is.
contradiction.
simpl in *.
destruct (classicT (In a is)).
right.
apply IHis.
easy.
simpl in *.
destruct H.
left.
easy.
right.
apply IHis.
easy.
Qed.

Lemma dedup_is_set : forall xs, set_list (dedup xs).
intros.
induction xs.
constructor.
simpl.
destruct (classicT (In a xs)).
easy.
constructor.
rewrite <- dedup_correct.
easy.
easy.
Qed.

Lemma interleave {E F} :
  forall is,
  set_list is ->
  forall qc,
    (forall i, ~In i is -> qc i = nil) ->
    exists p,
      @Interleave E F qc p.
intros.
generalize dependent qc.
induction H; intros.
exists nil.
constructor.
intros.
apply H0.
easy.
specialize (IHset_list (fun j => if i =? j then nil else qc j)).
eassert (exists p, Interleave _ p).
apply IHset_list.
intros.
assert (i = i0 \/ i <> i0) by apply excluded_middle.
destruct H2.
subst.
rewrite eqb_id.
easy.
rewrite eqb_nid.
apply H0.
unfold not.
intros.
destruct H3.
subst.
congruence.
apply H1.
easy.
easy.
destruct_all.
exists (List.map (fun e => (i, e)) (qc i) ++ x).
clear IHset_list H0 H n.
Admitted.