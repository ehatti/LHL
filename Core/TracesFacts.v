From Coq Require Import 
    Init.Nat
    Arith
    FunctionalExtensionality
    PropExtensionality
    Program.Equality.

From LHL.Util Require Import
  Util
  TransUtil
  Tactics.

From LHL.Core Require Import
    Program
    Specs
    Traces
    Eutt.

(* Basic Trace Properties *)

Lemma nil_IsTraceOfSpec {E} :  
    forall (spec : Spec E),
    IsTraceOfSpec nil spec.
Proof.
    intros. exists spec.(Init). apply TransUtil.StepsNone.
Qed.

Lemma IsTraceOf_iso {E} t spec :
  IsTraceOfSpec (E:=E) t spec ->
  IsTraceOfSpecBwd (to_bwd t) spec.
intros.
destruct H.
exists x.
apply Steps_iso.
easy.
Qed.

Lemma BwdIsTraceOf_iso {E} t spec :
  IsTraceOfSpecBwd (E:=E) (to_bwd t) spec ->
  IsTraceOfSpec t spec.
intros.
destruct H.
exists x.
apply BwdSteps_iso.
easy.
Qed.

(* State Properties *)

(* Step Properties *)

(* overObj and InterStep Properties *)

Fixpoint projOverThr {E F : ESig} (p : Trace (ThreadLEvent E F)) : Trace (ThreadEvent F) :=
  match p with
  | nil => nil
  | cons (i, UEvent _) p => projOverThr p
  | cons (i, OEvent e) p => cons (i, e) (projOverThr p)
  end.

Lemma overObj_iso {E F : ESig} {lay : Layer E F} :
  forall s p t,
  Steps (Step (overObj lay)) s p t ->
  exists q,
    p = projOverThr q /\
    InterSteps lay.(LImpl) s q t.
Admitted.

Lemma InterSteps_iso {E F : ESig} {lay : Layer E F} :
  forall s p t,
  InterSteps (spec:=lay.(USpec)) lay.(LImpl) s p t ->
  Steps (Step (overObj lay)) s (projOverThr p) t.
Admitted.

Lemma decompInterSteps {E F : ESig} {spec : Spec E} {impl : Impl E F} :
  InterSteps (spec:=spec) impl =
  (fun s p t =>
    InterOSteps impl (fst s) (projOver p) (fst t) /\
    InterUSteps s (projUnder p) t).
Admitted.

Lemma decompUnderSteps {E F : ESig} {spec : Spec E} :
  InterUSteps (F:=F) (spec:=spec) =
  fun s p t =>
    Steps (Step spec) (snd s) (projSilent p) (snd t) /\
    Steps (PointStep UnderThreadStep) (fst s) p (fst t).
extensionality s.
extensionality p.
extensionality t.
apply propositional_extensionality.
split.
intros.
split.
generalize dependent s.
induction p.
intros.
dependent destruction H.
constructor.
intros.
dependent destruction H.
unfold InterUStep in H.
destruct_all.
destruct a, o.
simpl in *.
econstructor.
exact H2.
apply IHp.
easy.
simpl in *.
rewrite H2.
apply IHp.
easy.
generalize dependent s.
induction p.
intros.
dependent destruction H.
constructor.
intros.
dependent destruction H.
unfold InterUStep in H.
destruct_all.
econstructor.
econstructor.
exact H1.
unfold differ_pointwise in H.
intros.
apply H in H3.
easy.
apply IHp.
easy.
intros.
destruct_all.
generalize dependent s.
induction p.
intros.
dependent destruction H.
dependent destruction H0.
destruct s, t.
simpl in *.
subst.
constructor.
intros.
simpl in *.
destruct a, o.
dependent destruction H.
dependent destruction H1.
dependent destruction H1.
simpl in *.
eapply StepsMore with (st'':=(st''0, st'')).
unfold InterUStep.
simpl.
split.
unfold differ_pointwise.
intros.
symmetry.
apply H2.
easy.
split.
easy.
easy.
apply IHp.
easy.
easy.
simpl in *.
dependent destruction H0.
dependent destruction H0.
simpl in *.
eapply StepsMore with (st'':=(st'', snd s)).
unfold InterUStep.
simpl.
split.
unfold differ_pointwise.
intros.
symmetry.
apply H1.
easy.
easy.
apply IHp.
easy.
easy.
Qed.

(* Eutt *)

(* Inductive euttTS_ {E E' F : ESig}  (RR : IRel E E') :
    ThreadState (E := E) (F := F) -> ThreadState (E := E') -> Prop :=
| euttTS_Idle : euttTS_ RR Idle Idle
| euttTS_Cont Ret m p p' : 
    eutt RR p p' -> 
    euttTS_ RR (Cont m (Ret := Ret) p) (Cont m (Ret := Ret) p')
| euttTS_UCall A Ret m k k' : 
    forall (x : A), eutt RR (k x) (k' x) ->
    euttTS_ RR (UCall m k) (UCall m (Ret := Ret) k').

Definition euttTS {E E' F : ESig}  (RR : IRel E E') :
    ThreadsSt (E := E) (F := F) -> ThreadsSt (E := E') -> Prop :=
    fun ths ths' => forall (i : ThreadName), euttTS_ RR (ths i) (ths' i).

Definition euttIS {A E E' F} (RR : IRel E E') :
    ThreadsSt (E := E) (F := F) * A -> ThreadsSt (E := E') * A -> Prop :=
        fun ost ost' => euttTS RR (fst ost) (fst ost') /\ (snd ost = snd ost').
        
Lemma eutt_InterStep {E F} (RR : IRel E E) (spec : Spec E) (impl : Impl E F) (impl' : Impl E F): 
    euttImpl RR impl impl' ->
    forall i ist0 ev ist1 ist0',
        euttIS (A := spec.(State)) RR ist0 ist0' ->
        InterStep (impl := impl) i ist0 ev ist1 ->
        exists ist1' ev',
            (ev' = ev  /\ InterStep (impl := impl') i ist0' ev' ist1' /\ euttIS RR ist1 ist1')
        \/  (ev' = (i, Silent) /\ InterStep (impl := impl') i ist0' ev' ist1' /\ euttIS RR ist0 ist1').
Proof.
    intros. remember H1. destruct H1.
    - (* OCall *) 
      unfold euttIS, euttTS in H0. destruct H0.
      pose (EUTTSI := (H0 i)).
      inversion EUTTSI. 
      pose (thst1' := (updt_thst (fst ist0') i (Cont m (impl' R m)))).
      pose (ist1' := (thst1', st)).
      exists ist1'. exists (i, OCallEv m).
      left; repeat split.
      + (* InterStep *)
        symmetry in H4.
        assert (thst1' i = Cont m (impl' R m)) by eapply updt_istate_i_eq_st.
        assert (differ_pointwise (fst ist0') thst1' i) by eapply updt_istate_pointwise.
        assert (ist0' = (fst ist0', st)) by (destruct ist0'; simpl in H1; rewrite H1; simpl; reflexivity).
        rewrite H6. pose (step' := IOCall (st := st) H4 H2 H5). apply step'.
      + (* Still eutt *)
        unfold euttTS. intro j. simpl.
        pose (Nat.eq_dec j i).
        destruct s.
        (* i = j *)
        assert (thst1' i = Cont m (impl' R m)) by eapply updt_istate_i_eq_st.
        subst. rewrite e0. rewrite H2.
        constructor. unfold euttImpl in H. apply H.
        (* i <> j *)
        pose (H0 j). simpl in e1. 
        assert (differ_pointwise (fst ist0') thst1' i) by eapply updt_istate_pointwise.
        rewrite (H2 j n). rewrite (d j n). assumption.   
Admitted.

Lemma euttTS_isPathOf {E F} (spec : Spec E) : 
    forall (impl : Impl E F) (impl' : Impl E F),
    forall t thst0 thst1 thst0', 
        euttIS ieq thst0 thst0' ->
        IsPathOf thst0 t thst1 (Steps (overObj (spec :> impl)).(Step)) ->
        exists thst1',  
            IsPathOf thst0' t thst1' (Steps (overObj (spec :> impl')).(Step)).
Admitted. *)