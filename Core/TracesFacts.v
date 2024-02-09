From Coq Require Import 
    Init.Nat
    Arith.

From LHL.Util Require Import
  Util
  TransUtil.

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

(* State Properties *)

(* Step Properties *)

(* Eutt *)

Inductive euttTS_ {E E' F : ESig}  (RR : IRel E E') :
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

Lemma euttTS_isPathOf {E F} (spec : Spec E) : 
    forall (impl : Impl E F) (impl' : Impl E F),
    forall t thst0 thst1 thst0', 
        euttIS ieq thst0 thst0' ->
        IsPathOf thst0 t thst1 (Steps (overObj (spec :> impl)).(Step)) ->
        exists thst1',  
            IsPathOf thst0' t thst1' (Steps (overObj (spec :> impl')).(Step)).
Admitted.