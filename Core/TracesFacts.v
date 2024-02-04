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
        fun ost ost' => euttTS RR (fst ost) (fst ost').

Lemma eutt_InterStep {E F} (RR : IRel E E) (spec : Spec E) (impl : Impl E F) (impl' : Impl E F): 
    euttImpl RR impl impl' ->
    forall i ist0 ev ist1 ist0',
        euttIS (A := spec.(State)) RR ist0 ist0' ->
        InterStep (impl := impl) i ist0 ev ist1 ->
        exists ist1' ev',
            (ev' = ev \/ ev' = (i, Silent)) /\
            InterStep (impl := impl') i ist0' ev' ist1'.
Admitted.

Lemma euttTS_isPathOf {E F} (spec : Spec E) : 
    forall (impl : Impl E F) (impl' : Impl E F),
    forall t thst0 thst1 thst0', 
        euttIS ieq thst0 thst0' ->
        IsPathOf thst0 t thst1 (Steps (overObj (spec :> impl)).(Step)) ->
        exists thst1',  
            IsPathOf thst0' t thst1' (Steps (overObj (spec :> impl')).(Step)).
Admitted.