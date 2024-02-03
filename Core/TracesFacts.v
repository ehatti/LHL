From LHL.Util Require Import
  Util.

From LHL.Core Require Import
    Program
    Specs
    Traces
    Eutt.

Lemma nil_IsTraceOfSpec {E} :  
    forall (spec : Spec E),
    IsTraceOfSpec nil spec.
Proof.
    intros. exists spec.(Init). apply TransUtil.StepsNone.
Qed.

(* Eutt *)

Inductive euttTS_ {E E' : ESig}  (RR : IRel E E') :
    ThreadState (E := E) -> ThreadState (E := E') -> Prop :=
| euttTS_Idle : euttTS_ RR Idle Idle
| euttTS_Cont Ret p p' : 
    eutt RR p p' -> 
    euttTS_ RR (Cont (Ret := Ret) p) (Cont (Ret := Ret) p')
| euttTS_UCall A Ret k k' : 
    forall (x : A), eutt RR (k x) (k' x) ->
    euttTS_ RR (UCall k) (UCall (Ret := Ret) k').

Definition euttTS {E E' : ESig}  (RR : IRel E E') :
    ThreadsSt (E := E) -> ThreadsSt (E := E') -> Prop :=
    fun ths ths' => forall (i : ThreadName), euttTS_ RR (ths i) (ths' i).

