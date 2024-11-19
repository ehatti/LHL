From Core Require Import
  Specification
  Signature
  Program.

From Util Require Import
  Relation
  Map.

Definition AgentState (E F : Sig) :=
  option ({R & prod (F R) (sum (Prog E R) {A & prod (E A) (A -> Prog E R)})}).
Notation Idle :=
  ( None
  : AgentState _ _ ).
Notation Cont m e :=
  ( Some (existT _ _ (m, inl e))
  : AgentState _ _ ).
Notation Call om um k :=
  ( Some (existT _ _ (om, inr (existT _ _ (um, k))))
  : AgentState _ _ ).

Definition AgentsState (T : nat) (E F : Sig) :=
  Map (Agent T) (AgentState E F).

Variant OSeqAgentStep {E F} {M : Mod E F} : Rel (SeqEvent F) (AgentState E F) :=
| OInvStep R (om : F R) :
  OSeqAgentStep Idle (InvEv om) (Cont om (M _ om))
| ORetStep R (om : F R) v :
  OSeqAgentStep (Cont om (Ret v)) (RetEv om v) Idle.
Arguments OSeqAgentStep {E F} M.

Variant USeqAgentStep {E F} : Rel (option (SeqEvent E)) (AgentState E F) :=
| UInvStep R (om : F R) A (um : E A) k :
  USeqAgentStep (Cont om (Vis um k)) (Some (InvEv um)) (Call om um k)
| URetStep R (om : F R) A (um : E A) k v :
  USeqAgentStep (Call om um k) (Some (RetEv um v)) (Cont om (k v))
| UTauStep R (om : F R) e :
  USeqAgentStep (Cont om (Tau e)) None (Cont om e).

Definition InterState T E F A :=
  prod (AgentsState T E F) A.

Definition LEvent T E F :=
  prod (Agent T) (sum (option (SeqEvent E)) (SeqEvent F)).

Definition UEvent T E :=
  prod (Agent T) (option (SeqEvent E)).

Definition AgentStep {T E F} (M : Mod E F)
: Rel (LEvent T E F) (AgentsState T E F) :=
  PtRel (DisjRel USeqAgentStep (OSeqAgentStep M)).

Definition ConcreteStep {T E F} (VE : Spec T E)
: Rel (LEvent T E F) VE.(State) :=
  fun s '(i, e) t =>
    match e with
    | inl (Some e) => VE.(Step) s (i, e) t
    | _ => s = t
    end.
  
Definition UnderConcreteStep {T E} (VE : Spec T E)
: Rel (UEvent T E) VE.(State) :=
  fun s '(i, e) t =>
    match e with
    | Some e => VE.(Step) s (i, e) t
    | _ => s = t
    end.

Definition UnderInterStep {T E F}
  (VE : Spec T E)
: Rel (UEvent T E) (InterState T E F VE.(State)) :=
  ConjRel (PtRel USeqAgentStep) (UnderConcreteStep VE).

Definition InterStep {T E F}
  (VE : Spec T E) (M : Mod E F)
: Rel (LEvent T E F) (InterState T E F VE.(State)) :=
  ConjRel (AgentStep M) (ConcreteStep VE).

Definition InterSteps {T E F}
  (VE : Spec T E) (M : Mod E F)
: Rel (list (LEvent T E F)) (InterState T E F VE.(State)) :=
  Steps (InterStep VE M).