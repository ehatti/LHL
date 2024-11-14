From LHL.Core Require Import
    Program
    Specs.

Variant CntSig : ESig :=
| Inc : CntSig unit
| Get : CntSig nat.

Variant CntState {T} :=
| CntDef (n : nat) (m : option (Name T * {A & CntSig A})).
Arguments CntState : clear implicits.

Notation cntPend s := (
    match s with
    | CntDef _ m => m
    end
).

Notation CntIdle n := (CntDef n None).
Notation CntRan n i m := (CntDef n (Some (i, existT _ _ m))).

Variant CntStep {T} : CntState T -> ThreadEvent T CntSig -> CntState T -> Prop :=
| CntCall i n A (m : CntSig A) : CntStep (CntIdle n) (i, CallEv m) (CntRan n i m)
| CntRetInc i n : CntStep (CntRan n i Inc) (i, RetEv Inc tt) (CntIdle (S n))
| CntRetGet i n : CntStep (CntRan n i Get)  (i, RetEv Get n) (CntIdle n).

Program Definition acntSpec {T} : Spec T CntSig := {|
    State := CntState T;
    Init := CntDef 0 None;
    Step := CntStep;
|}.

Next Obligation.
Admitted.