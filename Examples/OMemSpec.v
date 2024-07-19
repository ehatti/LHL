From LHL.Core Require Import
  Program
  Specs.

Variant OMemSig {A} : ESig :=
| Write (x : A) : OMemSig unit
| Read : OMemSig A.
Arguments OMemSig : clear implicits.

Variant OMemState {A} :=
| OMemInit
| OMemWriteRan (s : A)
| OMemCanRead (s : A) (m : bool)
| OMemUB.
Arguments OMemState : clear implicits.

Notation OMemIdle s := (OMemCanRead s false).
Notation OMemReadRan s := (OMemCanRead s true).

Variant OMemStep {T A} : OMemState A -> ThreadEvent T (OMemSig A) -> OMemState A -> Prop :=
| OMemCallWrite i s :
  OMemStep OMemInit (i, CallEv (Write s)) (OMemWriteRan s)
| OMemRetWrite i s :
  OMemStep (OMemWriteRan s) (i, RetEv (Write s) tt) (OMemIdle s)
| OMemCallRead i s :
  OMemStep (OMemIdle s) (i, CallEv Read) (OMemReadRan s)
| OMemRetRead i s :
  OMemStep (OMemReadRan s) (i, RetEv Read s) (OMemIdle s)
| OMemDoubleRead i s t :
  s <> OMemInit ->
  OMemStep s (i, CallEv (Write t)) OMemUB
| OMemStepUB e :
  OMemStep OMemUB e OMemUB.
Arguments OMemStep : clear implicits.

Program Definition omemSpec {T A} : Spec T (OMemSig A) := {|
  State := OMemState A;
  Step := OMemStep T A;
  Init := OMemInit
|}.

Admit Obligations.