From LHL.Core Require Import
  Program
  Specs.

Record PendingState {E : ESig} := MkPend {
  ARetTy : Type;
  AName : ThreadName;
  ACall : E ARetTy
}.
Arguments MkPend {E}.
Arguments PendingState : clear implicits.

Variant RacyState {E A} :=
| DefState (s : A) (m : option (PendingState E))
| UBState.
Arguments RacyState : clear implicits.

Definition idleSt {E A} (s : A) : RacyState E A :=
  DefState s None.
Definition pendSt {E A} (s : A) (i : ThreadName) (m : E A) :=
  DefState s (Some (MkPend _ i m)).
Definition ubSt {E A} : RacyState E A :=
  UBState.