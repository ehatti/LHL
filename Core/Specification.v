From Core Require Import
  Signature.

Definition Agent T := {i | i < T}.

Definition SeqEvent (E : Sig) :=
  {A & prod (E A) (option A)}.

Notation Evt m r := (existT _ _ (m, r)).
Notation InvEv m := (Evt m None).
Notation RetEv m v := (Evt m (Some v)).

Definition Event T E : Type := Agent T * SeqEvent E.

Record Spec {T E} : Type := {
  State : Type;
  Init : State;
  Step : State -> Event T E -> State -> Prop;
}.
Arguments Spec : clear implicits.
