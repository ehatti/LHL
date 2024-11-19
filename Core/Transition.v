From Core Require Import
  Signature.

Definition Agent T := {i | i < T}.

Record SeqEvent {E : Sig} := MkSeqEv {
  ETyp : Type;
  EInv : E ETyp;
  ERet : option ETyp
}.
Arguments SeqEvent : clear implicits.
Arguments MkSeqEv {E}.
Notation Evt m r := (MkSeqEv _ m r).
Notation InvEv m := (MkSeqEv _ m None).
Notation RetEv m v := (MkSeqEv _ m (Some v)).

Record Event T E := {
  CAgt : Agent T;
  CEvt : SeqEvent E
}.

Record Spec {T E} : Type := {
  State : Type;
  Init : State;
  Step : State -> Event T E -> State -> Prop;
}.
Arguments Spec : clear implicits.
