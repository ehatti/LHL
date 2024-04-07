From LHL.Core Require Import
    Program.

Definition ThreadName := nat.

Variant Event {E : ESig} :=
| CallEv {A} (m : E A)
| RetEv {A} (m : E A) (n : A).
Arguments Event : clear implicits.

Definition ThreadEvent (E : ESig) : Type := ThreadName * Event E.

Record Spec {E : ESig} : Type :=  {
    State : Type;
    Step : State -> ThreadEvent E -> State -> Prop;
    Init : State
}.
Arguments Spec : clear implicits.

Record Layer {E F : ESig} : Type := mkLayer {
    USpec : Spec E;
    LImpl : Impl E F; 
}.
Arguments Layer : clear implicits.
Arguments mkLayer {E F} USpec LImpl.
Notation "x :> y" := (mkLayer x y) (at level 80, right associativity).

Definition idLayer {E : ESig} (spec : Spec E) :=
    {|
        USpec := spec;
        LImpl := idImpl
    |}.

(* Layer Events *)

Variant LEvent {E F : ESig} :=
| UEvent (ev : option (Event E))
| OEvent (ev : Event F)
.
Arguments LEvent : clear implicits.

Definition Silent {E} : option (Event E) := None.

Definition ThreadLEvent E F : Type := nat * LEvent E F.

(* Layer Composition *)

Definition layVComp {E F G} (lay : Layer E F) (impl : Impl F G) : Layer E G :=
    {|
        USpec := lay.(USpec);
        LImpl := implVComp lay.(LImpl) impl
    |}.
Notation "x :|> y" := (layVComp x y) (at level 80, right associativity).