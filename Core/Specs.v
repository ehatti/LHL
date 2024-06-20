From LHL.Core Require Import
    Program.

Variant Event {E : ESig} :=
| CallEv {A} (m : E A)
| RetEv {A} (m : E A) (n : A).
Arguments Event : clear implicits.

Definition ThreadEvent T E : Type := {i : T & Event (E i)}.

Record Spec {T : Type} {E : T -> ESig} : Type :=  {
    State : Type;
    Step : State -> ThreadEvent T E -> State -> Prop;
    Init : State
}.
Arguments Spec : clear implicits.

Record Layer {T E F} : Type := mkLayer {
    USpec : Spec T E;
    LImpl : Impl E F; 
}.
Arguments Layer : clear implicits.
Arguments mkLayer {T E F} USpec LImpl.
Notation "x :> y" := (mkLayer x y) (at level 80, right associativity).

Definition idLayer {T E} (spec : Spec T E) :=
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

Definition ThreadLEvent A E F : Type := A * LEvent E F.

(* Layer Composition *)

Definition layVComp {T E F G} (lay : Layer T E F) (impl : Impl F G) : Layer T E G :=
    {|
        USpec := lay.(USpec);
        LImpl := implVComp lay.(LImpl) impl
    |}.
Notation "x :|> y" := (layVComp x y) (at level 80, right associativity).