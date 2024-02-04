From LHL.Core Require Import
    Program.

Definition ThreadName := nat.

Variant Event {E : ESig} : Type :=
| CallEv {Ret : Type} (m : E Ret)
| RetEv {Ret : Type} (m : E Ret) (n : Ret)
.

Definition ThreadEvent (E : ESig) : Type := ThreadName * Event (E := E).

Record Spec {E : ESig} : Type := 
    {
        State : Type;
        Step : State -> ThreadEvent E -> State -> Prop;
        Init : State
    }.
Arguments Spec : clear implicits.

Record Layer {E F : ESig} : Type :=
    {
        USpec : Spec E;
        LImpl : Impl E F; 
    }.
Arguments Layer : clear implicits.

Definition mkLayer {E F : ESig} (spec : Spec E) (impl : Impl E F) : (Layer E F) := 
    {|
        USpec := spec;
        LImpl := impl
    |}.
Notation "x :> y" := (mkLayer x y) (at level 80, right associativity).

Definition idLayer {E : ESig} (spec : Spec E) :=
    {|
        USpec := spec;
        LImpl := idImpl
    |}.

(* Layer Events *)

Variant LEvent {E F : ESig} : Type :=
| OCallEv {Ret : Type} (m : F Ret)
| ORetEv {Ret : Type} (m : F Ret) (n : Ret)
| UCallEv {A : Type} (m : E A)
| URetEv {A : Type} (m : E A) (n : A)
| Silent
.

Definition ThreadLEvent {E F} : Type := nat * @LEvent E F.

(* Layer Composition *)

Definition layVComp {E F G} (lay : Layer E F) (impl : Impl F G) : Layer E G :=
    {|
        USpec := lay.(USpec);
        LImpl := implVComp lay.(LImpl) impl
    |}.
Notation "x :|> y" := (layVComp x y) (at level 80, right associativity).