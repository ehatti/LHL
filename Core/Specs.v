From LHL.Core Require Import
  Program.

From Coq Require Import
  Arith.PeanoNat.

From LHL.Util Require Import
  TransUtil
  Util.

Definition ThreadName := nat.

Variant Event {E : ESig} :=
| CallEv {A} (m : E A)
| RetEv {A} (m : E A) (n : A).
Arguments Event : clear implicits.

Definition ThreadEvent (E : ESig) : Type := ThreadName * Event E.

Definition ActiveMap (E : ESig) := ThreadName -> option {A & E A}.

Inductive SeqConsistent {E} : ActiveMap E -> list (ThreadEvent E) -> Prop :=
| SCNil a : SeqConsistent a nil
| SCCall (a a' : ActiveMap E) i A (m : E A) p :
    a i = None ->
    a' i = Some (existT _ _ m) ->
    differ_pointwise a a' i ->
    SeqConsistent a' p ->
    SeqConsistent a ((i, CallEv m) :: p)
| SCRet (a a' : ActiveMap E) i A (m : E A) v p :
    a i = Some (existT _ _ m) ->
    a' i = None ->
    differ_pointwise a a' i ->
    SeqConsistent a' p ->
    SeqConsistent a ((i, RetEv m v) :: p).

Record Spec {E} : Type := {
  State : Type;
  Step : State -> ThreadEvent E -> State -> Prop;
  Init : State;
  seq_cons : forall p s,
    Steps Step Init p s ->
    SeqConsistent (fun _ => None) p
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