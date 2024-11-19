From LHL.Core Require Import
  Program.

From Coq Require Import
  Arith.PeanoNat.

From LHL.Util Require Import
  TransUtil
  Util.

Definition Name T := {i | i < T}.

Variant Event {E : ESig} :=
| CallEv {A} (m : E A)
| RetEv {A} (m : E A) (n : A).
Arguments Event : clear implicits.

Definition ThreadEvent T (E : ESig) : Type := Name T * Event E.

Definition ActiveMap T (E : ESig) := Name T -> option {A & E A}.

Inductive SeqConsistent {T E} : ActiveMap T E -> list (ThreadEvent T E) -> Prop :=
| SCNil a : SeqConsistent a nil
| SCCall (a a' : ActiveMap T E) i A (m : E A) p :
    a i = None ->
    a' i = Some (existT _ _ m) ->
    differ_pointwise a a' i ->
    SeqConsistent a' p ->
    SeqConsistent a ((i, CallEv m) :: p)
| SCRet (a a' : ActiveMap T E) i A (m : E A) v p :
    a i = Some (existT _ _ m) ->
    a' i = None ->
    differ_pointwise a a' i ->
    SeqConsistent a' p ->
    SeqConsistent a ((i, RetEv m v) :: p).

Record Spec {T E} : Type := {
  State : Type;
  Step : State -> ThreadEvent T E -> State -> Prop;
  Init : State;
  seq_cons : forall p s,
    Steps Step Init p s ->
    SeqConsistent (fun _ => None) p
}.
Arguments Spec : clear implicits.

Record Layer {T} {E F : ESig} : Type := mkLayer {
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

Definition ThreadLEvent T E F : Type := Name T * LEvent E F.

(* Layer Composition *)

Definition layVComp {T E F G} (lay : Layer T E F) (impl : Impl F G) : Layer T E G :=
  {|
    USpec := lay.(USpec);
    LImpl := implVComp lay.(LImpl) impl
  |}.
Notation "x :|> y" := (layVComp x y) (at level 80, right associativity).