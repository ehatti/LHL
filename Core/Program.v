Definition ESig : Type := Type -> Type.

CoInductive Prog {E : ESig} {Ret : Type} : Type :=
| Bind {A} : E A -> (A -> Prog) -> Prog
| Return : Ret -> Prog
| Noop : Prog -> Prog.

Arguments Prog : clear implicits.

Notation "x <- f ; m" := (Bind f (fun x => m)) (at level 80, right associativity).

Definition idProg {E : ESig} {Ret : Type} : E Ret -> Prog E Ret := 
    fun e => (x <- e ; Return x).

Definition Mod {E : ESig} {F : ESig} := (forall Ret, F Ret -> Prog E Ret).
Arguments Mod : clear implicits.

Definition idMod {E : ESig} : Mod E E := 
    fun Ret => idProg.

Definition ThreadName := nat.

Variant Event {E : ESig} : Type :=
| CallEv {Ret : Type} (m : E Ret)
| RetEv {Ret : Type} (n : Ret)
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
        Obj : Spec E;
        Impl : Mod E F; 
    }.

(* Layer Events *)

Variant LEvent {E F : ESig} : Type :=
| OCallEv {Ret : Type} (m : F Ret)
| ORetEv {Ret : Type} (n : Ret)
| UCallEv {A : Type} (m : E A)
| URetEv {A : Type} (n : A)
.

Definition ThreadLEvent {E F} : Type := nat * @LEvent E F.
