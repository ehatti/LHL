Definition ESig : Type := Type -> Type.

Definition Sum (EL ER : ESig) (Ret : Type) := sum (EL Ret) (ER Ret).
Notation "E |+| F" := (Sum E F) (right associativity, at level 41).

Class SigCoercion {E F : ESig} :=
  coerceOp : forall A, E A -> F A.
Arguments SigCoercion : clear implicits.

Instance coerceId E : SigCoercion E E :=
  fun _ e => e.
Instance coerceSumLeft S E F `{SigCoercion S E} : SigCoercion S (Sum E F) :=
  fun _ s => inl (coerceOp _ s).
Instance coerceSumRight S E F `{SigCoercion S F} : SigCoercion S (Sum E F) :=
  fun _ s => inr (coerceOp _ s).

CoInductive Prog {E : ESig} {B : Type} : Type :=
| Vis {A} : E A -> (A -> Prog) -> Prog
| Return : B -> Prog
| Tau : Prog -> Prog.
Arguments Prog : clear implicits.
Arguments Return {E A} : rename.
Arguments Tau {E A} : rename.

Definition Impl {E : ESig} {F : ESig} := (forall R, F R -> Prog E R).
Arguments Impl : clear implicits.

(* Identity Program and Implementation *)
Definition idProg {E : ESig} {R : Type} : E R -> Prog E R := 
    fun e => (Vis e Return).

Definition idImpl {E : ESig} : Impl E E := 
    fun _ => idProg.

(* Program Operations *)

CoFixpoint bindProg {E A B} (p : Prog E A) (f : A -> Prog E B) : Prog E B :=
  match p with
    | Vis e f' => Vis e (fun x => bindProg (f' x) f)
    | Return a => f a
    | Tau p' => Tau (bindProg p' f)
  end.
Notation "x <- f ; m" := (bindProg f (fun x => m)) (at level 80, right associativity).
Notation "f ;; m" := (bindProg f (fun _ => m)) (at level 80, right associativity).

CoFixpoint mapProg
           {E E'}
           (f : forall A, E A -> E' A)
           {R}
           (p : Prog E R) :
  Prog E' R :=
  match p with
    | Vis e f' => Vis (f _ e) (fun a => mapProg f (f' a))
    | Return r => Return r
    | Tau p' => Tau (mapProg f p')
  end.

CoFixpoint substProg
           {E F}
           (impl : Impl E F)
           {R}
           (p : Prog F R) :
  Prog E R :=
  match p with
    | Vis m f => Tau (bindSubstProg impl f (impl _ m))
    | Return a => Return a
    | Tau p' => Tau (substProg impl p')
  end

with bindSubstProg
           {F F'} (impl : forall A, F' A -> Prog F A)
           {R R'} (f: R -> Prog F' R') (p: Prog F R) :=
  match p with
  | Vis m' f' => Vis m' (fun r => bindSubstProg impl f (f' r))
  | Return a => Tau (substProg impl (f a))
  | Tau p'' => Tau (bindSubstProg impl f p'')
  end.

Definition implVComp {E F G} (impl : Impl E F) (impl' : Impl F G) : Impl E G := 
    fun _ g => substProg impl (impl' _ g).

Notation "x |> y" := (implVComp x y) (at level 80, right associativity).

CoInductive progEq {E} {R}: Prog E R -> Prog E R -> Prop :=
| VisEq R' (e: E R') (f1: R' -> Prog E R) (f2: R' -> Prog E R):
    (forall v, progEq (f1 v) (f2 v)) ->
    progEq (Vis e f1) (Vis e f2)
| ReturnEq r:
    progEq (Return r) (Return r)
| NoopEq p1 p2:
    progEq p1 p2 ->
    progEq (Tau p1) (Tau p2).

Definition implEq {E F} (impl : Impl E F) (impl' : Impl E F) : Prop :=
  forall R (f : F R), progEq (impl R f) (impl' R f).

(* Control/extra constructs *)

Definition call {E F A} `{SigCoercion E F} (m : E A) : Prog F A :=
  Vis (coerceOp A m) Return.

Definition ret {E A} := @Return E A.

Definition skip {E} := @ret E unit tt.

Section while.

Context {E} (t : Prog E bool) (e : Prog E unit).

CoFixpoint whileAux (t' : Prog E bool) (e' : Prog E unit) : Prog E unit :=
  match t', e' with
  | Vis m k, e' => Vis m (fun x => whileAux (k x) e')
  | Tau t', e' => Tau (whileAux t' e')
  | Return false, _ => skip
  | Return true, Vis m k => Vis m (fun x => whileAux (Return true) (k x))
  | Return true, Tau e' => Tau (whileAux (Return true) e')
  | Return true, Return _ => Tau (whileAux t e)
  end.

Definition while := whileAux t e.

End while.

Variant ControlFlow {A} :=
| Break (v : A)
| Continue.
Arguments ControlFlow : clear implicits.

Section loop.

Context {E A} (e : Prog E (ControlFlow A)).

CoFixpoint loopAux (e' : Prog E (ControlFlow A)) : Prog E A :=
  match e' with
  | Return (Break v) => Return v
  | Return Continue => Tau (loopAux e)
  | Tau e' => Tau (loopAux e')
  | Vis m k => Vis m (fun x => loopAux (k x))
  end.

Definition loop := loopAux e.

End loop.