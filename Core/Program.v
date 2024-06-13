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
| Bind {A} : E A -> (A -> Prog) -> Prog
| Return : B -> Prog
| NoOp : Prog -> Prog.
Arguments Prog : clear implicits.
Arguments Return {E A} : rename.
Arguments NoOp {E A} : rename.

Definition Impl {E : ESig} {F : ESig} := (forall Ret, F Ret -> Prog E Ret).
Arguments Impl : clear implicits.

(* Identity Program and Implementation *)
Definition idProg {E : ESig} {Ret : Type} : E Ret -> Prog E Ret := 
    fun e => (Bind e Return).

Definition idImpl {E : ESig} : Impl E E := 
    fun Ret => idProg.

(* Program Operations *)

CoFixpoint bindProg {E A B} (p : Prog E A) (f : A -> Prog E B) : Prog E B :=
  match p with
    | Bind e f' => Bind e (fun x => bindProg (f' x) f)
    | Return a => f a
    | NoOp p' => NoOp (bindProg p' f)
  end.
Notation "x <- f ; m" := (bindProg f (fun x => m)) (at level 80, right associativity).

CoFixpoint mapProg
           {E E'}
           (f : forall A, E A -> E' A)
           {Ret}
           (p : Prog E Ret) :
  Prog E' Ret :=
  match p with
    | Bind e f' => Bind (f _ e) (fun a => mapProg f (f' a))
    | Return r => Return r
    | NoOp p' => NoOp (mapProg f p')
  end.

CoFixpoint substProg
           {E F}
           (impl : Impl E F)
           {Ret}
           (p : Prog F Ret) :
  Prog E Ret :=
  match p with
    | Bind m f => NoOp (bindSubstProg impl f (impl _ m))
    | Return a => Return a
    | NoOp p' => NoOp (substProg impl p')
  end

with bindSubstProg
           {F F'} (impl : forall A, F' A -> Prog F A)
           {R R'} (f: R -> Prog F' R') (p: Prog F R) :=
  match p with
  | Bind m' f' => Bind m' (fun r => bindSubstProg impl f (f' r))
  | Return a => NoOp (substProg impl (f a))
  | NoOp p'' => NoOp (bindSubstProg impl f p'')
  end.

Definition implVComp {E F G} (impl : Impl E F) (impl' : Impl F G) : Impl E G := 
    fun Ret g => substProg impl (impl' Ret g).

Notation "x |> y" := (implVComp x y) (at level 80, right associativity).

(* Control/extra constructs *)

Definition call {E F A} `{SigCoercion E F} (m : E A) : Prog F A :=
  Bind (coerceOp A m) Return.

Definition ret {E A} := @Return E A.

Definition skip {E} := @ret E unit tt.

CoFixpoint while {E} (x : Prog E bool) (e : Prog E unit) : Prog E unit :=
  match x with
  | Return true => e
  | Return false => skip
  | Bind m k => Bind m (fun x => while (k x) e)
  | NoOp x => NoOp (while x e)
  end.