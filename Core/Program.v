Definition ESig : Type := Type -> Type.

CoInductive Prog {E : ESig} {Ret : Type} : Type :=
| Bind {A} : E A -> (A -> Prog) -> Prog
| Return : Ret -> Prog
| NoOp : Prog -> Prog.

Arguments Prog : clear implicits.

Notation "x <- f ; m" := (Bind f (fun x => m)) (at level 80, right associativity).

Definition Impl {E : ESig} {F : ESig} := (forall Ret, F Ret -> Prog E Ret).
Arguments Impl : clear implicits.

(* Identity Program and Implementation *)
Definition idProg {E : ESig} {Ret : Type} : E Ret -> Prog E Ret := 
    fun e => (x <- e ; Return x).

Definition idImpl {E : ESig} : Impl E E := 
    fun Ret => idProg.

(* Program Operations *)

CoFixpoint bindProg {E A B} (p : Prog E A) (f : A -> Prog E B) : Prog E B :=
  match p with
    | Bind e f' => x <- e; bindProg (f' x) f
    | Return a => f a
    | NoOp p' => NoOp (bindProg p' f)
  end.
Notation "x <-- f ; m" := (bindProg f (fun x => m)) (at level 80, right associativity).

CoFixpoint mapProg
           {E E'}
           (f : forall A, E A -> E' A)
           {Ret}
           (p : Prog E Ret) :
  Prog E' Ret :=
  match p with
    | @Bind _ _ A e f' => a <- f A e; mapProg f (f' a)
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
    | @Bind _ _ A m f => NoOp (bindSubstProg impl f (impl A m))
    | Return a => Return a
    | NoOp p' => NoOp (substProg impl p')
  end

with bindSubstProg
           {F F'} (impl : forall A, F' A -> Prog F A)
           {R R'} (f: R -> Prog F' R') (p: Prog F R) :=
  match p with
  | Bind m' f' => r <- m'; bindSubstProg impl f (f' r)
  | Return a => NoOp (substProg impl (f a))
  | NoOp p'' => NoOp (bindSubstProg impl f p'')
  end.

Definition implVComp {E F G} (impl : Impl E F) (impl' : Impl F G) : Impl E G := 
    fun Ret g => substProg impl (impl' Ret g).

Notation "x |> y" := (implVComp x y) (at level 80, right associativity).
