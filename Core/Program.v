From Core Require Import
  Signature.

(* Programs and modules *)

CoInductive Prog {E : Sig} {R : Type} :=
| Ret (v : R)
| Vis {A} (m : E A) (k : A -> Prog)
| Tau (e : Prog).
Arguments Prog : clear implicits.

Definition Mod (E F : Sig) :=
  forall R, F R -> Prog E R.

(* Identity module *)

Definition copy {E} : Mod E E :=
  fun _ m => Vis m Ret.

(* Program and module operations *)

CoFixpoint bind {E A B} (p : Prog E A) (k : A -> Prog E B) : Prog E B :=
  match p with
    | Vis e k' => Vis e (fun x => bind (k' x) k)
    | Ret v => k v
    | Tau e => Tau (bind e k)
  end.
