From LHL Require Import
  Program.

Section syntax.

Context {E : ESig}.

Definition ret {A} (v : A) : Prog E A :=
  Return v.

CoFixpoint bind {A B} (C : Prog E A) (k : A -> Prog E B) :=
  match C with
  | Bind m k' => Bind m (fun v => bind (k' v) k)
  | Return v => k v
  | NoOp C => NoOp (bind C k)
  end.

Definition call {A} (m : E A) : Prog E A :=
  Bind m Return.

End syntax.

Notation "x <- f ; m" := (bind f (fun x => m)) (at level 80, right associativity).