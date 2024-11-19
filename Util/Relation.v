From Util Require Import
  Map.

Definition Rel E A := A -> E -> A -> Prop.

Variant PtRel {E I A} {R : Rel E A} : Rel (I * E) (Map I A) :=
| MkPtRel m i e x y : R x e y -> PtRel (m [i ↦ x]) (i, e) (m [i ↦ y]).
Arguments PtRel {E I A} R.

Variant ConjRel {E A B} {RL : Rel E A} {RR : Rel E B} : Rel E (prod A B) :=
| MkConjRel e x z y w :
  RL x e z ->
  RR y e w ->
  ConjRel (x, y) e (z, w).
Arguments ConjRel {E A B} RL RR.

Variant DisjRel {E F A} {RL : Rel E A} {RR : Rel F A} : Rel (sum E F) A :=
| DisjRelLeft e x y :
  RL x e y ->
  DisjRel x (inl e) y
| DisjRelRight e x y :
  RR x e y ->
  DisjRel x (inr e) y.
Arguments DisjRel {E F A} RL RR.

Inductive Steps {E A} {R : Rel E A} : Rel (list E) A :=
| StepsNil x : Steps x nil x
| StepsCons e p x y z : R x e y -> Steps y p z -> Steps x (cons e p) z.
Arguments Steps {E A} R.