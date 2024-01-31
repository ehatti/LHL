Notation IRel M N := (forall X, M X -> N X -> Prop) (only parsing).

Definition ieq {M : Type -> Type} R (e1 e2 : M R) : Prop := e1 = e2.
Hint Unfold ieq : core.