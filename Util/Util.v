Notation IRel M N := (forall X, M X -> N X -> Prop) (only parsing).

Definition ieq {M : Type -> Type} R (e1 e2 : M R) : Prop := e1 = e2.
Hint Unfold ieq : core.

Definition irespectful {M1 M2 N1 N2 : Type -> Type}
           (RM : IRel M1 M2)
           (RN : IRel N1 N2)
           (f1 : forall T, M1 T -> N1 T)
           (f2 : forall T, M2 T -> N2 T)
  : Prop :=
  forall T e1 e2, RM T e1 e2 -> RN T (f1 T e1) (f2 T e2).

Declare Scope isig_scope.
Delimit Scope isig_scope with isig.
Infix "==>" := irespectful (right associativity, at level 55) : isig_scope.