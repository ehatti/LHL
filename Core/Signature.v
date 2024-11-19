Definition Sig := Type -> Type.

Declare Scope sig_scope.
Bind Scope sig_scope with Sig.
Delimit Scope sig_scope with Sig.

Definition Empty : Sig :=
  fun _ => Empty_set.
Notation "∅" := Empty : sig_scope.

Definition Union (E F : Sig) : Sig :=
  fun A => sum (E A) (F A).
Infix "∪" := Union (at level 40) : sig_scope.

