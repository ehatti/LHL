From LHL.Core Require Import
  Program
  Traces
  Logic
  Specs.

Section wp.

Context
  {T E F} {A : Type}
  {VE : Spec T E} {VF : Spec T F}
  (M : Impl E F) (i : Name T)
  (m : F A) (Q : Post VE VF A).

Definition wp : Prec VE VF :=
  fun s ρs =>
    forall p t v,
      fst s i = Cont m (M A m) ->
      InterSteps (spec:=VE) M s p t ->
      fst t i = Cont m (Return v) ->
      exists σs,
        Q v s ρs t σs.

Lemma wp_weakest {G : Relt VE VF} e :
  w
  Commit i G wp e Q.


End wp.