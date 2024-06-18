From Coq Require Import Eqdep.

Ltac injpair_ :=
  repeat
    lazymatch goal with
    | [ H : existT ?P ?R _ = existT ?P ?R _ |- _ ] => apply inj_pair2 in H
    end.

Ltac injpair :=
  subst; injpair_; subst.

Ltac inv H := inversion H; clear H; subst.

Ltac destruct_all :=
repeat lazymatch goal with
| [ H : ?P /\ ?Q |- _] => destruct H
| [ H : exists x, ?P |- _] => destruct H
end.

Axiom excluded_middle : forall P, P \/ ~P.

Ltac dec_eq_nats i j :=
  let H := fresh in
  assert (H : i = j \/ i <> j) by apply excluded_middle;
  destruct H; subst.

Axiom classicT : forall P : Prop, {P} + {~P}.