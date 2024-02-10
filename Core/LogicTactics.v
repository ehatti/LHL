From LHL Require Import
    Logic
    Linearizability
    Traces.

Ltac psimpl :=
repeat lazymatch goal with
| [ H : ReltCompose ?P ?Q ?s ?ρ ?t ?σ |- ?G] => destruct H
| [ H : PrecCompose ?P ?Q ?s ?ρ |- ?G] => destruct H
| [ H : ?P /\ ?Q |- ?G ] => destruct H
| [ H : exists x, ?P |- ?G ] => destruct H
| [ H : Invoke ?impl ?i ?A ?l ?s ?ρ ?t ?σ |- ?G ] => destruct H
| [ H : LinRw ?ρ ?σ |- ?G ] => destruct H
end;
repeat lazymatch goal with
| [ H : InterStep ?i ?st ?ev ?st' |- ?G ] => dependent destruction H
| [ H : Step ?impl ?st ?ev ?st' |- ?G ] => idtac ev; simpl in H; dependent destruction H
end;
simpl in *;
subst;
repeat lazymatch goal with
| [ H : ?A, H' : ?A |- ?G] => clear H'
end.

Ltac psplit :=
match goal with
| [ |- ReltCompose ?P ?Q ?s ?ρ ?t ?σ ] =>
    do 2 eexists; split
| [ |- PrecCompose ?P ?Q ?s ?ρ ] =>
    do 2 eexists; split
| [ |- ?G ] => fail "Cannot split on this goal"
end.

Ltac pdestruct H :=
match type of H with
| ReltCompose ?P ?Q ?s ?ρ ?t ?σ => do 3 destruct H
| PrecCompose ?P ?Q ?s ?ρ => do 3 destruct H
| _ => fail "Cannot destruct this hypothesis"
end.

Lemma stableHelp {E VE F} {R : @Relt E VE F} {Q} :
    Stable R Q ->
    forall s ρ t σ,
    (((R >> Q) s ρ t σ) \/ ((Q >> R) s ρ t σ)) ->
    Q s ρ t σ.
intros.
destruct H.
destruct H0.
apply H.
easy.
apply H1.
easy.
Qed.

Ltac stable :=
match goal with
| [ H : @Stable _ _ _ _ stablePrec ?R ?P |- ?P ?s ?ρ ] => apply H
| [ H : @Stable _ _ _ _ stableRelt ?R ?Q |- ?Q ?s ?ρ ?t ?σ ] => apply (stableHelp H)
end.