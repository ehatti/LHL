Lemma foo :
    forall P1 P2 Q1 Q2,
    (P1 /\ Q1 \/ P2 /\ Q2) <->
    ((P1 -> Q1) /\ (P2 -> Q2)).
split; intros.
{
    split.
    intros. destruct H.
    easy. easy.
}