Inductive Steps_ {Ev State} 
    (step : State -> Ev -> State -> Prop) 
    (st : State) :
    list Ev -> 
    State 
    -> Prop :=
| StepsNone : Steps_ step st nil st
| StepsMore ev evs st'' st' : step st ev st'' -> Steps_ step st'' evs st' -> Steps_ step st (ev :: evs) st'
.

Definition Steps {Ev State} (step : State -> Ev -> State -> Prop) st evs st' 
    := Steps_ step st evs st'.

Lemma Steps_nil {E A} (step : A -> E -> A -> Prop) x y
  : Steps step x nil y <-> x = y.
Proof.
  split.
  - inversion 1; auto.
  - intros []; constructor.
Qed.

Lemma Steps_app {E A} (step : A -> E -> A -> Prop) (xs ys : list E) s s' s''
  : Steps step s xs s' -> Steps step s' ys s'' -> Steps step s  (xs ++ ys) s''.
Proof.
  unfold Steps.
  induction 1; cbn; auto.
  econstructor; eauto.
Qed.

Inductive PointStep {Index Ev State : Type} (step : State -> Ev -> State -> Prop)
  (ts : Index -> State) (n : Index * Ev)  (ts' : Index -> State) : Prop :=
| MkListStep :
    step (ts (fst n)) (snd n) (ts' (fst n)) ->
    (forall m, m <> fst n -> ts m = ts' m) ->
    PointStep step ts n ts'.

Definition IsPathOf {Ev State : Type} 
    (st : State) (t : list Ev) (st' : State) 
    (steps : State -> list Ev -> State -> Prop) : Prop := steps st t st'.

Definition Incl {A} (s : A -> Prop) (s' : A -> Prop) := forall a, s a -> s' a.