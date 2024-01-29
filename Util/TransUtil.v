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