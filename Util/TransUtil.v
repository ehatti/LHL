Require Import Coq.Program.Equality.

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

Inductive bwd_list {A} :=
| Start
| Snoc (xs : bwd_list) (x : A).
Arguments bwd_list : clear implicits.

Fixpoint bwd_app {A} (xs ys : bwd_list A) : bwd_list A :=
  match ys with
  | Start => xs
  | Snoc ys y => Snoc (bwd_app xs ys) y
  end.

Inductive BwdSteps {Ev State} 
    (step : State -> Ev -> State -> Prop) 
    (st : State) :
    bwd_list Ev -> 
    State 
    -> Prop :=
| BwdStepsNone : BwdSteps step st Start st
| BwdStepsMore ev evs st' st'' :
    BwdSteps step st evs st' ->
    step st' ev st'' ->
    BwdSteps step st (Snoc evs ev) st''
.



Fixpoint to_bwd {A} (xs : list A) : bwd_list A :=
  match xs with
  | nil => Start
  | cons x ys => bwd_app (Snoc Start x) (to_bwd ys)
  end.

Fixpoint from_bwd {A} (xs : bwd_list A) : list A :=
  match xs with
  | Start => nil
  | Snoc ys x => app (from_bwd ys) (cons x nil)
  end.

Lemma to_bwd_nil {A} (xs : list A) :
  Start = to_bwd xs ->
  xs = nil.
intros.
induction xs.
easy.
simpl in *.
Admitted.

Lemma BwdSteps_app {E A} (step : A -> E -> A -> Prop) (xs ys : bwd_list E) s s' s''
  : BwdSteps step s xs s' -> BwdSteps step s' ys s'' -> BwdSteps step s  (bwd_app xs ys) s''.
intros.
induction H0.
easy.
simpl.
econstructor.
exact IHBwdSteps.
easy.
Qed.

Lemma Steps_app {E A} (step : A -> E -> A -> Prop) (xs ys : list E) s s' s''
  : Steps step s xs s' -> Steps step s' ys s'' -> Steps step s  (xs ++ ys) s''.
Proof.
  unfold Steps.
  induction 1; cbn; auto.
  econstructor; eauto.
Qed.

Lemma Steps_iso {Ev State} {step : State -> Ev -> State -> Prop} (st st' : State) (xs : list Ev) :
  Steps step st xs st' ->
  BwdSteps step st (to_bwd xs) st'.
generalize dependent st'.
generalize dependent st.
generalize dependent xs.
fix rec 4.
intros.
destruct H.
constructor.
simpl.
eapply BwdSteps_app.
econstructor.
constructor.
exact H.
apply rec.
easy.
Qed.

Lemma BwdSteps_iso {Ev State} {step : State -> Ev -> State -> Prop} (st st' : State) (xs : list Ev) :
  BwdSteps step st (to_bwd xs) st' ->
  Steps step st xs st'.
generalize dependent st'.
generalize dependent st.
generalize dependent xs.
fix rec 4.
intros.
Admitted.

Lemma Steps_nil {E A} (step : A -> E -> A -> Prop) x y
  : Steps step x nil y <-> x = y.
Proof.
  split.
  - inversion 1; auto.
  - intros []; constructor.
Qed.

Inductive PointStep {Index Ev State : Type} (step : State -> Ev -> State -> Prop)
  (ts : Index -> State) (n : Index * Ev)  (ts' : Index -> State) : Prop :=
| MkListStep :
    step (ts (fst n)) (snd n) (ts' (fst n)) ->
    (forall m, m <> fst n -> ts m = ts' m) ->
    PointStep step ts n ts'.

Definition Incl {A} (s : A -> Prop) (s' : A -> Prop) := forall a, s a -> s' a.

Theorem Incl_refl {A} : 
  forall (s : A -> Prop),
    Incl s s.
Proof.
    unfold Incl. auto.
Qed.

Theorem Incl_trans {A} :
  forall (s s' s'' : A -> Prop),
    Incl s s' -> Incl s' s'' -> Incl s s''.
Proof. 
    unfold Incl. auto.
Qed.

Theorem Incl_antisym {A} : 
  forall (s s' : A -> Prop),
    Incl s s' -> Incl s' s -> 
    forall a , s a <-> s' a.
Proof.
  unfold Incl. intros. split; auto.
Qed.