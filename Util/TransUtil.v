From Coq Require Import
  Program.Equality
  Logic.FunctionalExtensionality
  Logic.PropExtensionality
  Logic.ClassicalChoice
  Init.Nat.

From LHL.Util Require Import
  Tactics
  Util.

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
Admitted.

Lemma bwd_app_nil {A} (xs : bwd_list A) :
  bwd_app Start xs = xs.
induction xs.
easy.
simpl.
f_equal.
easy.
Qed.

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

Lemma BwdSteps_app_inv {E A} (step : A -> E -> A -> Prop) (xs ys : bwd_list E) s s'' :
  BwdSteps step s (bwd_app xs ys) s'' ->
  exists s',
    BwdSteps step s xs s' /\
    BwdSteps step s' ys s''.
intros.
generalize dependent s''.
induction ys.
eexists.
split.
exact H.
constructor.
simpl in *.
intros.
dependent destruction H.
apply IHys in H. clear IHys.
destruct_all.
eexists.
split.
exact H.
econstructor.
exact H1.
easy.
Qed.

Lemma Steps_app {E A} (step : A -> E -> A -> Prop) (xs ys : list E) s s'' :
  (exists s', Steps step s xs s' /\ Steps step s' ys s'') =
  Steps step s  (xs ++ ys) s''.
apply propositional_extensionality.
firstorder.
induction H.
easy.
simpl.
econstructor.
exact H.
apply IHSteps_.
easy.
generalize dependent s.
induction xs.
intros.
exists s.
split.
constructor.
easy.
intros.
simpl in *.
dependent destruction H.
apply IHxs in H0.
destruct_all.
exists x.
split.
econstructor.
exact H.
easy.
easy.
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
fix rec 1.
intros.
destruct xs.
dependent destruction H.
constructor.
simpl in *.
eapply BwdSteps_app_inv in H.
destruct_all.
do 2 dependent destruction H.
econstructor.
exact H0.
apply rec.
easy.
Qed.

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

Fixpoint projPoint {A} i (t : list (nat * A)) : list A :=
  match t with
  | nil => nil
  | cons (j, x) t =>
    if eqb i j then
      x :: projPoint i t
    else
      projPoint i t 
  end.

Lemma help10 :
  forall (P Q : nat -> Prop),
    (forall i, P i /\ Q i) ->
    ((forall i, P i) /\ (forall i, Q i)).
firstorder.
Qed.

Lemma eqbT : forall n, eqb n n = true.
intros.
induction n; easy.
Qed.

Axiom excluded_middle : forall P, P \/ ~P.

Lemma eqbF : forall n m, n <> m -> n =? m = false.
fix rec 1.
intros.
destruct n, m.
congruence.
reflexivity.
reflexivity.
simpl.
apply rec.
congruence.
Qed.

Lemma decompPointSteps {E A : Type} (step : A -> E -> A -> Prop) :
  forall s p t,
  Steps (PointStep (Index:=nat) step) s p t =
  forall i,
    Steps step (s i) (projPoint i p) (t i).
intros.
apply propositional_extensionality.
firstorder.
{
  generalize dependent s.
  induction p.
  intros.
  dependent destruction H.
  constructor.
  intros.
  dependent destruction H.
  apply IHp in H0. clear IHp.
  dependent destruction H.
  destruct a.
  simpl in *.
  specialize (H0 i).
  assert (i = n \/ i <> n).
  apply excluded_middle.
  destruct H2.
  subst.
  rewrite eqbT.
  econstructor.
  exact H.
  easy.
  rewrite eqbF.
  apply H0 in H2.
  rewrite H2.
  easy.
  easy.
}
{
  generalize dependent s.
  induction p.
  intros.
  simpl in H.
  apply Steps_nil.
  extensionality i.
  specialize (H i).
  rewrite Steps_nil in H.
  easy.
  intros.
  destruct a.
  simpl in *.
  assert (
    forall i, exists r,
      (if i =? n then step (s i) e r else s i = r) /\
      Steps step r (projPoint i p) (t i)
  ).
  intros.
  specialize (H i).
  assert (i = n \/ i <> n).
  apply excluded_middle.
  destruct H0.
  subst.
  repeat rewrite eqbT in *.
  dependent destruction H.
  exists st''.
  firstorder.
  rewrite eqbF in *.
  exists (s i).
  easy.
  easy.
  easy.
  apply choice in H0.
  destruct_all.
  apply help10 in H0.
  destruct_all.
  eapply StepsMore with (st'':=x).
  2:{
    apply IHp.
    easy.
  }
  clear IHp H1.
  econstructor.
  all: simpl.
  specialize (H0 n).
  rewrite eqbT in H0.
  easy.
  intros.
  specialize (H0 m).
  rewrite eqbF in H0.
  easy.
  easy.
}
Qed.


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