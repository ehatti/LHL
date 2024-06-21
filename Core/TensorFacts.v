From LHL.Core Require Import
  Program
  ProgramFacts
  Specs
  Traces
  Tensor
  TracesFacts
  Simulates
  SimulatesFacts.

From LHL.Util Require Import
  TransUtil
  Tactics
  Util.

From Coq Require Import
  Program.Equality
  Arith.PeanoNat
  Logic.FunctionalExtensionality
  Lists.List.
Import ListNotations.

Fixpoint projLeft {E F} (p : Trace (ThreadEvent (E |+| F))) : Trace (ThreadEvent E) :=
  match p with
  | nil => nil
  | cons (i, CallEv (inl e)) p => cons (i, CallEv e) (projLeft p)
  | cons (i, RetEv (inl e) v) p => cons (i, RetEv e v) (projLeft p)
  | cons _ p => projLeft p
  end.

Fixpoint liftLeft {E F} (p : Trace (ThreadEvent E)) : Trace (ThreadEvent (E |+| F)) :=
  match p with
  | nil => nil
  | cons (i, CallEv e) p => cons (i, CallEv (inl e)) (liftLeft p)
  | cons (i, RetEv e v) p => cons (i, RetEv (inl e) v) (liftLeft p)
  end.

Fixpoint projRight {E F} (p : Trace (ThreadEvent (E |+| F))) : Trace (ThreadEvent F) :=
  match p with
  | nil => nil
  | cons (i, CallEv (inr e)) p => cons (i, CallEv e) (projRight p)
  | cons (i, RetEv (inr e) v) p => cons (i, RetEv e v) (projRight p)
  | cons _ p => projRight p
  end.
  
Fixpoint liftRight {E F} (p : Trace (ThreadEvent F)) : Trace (ThreadEvent (E |+| F)) :=
  match p with
  | nil => nil
  | cons (i, CallEv e) p => cons (i, CallEv (inr e)) (liftRight p)
  | cons (i, RetEv e v) p => cons (i, RetEv (inr e) v) (liftRight p)
  end.

Lemma liftEx {A} {P : A -> Prop} {Q} :
  ((exists x, P x) -> Q) <-> (forall x, P x -> Q).
split; intros.
apply H.
exists x. easy.
destruct_all.
eapply H. exact H0.
Qed.

(* Note to Eashan: This is proven by C4 in Traces_Pair.v, see ConcTraceIncl_pairObject *)
Theorem tensor_monotonic {E F} :
  forall (specE specE' : Spec E) (specF specF' : Spec F) ,
  specRefines specE specE' ->
  specRefines specF specF' -> 
  specRefines (tensorSpec specE specF) (tensorSpec specE' specF').
Proof.
unfold specRefines, Incl, IsTraceOfSpec. intros. cbn in *.
destruct_all. specialize (H (projLeft a)). specialize (H0 (projRight a)).
rewrite liftEx in H. rewrite liftEx in H0.
specialize (H x.(LState)). specialize (H0 x.(RState)).
assert (exists st, Steps (Step specE') (Init specE') (projLeft a) st).
{
  clear H0. apply H. clear H.
  generalize dependent (Init specE). generalize dependent (Init specF).
  generalize dependent (fun _ : ThreadName => @None {A & (E |+| F) A}).
  induction a.
  {
    cbn. intros. dependent destruction H1.
    constructor.
  }
  {
    cbn. intros. dependent destruction H1.
    destruct a, e, m; cbn in *; destruct_all; subst.
    {
      econstructor. exact H. destruct st''. cbn in *.
      eapply IHa. exact H1.
    }
    {
      destruct st''. cbn in *.
      eapply IHa. exact H1.
    }
    {
      econstructor. exact H. destruct st''. cbn in *.
      eapply IHa. exact H1.
    }
    {
      destruct st''. cbn in *.
      eapply IHa. exact H1.
    }
  }
}
assert (exists st, Steps (Step specF') (Init specF') (projRight a) st).
{
  clear H H2. apply H0. clear H0.
  generalize dependent (Init specE). generalize dependent (Init specF).
  generalize dependent (fun _ : ThreadName => @None {A & (E |+| F) A}).
  induction a.
  {
    cbn. intros. dependent destruction H1.
    constructor.
  }
  {
    cbn. intros. dependent destruction H1.
    destruct a, e, m; cbn in *; destruct_all; subst.
    {
      destruct st''. cbn in *.
      eapply IHa. exact H1.
    }
    {
      econstructor. exact H. destruct st''. cbn in *.
      eapply IHa. exact H1.
    }
    {
      destruct st''. cbn in *.
      eapply IHa. exact H1.
    }
    {
      econstructor. exact H. destruct st''. cbn in *.
      eapply IHa. exact H1.
    }
  }
}
clear H H0. destruct_all.
generalize dependent (Init specE). generalize dependent (Init specF).
generalize dependent (Init specE'). generalize dependent (Init specF').
generalize dependent (fun _ : ThreadName => @None {A & (E |+| F) A}).
induction a; cbn in *; intros.
{
  repeat econstructor.
}
{
  destruct a, e, m; dependent destruction H1;
  unfold TensorStep in H1; cbn in *; destruct_all;
  subst; destruct st''; cbn in *.
  {
    dependent destruction H0.
    eapply IHa in H6. 2: exact H. 2: exact H1.
    destruct_all. exists x2.
    eapply StepsMore with (st'':={|
      TActive := TActive
    |}).
    unfold TensorStep. cbn. repeat split.
    exact H0. easy. easy. easy. easy.
  }
  {
    dependent destruction H.
    eapply IHa in H6. 2: exact H0. 2: exact H1.
    destruct_all. exists x2.
    eapply StepsMore with (st'':={|
      TActive := TActive
    |}).
    unfold TensorStep. cbn. repeat split.
    exact H. easy. easy. easy. easy.
  }
  {
    dependent destruction H0.
    eapply IHa in H6. 2: exact H. 2: exact H1.
    destruct_all. exists x2.
    eapply StepsMore with (st'':={|
      TActive := TActive
    |}).
    unfold TensorStep. cbn. repeat split.
    exact H0. easy. easy. easy. easy.
  }
  {
    dependent destruction H.
    eapply IHa in H6. 2: exact H0. 2: exact H1.
    destruct_all. exists x2.
    eapply StepsMore with (st'':={|
      TActive := TActive
    |}).
    unfold TensorStep. cbn. repeat split.
    exact H. easy. easy. easy. easy.
  }
}
Qed.

Check MkTS.

Definition tensorLeftActiveMap {E F} (a : TensorActive E F) : ThreadName -> option {A & E A} :=
  fun i => match a i with
  | Some (existT _ _ (inl m)) => Some (existT _ _ m)
  | _ => None
  end.

Definition tensorNoRight {E F} (a : TensorActive E F) :=
  forall i,
    ~(exists A (m : F A), a i = Some (existT _ _ (inr m))).

Lemma eq_help {A} :
  forall x y : A, x = y -> x ~= y.
intros. rewrite H. easy.
Qed.

Lemma tensor_liftLeft_trivial {E F} :
  forall (specE : Spec E) (specF : Spec F),
  forall s t c p a,
  SeqConsistent (tensorLeftActiveMap a) p ->
  tensorNoRight a ->
  (exists a', Steps (TensorStep specE specF) (MkTS a s c) (liftLeft p) (MkTS a' t c)) <->
  Steps (Step specE) s p t.
split; intros.
{
  clear H H0.
  generalize dependent a. generalize dependent s.
  induction p; cbn; intros.
  {
    destruct_all. dependent destruction H.
    constructor.
  }
  {
    destruct_all. destruct a, e.
    dependent destruction H. unfold TensorStep in H. cbn in *.
    destruct_all. subst. destruct st''. cbn in *.
    econstructor. exact H. eapply IHp. eexists. exact H0.
    dependent destruction H. unfold TensorStep in H. cbn in *.
    destruct_all. subst. destruct st''. cbn in *.
    econstructor. exact H. eapply IHp. eexists. exact H0.
  }
}
{
  generalize dependent s. generalize dependent a.
  induction p; cbn; intros.
  {
    dependent destruction H1.
    repeat econstructor.
  }
  dependent destruction H; dependent destruction H4.
  {
    assert (
      (tensorLeftActiveMap (F:=F) (fun j => if i =? j then Some (existT _ _ (inl m)) else a0 j) = a')
    ).
    {
      extensionality j.
      dec_eq_nats i j.
      {
        unfold tensorLeftActiveMap. rewrite eqb_id. easy.
      }
      {
        rewrite H1. 2: easy. unfold tensorLeftActiveMap.
        rewrite eqb_nid. easy. easy.
      }
    }
    apply IHp with
      (a:=fun j =>
        if i =? j then
          Some (existT _ _ (inl m))
        else
          a0 j) in H5.
    2:{ rewrite H6 at 1. easy. }
    2:{
      assert (H3' := H3).
      unfold tensorNoRight. intros. specialize (H3 i0). move H3 at bottom.
      unfold not. intros. apply H3. clear H3.
      destruct_all.
      dec_eq_nats i i0.
      { rewrite eqb_id in H3. dependent destruction H3. }
      {
        rewrite eqb_nid in H3.
        specialize (H3' i0). exfalso.
        apply H3'. rewrite H3. repeat econstructor.
        easy.
      }
    }
    destruct_all.
    exists x. eapply StepsMore with
      (st'':= MkTS (fun j =>
        if i =? j then
          Some (existT _ _ (inl m))
        else
          a0 j) _ _). cbn.
    split. exact H4.
    split.
    {
      unfold tensorLeftActiveMap in H. specialize (H3 i).
      destruct (a0 i). destruct s0, s0.
      discriminate.
      exfalso. apply H3. repeat econstructor.
      easy.
    }
    split. rewrite eqb_id. easy.
    split. apply differ_pointwise_trivial.
    easy.
    easy.
  }
  {
    assert (
      (tensorLeftActiveMap (F:=F) (fun j => if i =? j then None else a0 j) = a')
    ).
    {
      extensionality j.
      dec_eq_nats i j.
      {
        unfold tensorLeftActiveMap. rewrite eqb_id. easy.
      }
      {
        rewrite H1. 2: easy. unfold tensorLeftActiveMap.
        rewrite eqb_nid. easy. easy.
      }
    }
    apply IHp with
      (a:=fun j =>
        if i =? j then
          None
        else
          a0 j) in H5.
    2:{ rewrite H6 at 1. easy. }
    2:{
      assert (H3' := H3).
      unfold tensorNoRight. intros. specialize (H3 i0). move H3 at bottom.
      unfold not. intros. apply H3. clear H3.
      destruct_all.
      dec_eq_nats i i0.
      { rewrite eqb_id in H3. dependent destruction H3. }
      {
        rewrite eqb_nid in H3.
        specialize (H3' i0). exfalso.
        apply H3'. rewrite H3. repeat econstructor.
        easy.
      }
    }
    destruct_all.
    exists x. eapply StepsMore with
      (st'':= MkTS (fun j =>
        if i =? j then
          None
        else
          a0 j) _ _). cbn.
    split. exact H4.
    split.
    {
      unfold tensorLeftActiveMap in H. specialize (H3 i).
      destruct (a0 i). destruct s0, s0.
      dependent destruction H. easy.
      exfalso. apply H3. repeat econstructor.
      easy.
    }
    split. rewrite eqb_id. easy.
    split. apply differ_pointwise_trivial.
    easy.
    easy.
  }
}
Qed.

Definition tensorRightActiveMap {E F} (a : TensorActive E F) : ThreadName -> option {A & F A} :=
  fun i => match a i with
  | Some (existT _ _ (inr m)) => Some (existT _ _ m)
  | _ => None
  end.

Definition tensorNoLeft {E F} (a : TensorActive E F) :=
  forall i,
    ~(exists A (m : E A), a i = Some (existT _ _ (inl m))).

Lemma tensor_liftRight_trivial {E F} :
  forall (specE : Spec E) (specF : Spec F),
  forall s t c p a,
  SeqConsistent (tensorRightActiveMap a) p ->
  tensorNoLeft a ->
  (exists a', Steps (TensorStep specE specF) (MkTS a c s) (liftRight p) (MkTS a' c t)) <->
  Steps (Step specF) s p t.
split; intros.
{
  clear H H0.
  generalize dependent a. generalize dependent s.
  induction p; cbn; intros.
  {
    destruct_all. dependent destruction H.
    constructor.
  }
  {
    destruct_all. destruct a, e.
    dependent destruction H. unfold TensorStep in H. cbn in *.
    destruct_all. subst. destruct st''. cbn in *.
    econstructor. exact H. eapply IHp. eexists. exact H0.
    dependent destruction H. unfold TensorStep in H. cbn in *.
    destruct_all. subst. destruct st''. cbn in *.
    econstructor. exact H. eapply IHp. eexists. exact H0.
  }
}
{
  generalize dependent s. generalize dependent a.
  induction p; cbn; intros.
  {
    dependent destruction H1.
    repeat econstructor.
  }
  dependent destruction H; dependent destruction H4.
  {
    assert (
      (tensorRightActiveMap (E:=E) (F:=F) (fun j => if i =? j then Some (existT _ _ (inr m)) else a0 j) = a')
    ).
    {
      extensionality j.
      dec_eq_nats i j.
      {
        unfold tensorRightActiveMap. rewrite eqb_id. easy.
      }
      {
        rewrite H1. 2: easy. unfold tensorRightActiveMap.
        rewrite eqb_nid. easy. easy.
      }
    }
    apply IHp with
      (a:=fun j =>
        if i =? j then
          Some (existT _ _ (inr m))
        else
          a0 j) in H5.
    2:{ rewrite H6 at 1. easy. }
    2:{
      assert (H3' := H3).
      unfold tensorNoLeft. intros. specialize (H3 i0). move H3 at bottom.
      unfold not. intros. apply H3. clear H3.
      destruct_all.
      dec_eq_nats i i0.
      { rewrite eqb_id in H3. dependent destruction H3. }
      {
        rewrite eqb_nid in H3.
        specialize (H3' i0). exfalso.
        apply H3'. rewrite H3. repeat econstructor.
        easy.
      }
    }
    destruct_all.
    exists x. eapply StepsMore with
      (st'':= MkTS (fun j =>
        if i =? j then
          Some (existT _ _ (inr m))
        else
          a0 j) _ _). cbn.
    split. exact H4.
    split.
    {
      unfold tensorRightActiveMap in H. specialize (H3 i).
      destruct (a0 i). destruct s0, s0.
      exfalso. apply H3. repeat econstructor.
      easy.
      easy.
    }
    split. rewrite eqb_id. easy.
    split. apply differ_pointwise_trivial.
    easy.
    easy.
  }
  {
    assert (
      (tensorRightActiveMap (F:=F) (fun j => if i =? j then None else a0 j) = a')
    ).
    {
      extensionality j.
      dec_eq_nats i j.
      {
        unfold tensorRightActiveMap. rewrite eqb_id. easy.
      }
      {
        rewrite H1. 2: easy. unfold tensorRightActiveMap.
        rewrite eqb_nid. easy. easy.
      }
    }
    apply IHp with
      (a:=fun j =>
        if i =? j then
          None
        else
          a0 j) in H5.
    2:{ rewrite H6 at 1. easy. }
    2:{
      assert (H3' := H3).
      unfold tensorNoLeft. intros. specialize (H3 i0). move H3 at bottom.
      unfold not. intros. apply H3. clear H3.
      destruct_all.
      dec_eq_nats i i0.
      { rewrite eqb_id in H3. dependent destruction H3. }
      {
        rewrite eqb_nid in H3.
        specialize (H3' i0). exfalso.
        apply H3'. rewrite H3. repeat econstructor.
        easy.
      }
    }
    destruct_all.
    exists x. eapply StepsMore with
      (st'':= MkTS (fun j =>
        if i =? j then
          None
        else
          a0 j) _ _). cbn.
    split. exact H4.
    split.
    {
      unfold tensorRightActiveMap in H. specialize (H3 i).
      destruct (a0 i). destruct s0, s0.
      exfalso. apply H3. repeat econstructor.
      dependent destruction H. easy.
      easy.
    }
    split. rewrite eqb_id. easy.
    split. apply differ_pointwise_trivial.
    easy.
    easy.
  }
}
Qed.

Lemma tensor_liftLeft_const {E F} :
  forall (specE : Spec E) (specF : Spec F),
  forall s t c c' a a' p,
  Steps (TensorStep specE specF) (MkTS a s c) (liftLeft p) (MkTS a' t c') ->
  c = c'.
intros. generalize dependent a. generalize dependent s. generalize dependent c.
induction p; cbn; intros.
{
  dependent destruction H.
  easy.
}
{
  destruct a, e; dependent destruction H;
  cbn in H; destruct_all; subst; destruct st'';
  eapply IHp; exact H0.
}
Qed.

Lemma tensor_liftRight_const {E F} :
  forall (specE : Spec E) (specF : Spec F),
  forall s t c c' a a' p,
  Steps (TensorStep specE specF) (MkTS a c s) (liftRight p) (MkTS a' c' t) ->
  c = c'.
intros. generalize dependent a. generalize dependent s. generalize dependent c.
induction p; cbn; intros.
{
  dependent destruction H.
  easy.
}
{
  destruct a, e; dependent destruction H;
  cbn in H; destruct_all; subst; destruct st'';
  eapply IHp; exact H0.
}
Qed.

(* Note to Eashan: This is also seems to be proven by C4 in Traces_Pair.v *)
Theorem tensor_monotonic_inv {E F} : 
  forall (specE specE' : Spec E) (specF specF' : Spec F), 
    specRefines (tensorSpec specE specF) (tensorSpec specE' specF') ->
    specRefines specE specE' /\ specRefines specF specF'.
unfold specRefines, Incl, IsTraceOfSpec. intros.
split.
{
  intros. destruct_all. specialize (H (liftLeft a)). cbn in *.
  assert (
    exists st, Steps (TensorStep specE' specF') (MkTS (fun _ => None) (Init specE') (Init specF')) (liftLeft a) st
  ).
  {
    apply H.
    rewrite <- (tensor_liftLeft_trivial (E:=E) (F:=F)) with
      (specF:=specF)
      (a:=fun _ => None)
      (c:= Init specF)
      in H0.
    destruct_all.
    eexists. exact H0.
    eapply specE.(seq_cons). exact H0.
    unfold tensorNoRight. intros.
    unfold not. intros. destruct_all. discriminate.
  }
  destruct_all.
  destruct x0.
  exists LState.
  erewrite <- (tensor_liftLeft_trivial (F:=F)) with
    (specF:=specF')
    (c:= Init specF')
    (a:=fun _ => None).
  2:{ eapply (specE.(seq_cons)). exact H0. }
  2:{
    unfold tensorNoRight. unfold not.
    intros. destruct_all. discriminate.
  }
  exists TActive.
  assert (Init specF' = RState).
  eapply tensor_liftLeft_const. exact H1.
  cbn. rewrite H2 at 2. easy.
}
{
  intros. destruct_all. specialize (H (liftRight a)). cbn in *.
  assert (
    exists st, Steps (TensorStep specE' specF') (MkTS (fun _ => None) (Init specE') (Init specF')) (liftRight a) st
  ).
  {
    apply H.
    rewrite <- (tensor_liftRight_trivial (E:=E) (F:=F)) with
      (specE:=specE)
      (a:=fun _ => None)
      (c:= Init specE)
      in H0.
    destruct_all.
    eexists. exact H0.
    eapply specF.(seq_cons). exact H0.
    unfold tensorNoLeft. intros.
    unfold not. intros. destruct_all. discriminate.
  }
  destruct_all.
  destruct x0.
  exists RState.
  erewrite <- (tensor_liftRight_trivial (E:=E)) with
    (specE:=specE')
    (c:= Init specE')
    (a:=fun _ => None).
  2:{ eapply (specF.(seq_cons)). exact H0. }
  2:{
    unfold tensorNoLeft. unfold not.
    intros. destruct_all. discriminate.
  }
  exists TActive.
  assert (Init specE' = LState).
  eapply tensor_liftRight_const. exact H1.
  cbn. rewrite H2 at 2. easy.
}
Qed.

Theorem tensor_neutral {E F} : 
  implEq (tensorImpl (@idImpl E) (@idImpl F)) (@idImpl (E |+| F)).
unfold implEq. intros.
destruct f.
{
  cbn. unfold idImpl, idProg.
  rewrite frobProgId at 1. cbn.
  constructor.
  intros.
  rewrite frobProgId at 1. cbn.
  constructor.
}
{
  cbn. unfold idImpl, idProg.
  rewrite frobProgId at 1. cbn.
  constructor.
  intros.
  rewrite frobProgId at 1. cbn.
  constructor.
}
Qed.

Lemma swapEx {A B} {P : A -> B -> Prop} :
  (exists x y, P x y) ->
  (exists y x, P x y).
intros. destruct_all. repeat eexists. exact H.
Qed.

Definition isIdle {E F} (s : ThreadState E F) :=
  match s with Idle => true | _ => false end.

Definition tensorTS {E E' F F'} (s : ThreadState E E') (t : ThreadState F F') : ThreadState (E |+| F) (E' |+| F') :=
  match s with
  | Idle =>
    match t with
    | Idle => Idle
    | Cont m p => Cont (inr m) (mapProg (fun _ => inr) p)
    | UCall om um k => UCall (inr om) (inr um) (fun x => mapProg (fun _ => inr) (k x))
    end
  | Cont m p => Cont (inl m) (mapProg (fun _ => inl) p)
  | UCall om um k => UCall (inl om) (inl um) (fun x => mapProg (fun _ => inl) (k x))
  end.

Lemma split_tensor_steps {E F} :
  forall (specE : Spec E) (specF : Spec F),
  forall p tL tR sL sR a a',
  Steps (TensorStep specE specF) (MkTS a sL sR) p (MkTS a' tL tR) ->
  Steps (Step specE) sL (projLeft p) tL /\
  Steps (Step specF) sR (projRight p) tR.
intros specE specF p tL tR. induction p;
intros; cbn in *; dependent destruction H.
{
  repeat constructor.
}
{
  destruct a, e, m; unfold TensorStep in H;
  destruct_all; destruct st''; cbn in *; subst;
  apply IHp in H0; destruct_all.
  split. econstructor. exact H. easy. easy.
  split. easy. econstructor. exact H. easy.
  split. econstructor. exact H. easy. easy.
  split. easy. econstructor. exact H. easy.
}
Qed.

Definition liftTSLeft {E E' F F'} (s : ThreadState E E') : ThreadState (E |+| F) (E' |+| F') :=
  match s with
  | Idle => Idle
  | Cont m p => Cont (inl m) (mapProg (fun _ => inl) p)
  | UCall om um k => UCall (inl om) (inl um) (fun x => mapProg (fun _ => inl) (k x))
  end.

Definition liftTSRight {E E' F F'} (s : ThreadState F F') : ThreadState (E |+| F) (E' |+| F') :=
  match s with
  | Idle => Idle
  | Cont m p => Cont (inr m) (mapProg (fun _ => inr) p)
  | UCall om um k => UCall (inr om) (inr um) (fun x => mapProg (fun _ => inr) (k x))
  end.

Ltac destruct_steps :=
repeat (
cbn in *;
destruct_all;
subst;
match goal with
| [ H : InterSteps ?M ?s nil ?t |- _] => dependent destruction H
| [ H : InterSteps ?M ?s (?e :: ?p) ?t |- _] => dependent destruction H
| [ H : InterStep ?M ?s ?e ?t |- _] => unfold InterStep in H
| [ H : StateStep ?s ?e ?t |- _] => unfold StateStep in H
| [ H : ThreadsStep ?M ?s ?e ?t |- _] => unfold ThreadsStep in H
| [ H : PointStep ?S ?s ?e ?t |- _] => dependent destruction H
| [ H : OverThreadStep ?M ?s ?e ?t |- _] => dependent destruction H
| [ H : UnderThreadStep ?s ?e ?t |- _] => dependent destruction H
| [ s : InterState ?F ?spec |- _] => destruct s
end).

Lemma over_call_states {E F} {V : Spec E} {M : Impl E F} :
  forall i A (m : F A) s t,
  InterStep (spec:=V) M s (i, OEvent (CallEv m)) t ->
  fst t i <> Idle.
unfold InterStep, ThreadsStep. intros. destruct_all.
dependent destruction H. cbn in *. dependent destruction H.
rewrite <- x. easy.
Qed.

Lemma step_no_diff {E F} {V : Spec E} {M : Impl E F} :
  forall i e s t,
  InterStep (spec:=V) M s (i, e) t ->
  forall j, j <> i -> fst s j = fst t j.
unfold InterStep, ThreadsStep. intros. destruct_all.
dependent destruction H. cbn in *.
rewrite H0; easy.
Qed.

Definition tensorActive {E E' F F'} (s : ThreadsSt E E') (t : ThreadsSt F F') : ActiveMap (E |+| F) :=
  fun i => match s i with
  | UCall om um k => Some (existT _ _ (inl um))
  | _ =>
    match t i with
    | UCall om um k => Some (existT _ _ (inr um))
    | _ => None
    end
  end.

Definition liftLeftEvent {E E' F F'} (e : ThreadLEvent E E') : ThreadLEvent (E |+| F) (E' |+| F') :=
  (fst e, match snd e with
  | UEvent (Some (CallEv m)) => UEvent (Some (CallEv (inl m)))
  | UEvent (Some (RetEv m v)) => UEvent (Some (RetEv (inl m) v))
  | UEvent None => UEvent None
  | OEvent (CallEv m) => OEvent (CallEv (inl m))
  | OEvent (RetEv m v) => OEvent (RetEv (inl m) v)
  end).

Definition liftRightEvent {E E' F F'} (e : ThreadLEvent F F') : ThreadLEvent (E |+| F) (E' |+| F') :=
  (fst e, match snd e with
  | UEvent (Some (CallEv m)) => UEvent (Some (CallEv (inr m)))
  | UEvent (Some (RetEv m v)) => UEvent (Some (RetEv (inr m) v))
  | UEvent None => UEvent None
  | OEvent (CallEv m) => OEvent (CallEv (inr m))
  | OEvent (RetEv m v) => OEvent (RetEv (inr m) v)
  end).

Definition liftLeftState {E E' F F'} {V : Spec E} {W : Spec F} (s : InterState E' V) (ts : ThreadsSt F F') (t : State W) : InterState (E' |+| F') (tensorSpec V W) :=
  (fun i => liftTSLeft (fst s i), MkTS (specL:=V) (specR:=W) (@tensorActive E E' F F' (fst s) ts) (snd s) t).

Definition liftRightState {E E' F F'} {V : Spec E} {W : Spec F} (ss : ThreadsSt E E') (s : State V) (t : InterState F' W) : InterState (E' |+| F') (tensorSpec V W) :=
  (fun i => liftTSRight (fst t i), MkTS (specL:=V) (specR:=W) (@tensorActive E E' F F' ss (fst t)) s (snd t)).

Inductive tensor_system {E E' F F'} : ActiveMap (E |+| F) -> ActiveMap (E' |+| F') -> Trace (ThreadLEvent E E') -> Trace (ThreadLEvent F F') -> Trace (ThreadEvent (E' |+| F')) -> Prop :=
| TSNil ua oa :
    tensor_system ua oa nil nil nil
| TSLeftOverCall ua oa oa' p q i A (om : E' A) r :
    tensor_system ua oa' p q r ->
    ua i = None ->
    differ_pointwise oa oa' i ->
    oa i = None ->
    oa' i = Some (existT _ _ (inl om)) ->
    tensor_system ua oa ((i, OEvent (CallEv om)) :: p) q ((i, CallEv (inl om)) :: r)
| TSRightOverCall ua oa oa' p q i A (om : F' A) r :
    tensor_system ua oa' p q r ->
    ua i = None ->
    differ_pointwise oa oa' i ->
    oa i = None ->
    oa' i = Some (existT _ _ (inr om)) ->
    tensor_system ua oa p ((i, OEvent (CallEv om)) :: q) ((i, CallEv (inr om)) :: r)
| TSLeftOverRet ua oa oa' p q i A (om : E' A) v r :
    tensor_system ua oa' p q r ->
    ua i = None ->
    differ_pointwise oa oa' i ->
    oa i = Some (existT _ _ (inl om)) ->
    oa' i = None ->
    tensor_system ua oa ((i, OEvent (RetEv om v)) :: p) q ((i, RetEv (inl om) v) :: r)
| TSRightOverRet ua oa oa' p q i A (om : F' A) v r :
    tensor_system ua oa' p q r ->
    ua i = None ->
    differ_pointwise oa oa' i ->
    oa i = Some (existT _ _ (inr om)) ->
    oa' i = None ->
    tensor_system ua oa p ((i, OEvent (RetEv om v)) :: q) ((i, RetEv (inr om) v) :: r)
| TSLeftUnderCall ua ua' oa p q i A (om : E' A) B (um : E B) r :
    tensor_system ua' oa p q r ->
    oa i = Some (existT _ _ (inl om)) ->
    differ_pointwise ua ua' i ->
    ua i = None ->
    ua' i = Some (existT _ _ (inl um)) ->
    tensor_system ua oa ((i, UEvent (Some (CallEv um))) :: p) q r
| TSRightUnderCall ua ua' oa p q i A (om : F' A) B (um : F B) r :
    tensor_system ua' oa p q r ->
    oa i = Some (existT _ _ (inr om)) ->
    differ_pointwise ua ua' i ->
    ua i = None ->
    ua' i = Some (existT _ _ (inr um)) ->
    tensor_system ua oa p ((i, UEvent (Some (CallEv um))) :: q) r
| TSLeftUnderRet ua ua' oa p q i A (om : E' A) B (um : E B) v r :
    tensor_system ua' oa p q r ->
    oa i = Some (existT _ _ (inl om)) ->
    differ_pointwise ua ua' i ->
    ua i = Some (existT _ _ (inl um)) ->
    ua' i = None ->
    tensor_system ua oa ((i, UEvent (Some (RetEv um v))) :: p) q r
| TSRightUnderRet ua ua' oa p q i A (om : F' A) B (um : F B) v r :
    tensor_system ua' oa p q r ->
    oa i = Some (existT _ _ (inr om)) ->
    differ_pointwise ua ua' i ->
    ua i = Some (existT _ _ (inr um)) ->
    ua' i = None ->
    tensor_system ua oa p ((i, UEvent (Some (RetEv um v))) :: q) r
| TSLeftUnderSil ua oa p q i A (om : E' A) B (um : E B) r :
    tensor_system ua oa p q r ->
    oa i = Some (existT _ _ (inl om)) ->
    ua i = Some (existT _ _ (inl um)) ->
    tensor_system ua oa ((i, UEvent None) :: p) q r
| TSRightUnderSil ua oa p q i A (om : F' A) B (um : F B) r :
    tensor_system ua oa p q r ->
    oa i = Some (existT _ _ (inr om)) ->
    ua i = Some (existT _ _ (inr um)) ->
    tensor_system ua oa p ((i, UEvent None) :: q) r.

Inductive over_rel {E E' F F'} : option {A & (E' |+| F') A} -> ThreadState E E' -> ThreadState F F' -> Prop :=
| ORIdle :
    over_rel None Idle Idle
| ORLeftCont A (om : E' A) p :
    over_rel (Some (existT _ _ (inl om))) (Cont om p) Idle
| ORLeftUCall A (om : E' A) B (um : E B) k :
    over_rel (Some (existT _ _ (inl om))) (UCall om um k) Idle
| ORRightCont A (om : F' A) p :
    over_rel (Some (existT _ _ (inr om))) Idle (Cont om p)
| ORRightUCall A (om : F' A) B (um : F B) k :
    over_rel (Some (existT _ _ (inr om))) Idle (UCall om um k).

Inductive inter_system {E F} : ActiveMap E -> ActiveMap F -> Trace (ThreadLEvent E F) -> Prop :=
| ISNil ua oa :
    inter_system ua oa nil
| ISOverCall ua oa oa' p i A (om : F A) :
    inter_system ua oa' p ->
    differ_pointwise oa oa' i ->
    ua i = None ->
    oa i = None ->
    oa' i = Some (existT _ _ om) ->
    inter_system ua oa ((i, OEvent (CallEv om)) :: p)
| ISOverRet ua oa oa' p i A (om : F A) v :
    inter_system ua oa' p ->
    differ_pointwise oa oa' i ->
    ua i = None ->
    oa i = Some (existT _ _ om) ->
    oa' i = None ->
    inter_system ua oa ((i, OEvent (RetEv om v)) :: p)
| ISUnderCall ua ua' oa p i A (om : F A) B (um : E B) :
    inter_system ua' oa p ->
    differ_pointwise ua ua' i ->
    oa i = Some (existT _ _ om) ->
    ua i = None ->
    ua' i = Some (existT _ _ um) ->
    inter_system ua oa ((i, UEvent (Some (CallEv um))) :: p)
| ISUnderRet ua ua' oa p i A (om : F A) B (um : E B) v :
    inter_system ua' oa p ->
    differ_pointwise ua ua' i ->
    oa i = Some (existT _ _ om) ->
    ua i = Some (existT _ _ um) ->
    ua' i = None ->
    inter_system ua oa ((i, UEvent (Some (RetEv um v))) :: p)
| IsUnderSil ua oa p i :
    inter_system ua oa p ->
    inter_system ua oa ((i, UEvent None) :: p).

Lemma InterSteps_system {E F} {V : Spec E} {M : Impl E F} :
  forall s p t,
  InterSteps (spec:=V) M s p t ->
  inter_system.

(* Lemma funct_l_help {E F E' F'} {specE : Spec E} {specF : Spec F} {M : Impl E E'} {N : Impl F F'} {LState : InterState E' specE} {RState : InterState F' specF} {x0 : list (ThreadLEvent E E')} {x : list (ThreadLEvent F F')} {o : ThreadName -> option {A : Type & (E' |+| F') A}} {o0 : ThreadName -> option {A : Type & (E |+| F) A}} {a : Trace (ThreadEvent (E' |+| F'))} :
  tensor_system o0 o x0 x a ->
  forall (s : State specF) (s0 : State specE) (t0 : ThreadsSt E E'),
  InterSteps M (t0, s0) x0 LState ->
  forall t : ThreadsSt F F',
  InterSteps N (t, s) x RState ->
  (forall i : ThreadName, over_rel (o i) (t0 i) (t i)) ->
  exists st q,
    a = projOver q /\
  InterSteps (spec:= tensorSpec specE specF) (tensorImpl M N) (fun i => tensorTS (t0 i) (t i), {| TActive := o0; LState := s0; RState := s |}) q st.
intro H. induction H; cbn; intros; destruct_steps.
{
  repeat econstructor. easy.
}
{
  eapply IHtensor_system in H7.
  2: exact H6.
  2:{
    intros. specialize (H8 i0). dec_eq_nats i i0.
    {
      rewrite H3 in *. rewrite H2 in *.
      dependent destruction H8. rewrite <- x0. rewrite <- x.
      constructor.
    }
    {
      rewrite H1. rewrite <- H5. easy. easy. easy.
    }
  }
  destruct_all. subst.
  exists x0, ((i, OEvent (CallEv (inl om))) :: x1).
  cbn. split. easy.
  eapply StepsMore with (st'':=(fun j => tensorTS (t1 j) (t j),_)).
  split; cbn.
  econstructor; cbn.
  econstructor.
  specialize (H8 i). rewrite H4, H2 in H8.
  dependent destruction H8. rewrite H4, <- x.
  easy.
  cbn.
  rewrite <- x. easy.
  intros. rewrite H5; easy.
  easy.
  easy.
}
{
  eapply IHtensor_system in H7.
  2: exact H4.
  2:{
    intros. specialize (H8 i0). dec_eq_nats i i0.
    {
      rewrite H3 in *. rewrite H2 in *.
      dependent destruction H8. rewrite <- x2. rewrite <- x0.
      constructor.
    }
    {
      rewrite H1. rewrite <- H6. easy. easy. easy.
    }
  }
  destruct_all. subst.
  exists x0, ((i, OEvent (CallEv (inr om))) :: x1).
  cbn. split. easy.
  eapply StepsMore with (st'':=(fun j => tensorTS (t0 j) (t1 j),_)).
  split; cbn.
  econstructor; cbn.
  econstructor.
  specialize (H8 i). rewrite H2, H5 in H8.
  dependent destruction H8. rewrite H5, <- x.
  easy.
  cbn.
  rewrite <- x. specialize (H8 i).
  rewrite H5, H2 in H8. dependent destruction H8.
  rewrite <- x. easy.
  intros. rewrite H6; easy.
  easy.
  easy.
}
{
  eapply IHtensor_system in H6.
  2: exact H7.
  2:{
    intros. specialize (H8 i0). dec_eq_nats i i0.
    rewrite H3 in *. rewrite H2 in *.
    rewrite H4 in *. rewrite <- x in *.
    dependent destruction H8. rewrite <- x. constructor.
    rewrite H1. rewrite <- H5. easy. easy. easy.
  }
  destruct_all. subst.
  exists x0, ((i, OEvent (RetEv (inl om) v)) :: x1).
  split. cbn. easy.
  eapply StepsMore with (st'':=(fun j => tensorTS (t1 j) (t j), _)).
  split; cbn.
  econstructor; cbn.
  econstructor.
  rewrite H4. cbn.
  rewrite frobProgId at 1. easy.
  rewrite <- x. specialize (H8 i).
  rewrite H2, H4 in H8. dependent destruction H8.
  rewrite <- x. easy.
  intros. rewrite H5; easy.
  easy.
  easy.
}
{
  eapply IHtensor_system in H7.
  2: exact H4.
  2:{
    intros. specialize (H8 i0). dec_eq_nats i i0.
    rewrite H3 in *. rewrite H2 in *. rewrite H5 in *.
    rewrite <- x. dependent destruction H8. rewrite <- x.
    constructor.
    rewrite H1. rewrite <- H6. easy. easy. easy.
  }
  destruct_all. subst.
  exists x0, ((i, OEvent (RetEv (inr om) v)) :: x1).
  split. cbn. easy.
  eapply StepsMore with (st'':=(fun j => tensorTS (t0 j) (t1 j), _)).
  split; cbn.
  econstructor; cbn.
  econstructor.
  specialize (H8 i). rewrite H2 in *. rewrite H5 in *.
  dependent destruction H8. rewrite <- x. cbn.
  rewrite frobProgId at 1. easy.
  specialize (H8 i). rewrite H5 in *. rewrite H2 in *.
  dependent destruction H8. rewrite <- x0. rewrite <- x.
  easy.
  intros. rewrite H6; easy.
  easy.
  easy.
}
{
  eapply IHtensor_system in H6.
  2: exact H7.
  2:{
    intros. specialize (H9 i0). dec_eq_nats i i0.
    rewrite H4 in *. rewrite <- x. dependent destruction H9.
    rewrite <- x. rewrite <- x1. constructor.
    rewrite <- H5; easy.
  }
  destruct_all. subst.
  exists x0, ((i, UEvent (Some (CallEv (inl um)))) :: x1).
  cbn. split. easy.
  eapply StepsMore with (st'':=(fun j => tensorTS (t1 j) (t j), MkTS ua' _ _)).
  split; cbn.
  econstructor; cbn.
  econstructor.
  rewrite H4. cbn. rewrite frobProgId at 1. easy.
  specialize (H9 i). rewrite H0 in *. rewrite H4 in *.
  rewrite <- x. dependent destruction H9. rewrite <- x.
  easy.
  intros. rewrite H5; easy.
  split. exact H8.
  split. easy.
  split. easy.
  split. easy.
  easy.
  easy.
}
{
  eapply IHtensor_system in H7.
  2: exact H4.
  2:{
    intros. specialize (H9 i0). dec_eq_nats i i0.
    rewrite H0 in *. rewrite <- x. rewrite H5 in *.
    dependent destruction H9. rewrite <- x.
    constructor. rewrite <- H6; easy.
  }
  destruct_all. subst.
  exists x0, ((i, UEvent (Some (CallEv (inr um)))) :: x1).
  cbn. split. easy.
  eapply StepsMore with (st'':=(fun j => tensorTS (t0 j) (t1 j), MkTS ua' _ _)).
  split; cbn.
  econstructor; cbn.
  econstructor.
  rewrite H5. cbn. specialize (H9 i). rewrite H0 in *. rewrite H5 in *.
  dependent destruction H9. rewrite <- x. cbn. rewrite frobProgId at 1.
  cbn. easy.
  specialize (H9 i). rewrite H0 in *. rewrite <- x in *.
  rewrite H5 in *. dependent destruction H9. rewrite <- x.
  constructor.
  intros. rewrite H6; easy.
  split. exact H8.
  split. easy.
  split. easy.
  split. easy.
  easy.
  easy.
}
{
  eapply IHtensor_system in H6.
  2: exact H7.
  2:{
    intros. specialize (H9 i0). dec_eq_nats i i0.
    rewrite H0 in *. rewrite H4 in *. rewrite <- x.
    dependent destruction H9. rewrite <- x. constructor.
    rewrite <- H5; easy.
  }
  destruct_all. subst.
  exists x0, ((i, UEvent (Some (RetEv (inl um) v))) :: x1).
  cbn. split. easy.
  eapply StepsMore with (st'':=(fun j => tensorTS (t1 j) (t j), MkTS ua' _ _)).
  split; cbn.
  econstructor; cbn.
  econstructor. rewrite H4. cbn. easy.
  rewrite <- x. easy.
  intros. rewrite H5; easy.
  split. exact H8.
  split. easy.
  split. easy.
  split. easy.
  easy.
  easy.
}
{
  eapply IHtensor_system in H7.
  2: exact H4.
  2:{
    intros. specialize (H9 i0). dec_eq_nats i i0.
    rewrite H0 in *. rewrite H5 in *. rewrite <- x.
    dependent destruction H9. rewrite <- x. constructor.
    rewrite <- H6; easy.
  }
  destruct_all. subst.
  exists x0, ((i, UEvent (Some (RetEv (inr um) v))) :: x1).
  cbn. split. easy.
  eapply StepsMore with (st'':=(fun j => tensorTS (t0 j) (t1 j), MkTS ua' _ _)).
  split; cbn.
  econstructor; cbn.
  specialize (H9 i). rewrite H0 in *. rewrite H5 in *.
  dependent destruction H9. rewrite <- x.
  econstructor. easy.
  rewrite <- x0. easy.
  intros. rewrite H6; easy.
  split. exact H8.
  easy.
  easy.
}
{
  eapply IHtensor_system in H4.
  2: exact H5.
  2:{
    intros. specialize (H6 i0). dec_eq_nats i i0.
    rewrite H0 in *. rewrite H2 in *. rewrite <- x.
    dependent destruction H6. rewrite <- x. constructor.
    rewrite <- H3; easy.
  }
  destruct_all. subst.
  exists x0, ((i, UEvent None) :: x1).
  split. easy.
  eapply StepsMore with (st'':=(fun j => tensorTS (t1 j) (t j), MkTS ua _ _)).
  split; cbn.
  econstructor.
  specialize (H6 i). rewrite H2 in *. cbn. rewrite <- x in *. rewrite H0 in *.
  dependent destruction H6. rewrite <- x.
  eapply USilentThreadStep.
  cbn. rewrite frobProgId at 1. rewrite H2. simpl (tensorTS _ _).
  rewrite frobProgId at 1. cbn. easy.
  easy.
  intros. rewrite H3; easy.
  easy.
  easy.
}
{
  eapply IHtensor_system in H5.
  2: exact H2.
  2:{
    intros. specialize (H6 i0). dec_eq_nats i i0.
    rewrite H0 in *. rewrite H3 in *. rewrite <- x in *.
    dependent destruction H6. rewrite <- x. constructor.
    rewrite <- H4; easy.
  }
  destruct_all. subst.
  exists x0, ((i, UEvent None) :: x1).
  split. easy.
  eapply StepsMore with (st'':=(fun j => tensorTS (t0 j) (t1 j), MkTS ua _ _)).
  split; cbn.
  econstructor; cbn.
  specialize (H6 i).
  rewrite H3 in *. rewrite <- x in *. rewrite H0 in *.
  dependent destruction H6. rewrite <- x.
  cbn. econstructor.
  rewrite frobProgId at 1. easy.
  easy.
  intros. rewrite <- H4; easy.
  easy.
  easy.
}
Qed.

Theorem tensor_layer_funct_l {E F E' F'}:   
  forall (specE : Spec E) (specF : Spec F) (M : Impl E E') (N : Impl F F'),
  specRefines
    (tensorSpec (overObj (specE :> M)) (overObj (specF :> N)))
    (overObj (tensorLayer (specE :> M) (specF :> N))).
unfold specRefines, Incl, IsTraceOfSpec. intros.
destruct_all. destruct x.
assert (SeqConsistent (fun _ => None) a).
eapply ((tensorSpec (overObj (specE:>M)) (overObj (specF:>N)))).
exact H.
eapply split_tensor_steps with
  (specE:= overObj (specE :> M))
  (specF:= overObj (specF :> N))
  in H.
repeat rewrite projInterSteps in *.
destruct_all. cbn in *.
cut (
  exists st q,
    a = projOver q /\
    InterSteps (spec:= tensorSpec specE specF) (tensorImpl M N) (allIdle, MkTS (fun _ => None) (Init specE) (Init specF))
  q
  st
).
{
  intros. destruct_all. subst.
  exists x1, x2. repeat split.
  easy.
  dependent destruction H7.
  left. easy.
  unfold InterStep, ThreadsStep in H6. destruct_all.
  dependent destruction H6. unfold ThreadStep in H6. cbn in H6.
  destruct ev, l; cbn in *.
  dependent destruction H6.
  right. repeat econstructor. 
}
assert (
  @tensor_system E E' F F' (fun _ => None) (fun _ => None) x0 x a
).

assert (
  forall i,
    @over_rel E E' F F' ((fun _ => None) i) (allIdle i) (allIdle i)
).
constructor.
generalize dependent (fun _ : ThreadName => @None {A & (E |+| F) A}).
generalize dependent (fun _ : ThreadName => @None {A & (E' |+| F') A}).
change (@allIdle (E |+| F) (E' |+| F'))
with (fun i => tensorTS (@allIdle E E' i) (@allIdle F F' i)).
generalize dependent (@allIdle E E').
generalize dependent (@allIdle F F').
intros.
generalize dependent t. generalize dependent t0.
generalize dependent (Init specE). generalize dependent (Init specF).
generalize dependent a.
clear TActive.
intros.
eapply funct_l_help.
exact H6. exact H4. exact H2. easy.

Theorem tensor_layer_funct_r {E F E' F'}:   
  forall (specE : Spec E) (specF : Spec F) (M : Impl E E') (N : Impl F F'),
  specRefines
    (overObj (tensorLayer (specE :> M) (specF :> N)))
    (tensorSpec (overObj (specE :> M)) (overObj (specF :> N))).
unfold specRefines, Incl, IsTraceOfSpec. intros. destruct_all.
simpl (Init _) in *. *)