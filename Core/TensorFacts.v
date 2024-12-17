From LHL.Core Require Import
  Program
  ProgramFacts
  Specs
  Traces
  Tensor
  TracesFacts.

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

Fixpoint projLeft {T E F} (p : Trace (ThreadEvent T (E |+| F))) : Trace (ThreadEvent T E) :=
  match p with
  | nil => nil
  | cons (i, CallEv (inl e)) p => cons (i, CallEv e) (projLeft p)
  | cons (i, RetEv (inl e) v) p => cons (i, RetEv e v) (projLeft p)
  | cons _ p => projLeft p
  end.

Fixpoint liftLeft {T E F} (p : Trace (ThreadEvent T E)) : Trace (ThreadEvent T (E |+| F)) :=
  match p with
  | nil => nil
  | cons (i, CallEv e) p => cons (i, CallEv (inl e)) (liftLeft p)
  | cons (i, RetEv e v) p => cons (i, RetEv (inl e) v) (liftLeft p)
  end.

Fixpoint projRight {T E F} (p : Trace (ThreadEvent T (E |+| F))) : Trace (ThreadEvent T F) :=
  match p with
  | nil => nil
  | cons (i, CallEv (inr e)) p => cons (i, CallEv e) (projRight p)
  | cons (i, RetEv (inr e) v) p => cons (i, RetEv e v) (projRight p)
  | cons _ p => projRight p
  end.
  
Fixpoint liftRight {T E F} (p : Trace (ThreadEvent T F)) : Trace (ThreadEvent T (E |+| F)) :=
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

Theorem tensor_monotonic {T E F} :
  forall (specE specE' : Spec T E) (specF specF' : Spec T F) ,
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
  generalize dependent (fun _ : Name T => @None {A & (E |+| F) A}).
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
  generalize dependent (fun _ : Name T => @None {A & (E |+| F) A}).
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
generalize dependent (fun _ : Name T => @None {A & (E |+| F) A}).
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

Definition tensorLeftActiveMap {T E F} (a : TensorActive T E F) : Name T -> option {A & E A} :=
  fun i => match a i with
  | Some (existT _ _ (inl m)) => Some (existT _ _ m)
  | _ => None
  end.

Definition tensorNoRight {T E F} (a : TensorActive T E F) :=
  forall i,
    ~(exists A (m : F A), a i = Some (existT _ _ (inr m))).

Lemma tensor_liftLeft_trivial {T E F} :
  forall (specE : Spec T E) (specF : Spec T F),
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

Definition tensorRightActiveMap {T E F} (a : TensorActive T E F) : Name T -> option {A & F A} :=
  fun i => match a i with
  | Some (existT _ _ (inr m)) => Some (existT _ _ m)
  | _ => None
  end.

Definition tensorNoLeft {T E F} (a : TensorActive T E F) :=
  forall i,
    ~(exists A (m : E A), a i = Some (existT _ _ (inl m))).

Lemma tensor_liftRight_trivial {T E F} :
  forall (specE : Spec T E) (specF : Spec T F),
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

Lemma tensor_liftLeft_const {T E F} :
  forall (specE : Spec T E) (specF : Spec T F),
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

Lemma tensor_liftRight_const {T E F} :
  forall (specE : Spec T E) (specF : Spec T F),
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
Theorem tensor_monotonic_inv {T E F} : 
  forall (specE specE' : Spec T E) (specF specF' : Spec T F), 
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

Lemma split_tensor_steps {T E F} :
  forall (specE : Spec T E) (specF : Spec T F),
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

Lemma over_call_states {T E F} {V : Spec T E} {M : Impl E F} :
  forall i A (m : F A) s t,
  InterStep (spec:=V) M s (i, OEvent (CallEv m)) t ->
  fst t i <> Idle.
unfold InterStep, ThreadsStep. intros. destruct_all.
dependent destruction H. cbn in *. dependent destruction H.
rewrite <- x. easy.
Qed.

Lemma step_no_diff {T E F} {V : Spec T E} {M : Impl E F} :
  forall i e s t,
  InterStep (spec:=V) M s (i, e) t ->
  forall j, j <> i -> fst s j = fst t j.
unfold InterStep, ThreadsStep. intros. destruct_all.
dependent destruction H. cbn in *.
rewrite H0; easy.
Qed.

Definition tensorActiveUnder {T E F} (s : ThreadsSt T E F) : ActiveMap T E :=
  fun i => match s i with
  | UCall om um k => Some (existT _ _ um)
  | _ => None
  end.

Definition tensorActiveOver {T E F} (s : ThreadsSt T E F) : ActiveMap T F :=
  fun i => match s i with
  | Cont m _ => Some (existT _ _ m)
  | UCall m _ k => Some (existT _ _ m)
  | Idle => None
  end.

Inductive tensor_system {T E E' F F'} : ActiveMap T (E |+| F) -> ActiveMap T (E' |+| F') -> Trace (ThreadLEvent T E E') -> Trace (ThreadLEvent T F F') -> Trace (ThreadEvent T (E' |+| F')) -> Prop :=
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
| TSLeftUnderSil ua oa p q i A (om : E' A) r :
    tensor_system ua oa p q r ->
    oa i = Some (existT _ _ (inl om)) ->
    tensor_system ua oa ((i, UEvent None) :: p) q r
| TSRightUnderSil ua oa p q i A (om : F' A) r :
    tensor_system ua oa p q r ->
    oa i = Some (existT _ _ (inr om)) ->
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

Inductive inter_system {T E F} : ActiveMap T E -> ActiveMap T F -> Trace (ThreadLEvent T E F) -> Prop :=
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
| IsUnderSil ua oa p i A (om : F A) :
    inter_system ua oa p ->
    oa i = Some (existT _ _ om) ->
    inter_system ua oa ((i, UEvent None) :: p).

Lemma InterSteps_system {T E F} {V : Spec T E} {M : Impl E F} :
  forall t p s,
  InterSteps (spec:=V) M s p t ->
  inter_system (tensorActiveUnder (fst s)) (tensorActiveOver (fst s)) p.
intros t p s. destruct s.
generalize dependent t0. generalize dependent s.
induction p; cbn; intros; destruct_steps.
{
  econstructor.
}
{
  destruct a. unfold ThreadStep in *. destruct l; cbn in *;
  dependent destruction H.
  {
    apply IHp in H2. destruct_all. subst.
    assert (tensorActiveOver t0 = tensorActiveOver t).
    {
      unfold tensorActiveOver. extensionality i.
      dec_eq_nats i n.
      rewrite H. rewrite <- x. easy.
      rewrite H0; easy.
    }
    rewrite H3. clear H3.
    econstructor.
    { exact H2. }
    {
      unfold tensorActiveUnder, differ_pointwise. intros.
      rewrite H0; easy.
    }
    { unfold tensorActiveOver. rewrite <- x. easy. }
    { unfold tensorActiveUnder. rewrite H. easy. }
    { unfold tensorActiveUnder. rewrite <- x. easy. }
  }
  {
    apply IHp in H2. destruct_all. subst.
    assert (tensorActiveOver t0 = tensorActiveOver t).
    {
      unfold tensorActiveOver. extensionality i.
      dec_eq_nats i n.
      rewrite H. rewrite <- x. easy.
      rewrite H0; easy.
    }
    rewrite H3. clear H3.
    econstructor.
    { exact H2. }
    {
      unfold tensorActiveUnder, differ_pointwise. intros.
      rewrite H0; easy.
    }
    { unfold tensorActiveOver. rewrite <- x. easy. }
    { unfold tensorActiveUnder. rewrite H. easy. }
    { unfold tensorActiveUnder. rewrite <- x. easy. }
  }
  {
    apply IHp in H2. destruct_all. subst.
    assert (tensorActiveOver t0 = tensorActiveOver t).
    {
      unfold tensorActiveOver. extensionality i.
      dec_eq_nats i n.
      rewrite H. rewrite <- x. easy.
      rewrite H0; easy.
    }
    assert (tensorActiveUnder t0 = tensorActiveUnder t).
    {
      unfold tensorActiveUnder. extensionality i.
      dec_eq_nats i n. rewrite H. rewrite <- x. easy.
      rewrite H0; easy.
    }
    rewrite H3. clear H3. rewrite H1. clear H1.
    econstructor.
    easy.
    unfold tensorActiveOver. rewrite <- x. easy.
  }
  {
    apply IHp in H2. destruct_all. subst.
    assert (tensorActiveUnder t0 = tensorActiveUnder t).
    {
      unfold tensorActiveUnder. extensionality i.
      dec_eq_nats i n.
      rewrite H. rewrite <- x. easy.
      rewrite H0; easy.
    }
    rewrite H1. clear H1.
    econstructor.
    { exact H2. }
    {
      unfold tensorActiveOver, differ_pointwise. intros.
      rewrite H0; easy.
    }
    { unfold tensorActiveUnder. rewrite <- x. easy. }
    { unfold tensorActiveOver. rewrite H. easy. }
    { unfold tensorActiveOver. rewrite <- x. easy. }
  }
  {
    apply IHp in H2. destruct_all. subst.
    assert (tensorActiveUnder t0 = tensorActiveUnder t).
    {
      unfold tensorActiveUnder. extensionality i.
      dec_eq_nats i n.
      rewrite H. rewrite <- x. easy.
      rewrite H0; easy.
    }
    rewrite H1. clear H1.
    econstructor.
    { exact H2. }
    {
      unfold tensorActiveOver, differ_pointwise. intros.
      rewrite H0; easy.
    }
    { unfold tensorActiveUnder. rewrite <- x. easy. }
    { unfold tensorActiveOver. rewrite H. easy. }
    { unfold tensorActiveOver. rewrite <- x. easy. }
  }
}
Qed.

Lemma funct_l_help {T E F E' F'} {specE : Spec T E} {specF : Spec T F} {M : Impl E E'} {N : Impl F F'} {LState : InterState E' specE} {RState : InterState F' specF} {x0 : list (ThreadLEvent T E E')} {x : list (ThreadLEvent T F F')} {o : Name T -> option {A : Type & (E' |+| F') A}} {o0 : Name T -> option {A : Type & (E |+| F) A}} {a : Trace (ThreadEvent T (E' |+| F'))} :
  tensor_system o0 o x0 x a ->
  forall (s : State specF) (s0 : State specE) (t0 : ThreadsSt T E E'),
  InterSteps M (t0, s0) x0 LState ->
  forall t : ThreadsSt T F F',
  InterSteps N (t, s) x RState ->
  (forall i, over_rel (o i) (t0 i) (t i)) ->
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
  2: exact H3.
  2:{
    intros. specialize (H5 i0). dec_eq_nats i i0.
    rewrite <- x in *. rewrite H1 in *. rewrite H0 in *.
    dependent destruction H5. rewrite <- x. econstructor.
    rewrite <- H2; easy.
  }
  destruct_all. subst.
  exists x0, ((i, UEvent None) :: x1).
  split. easy.
  eapply StepsMore with (st'':=(fun j => tensorTS (t1 j) (t j), MkTS ua _ _)).
  split; cbn.
  econstructor.
  2:{ intros. rewrite H2; easy. }
  2: easy.
  2: easy.
  cbn. eapply USilentThreadStep with (p:= mapProg (fun _ => inl) p0).
  rewrite H1. cbn. rewrite frobProgId at 1. easy.
  rewrite <- x. cbn. easy.
}
{
  eapply IHtensor_system in H4.
  2: exact H1.
  2:{
    intros. specialize (H5 i0). dec_eq_nats i i0.
    rewrite <- x in *. rewrite H2 in *. rewrite H0 in *.
    dependent destruction H5. rewrite <- x. econstructor.
    rewrite <- H3; easy.
  }
  destruct_all. subst.
  exists x0, ((i, UEvent None) :: x1).
  split. easy.
  eapply StepsMore with (st'':=(fun j => tensorTS (t0 j) (t1 j), MkTS ua _ _)).
  split; cbn.
  econstructor.
  2:{ intros. rewrite <- H3; easy. }
  2: easy.
  2: easy.
  specialize (H5 i). rewrite H0 in *. rewrite H2 in *.
  dependent destruction H5. cbn in *.
  rewrite <- x. rewrite H2. rewrite <- x0.
  cbn. eapply USilentThreadStep with (p:= mapProg (fun _ => inr) p0).
  rewrite frobProgId at 1. easy.
  easy.
}
Qed.

Definition Status (E : ESig) := option {A & E A}.

Inductive active_square {E E' F F'} : Status (E |+| F) -> Status E -> Status F -> Status E' -> Status F' -> Status (E' |+| F') -> Prop :=
| ASAllIdle : active_square None None None None None None
| ASLeftOver A (om : E' A) :
    active_square None None None (Some (existT _ _ om)) None (Some (existT _ _ (inl om)))
| ASRightOver A (om : F' A) :
    active_square None None None None (Some (existT _ _ om)) (Some (existT _ _ (inr om)))
| ASLeftUnder A (om : E' A) B (um : E B) :
    active_square (Some (existT _ _ (inl um))) (Some (existT _ _ um)) None (Some (existT _ _ om)) None (Some (existT _ _ (inl om)))
| ASRightUnder A (om : F' A) B (um : F B) :
    active_square (Some (existT _ _ (inr um))) None (Some (existT _ _ um)) None (Some (existT _ _ om)) (Some (existT _ _ (inr om))).

Definition all_active_square {T E E' F F'} : ActiveMap T (E |+| F) -> ActiveMap T E -> ActiveMap T F -> ActiveMap T E' -> ActiveMap T F' -> ActiveMap T (E' |+| F') -> Prop :=
  fun a b c d e f =>
    forall i, active_square (a i) (b i) (c i) (d i) (e i) (f i). 

Lemma proj_dirs_nil {T E F} :
  forall p : Trace (ThreadEvent T (E |+| F)),
  projLeft p = nil ->
  projRight p = nil ->
  p = nil.
intros. destruct p. easy.
destruct t, e, m; cbn in *; discriminate.
Qed.

Require Import Lia.

Ltac rw_all :=
repeat match goal with
| [ H : ?f ?x = ?y |- _] => (repeat rewrite H in * || clear H)
| [ H : ?x = ?f ?y |- _] => (repeat rewrite <- H in * || clear H)
end.

Inductive tensor_trace_square {T E E' F F'} : Trace (ThreadLEvent T E E') -> Trace (ThreadLEvent T F F') -> Trace (ThreadEvent T (E' |+| F')) -> Prop :=
| TTSNil :
    tensor_trace_square nil nil nil
| TTSLeftOverCall p q r i A (m : E' A) :
    tensor_trace_square p q r ->
    tensor_trace_square ((i, OEvent (CallEv m)) :: p) q ((i, CallEv (inl m)) :: r)
| TTSLeftOverRet p q r i A (m : E' A) v :
    tensor_trace_square p q r ->
    tensor_trace_square ((i, OEvent (RetEv m v)) :: p) q ((i, RetEv (inl m) v) :: r)
| TTSLeftUnderCall p q r i A (m : E A) :
    tensor_trace_square p q r ->
    tensor_trace_square ((i, UEvent (Some (CallEv m))) :: p) q r
| TTSLeftUnderRet p q r i A (m : E A) v :
    tensor_trace_square p q r ->
    tensor_trace_square ((i, UEvent (Some (RetEv m v))) :: p) q r
| TTSRightOverCall p q r i A (m : F' A) :
    tensor_trace_square p q r ->
    tensor_trace_square p ((i, OEvent (CallEv m)) :: q) ((i, CallEv (inr m)) :: r)
| TTSRightOverRet p q r i A (m : F' A) v :
    tensor_trace_square p q r ->
    tensor_trace_square p ((i, OEvent (RetEv m v)) :: q) ((i, RetEv (inr m) v) :: r)
| TTSRightUnderCall p q r i A (m : F A) :
    tensor_trace_square p q r ->
    tensor_trace_square p ((i, UEvent (Some (CallEv m))) :: q) r
| TTSRightUnderRet p q r i A (m : F A) v :
    tensor_trace_square p q r ->
    tensor_trace_square p ((i, UEvent (Some (RetEv m v))) :: q) r
| TTSLeftUnderSilent p q r i :
    tensor_trace_square p q r ->
    tensor_trace_square ((i, UEvent None) :: p) q r
| TTSRightUnderSilent p q r i :
    tensor_trace_square p q r ->
    tensor_trace_square p ((i, UEvent None) :: q) r.

Program Fixpoint get_tensor_trace_square {T E E' F F'} {x0 : Trace (ThreadLEvent T E E')} {x : Trace (ThreadLEvent T F F')} {measure (length x0 + length x)} :
  forall a : Trace (ThreadEvent T (E' |+| F')),
  projLeft a = projOver x0 ->
  projRight a = projOver x ->
  tensor_trace_square x0 x a := _.
Next Obligation.
rename get_tensor_trace_square into IH.
destruct x, x0; cbn in *.
{
  rewrite proj_dirs_nil.
  constructor. easy. easy.
}
{
  destruct t, l, ev; cbn in *.
  destruct e.
  econstructor. apply IH. simpl. lia. easy. easy.
  econstructor. apply IH. simpl. lia. easy. easy.
  econstructor. apply IH. simpl. lia. easy. easy.
  destruct a. cbn in *. discriminate.
  destruct t, e, m0; cbn in *; try discriminate.
  dependent destruction H.
  econstructor. apply IH. simpl. lia. easy. easy.
  destruct a. cbn in *. discriminate.
  destruct t, e, m0; cbn in *; try discriminate.
  dependent destruction H.
  econstructor. apply IH. simpl. lia. easy. easy.
}
{
  destruct t, l, ev; cbn in *.
  destruct e.
  econstructor. apply IH. simpl. lia. easy. easy.
  econstructor. apply IH. simpl. lia. easy. easy.
  econstructor. apply IH. simpl. lia. easy. easy.
  destruct a. cbn in *. discriminate.
  destruct t, e, m0; cbn in *; try discriminate.
  dependent destruction H0.
  econstructor. apply IH. simpl. lia. easy. easy.
  destruct a. cbn in *. discriminate.
  destruct t, e, m0; cbn in *; try discriminate.
  dependent destruction H0.
  econstructor. apply IH. simpl. lia. easy. easy.
}
{
  destruct t0, t, l, l0; cbn in *.
  destruct ev, ev0.
  destruct e, e0.
  econstructor. apply IH. simpl. lia. easy. easy.
  econstructor. apply IH. simpl. lia. easy. easy.
  econstructor. apply IH. simpl. lia. easy. easy.
  econstructor. apply IH. simpl. lia. easy. easy.
  econstructor. apply IH. simpl. lia. easy. easy.
  econstructor. apply IH. simpl. lia. easy. easy.
  econstructor. apply IH. simpl. lia. easy. easy.
  destruct a. cbn in *. discriminate.
  destruct t, e, m; cbn in *; try discriminate.
  destruct ev. destruct e0.
  econstructor. apply IH. simpl. lia. easy. easy.
  econstructor. apply IH. simpl. lia. easy. easy.
  econstructor. apply IH. simpl. lia. easy. easy.
  dependent destruction H0.
  econstructor. apply IH. simpl. lia. easy. easy.
  destruct ev. destruct e0.
  econstructor. apply IH. simpl. lia. easy. easy.
  econstructor. apply IH. simpl. lia. easy. easy.
  econstructor. apply IH. simpl. lia. easy. easy.
  dependent destruction H0.
  econstructor. apply IH. simpl. lia. easy. easy.
  destruct a. cbn in *. discriminate.
  destruct t, e, m; cbn in *; try discriminate.
  dependent destruction H.
  econstructor. apply IH. simpl. lia. easy. easy.
  destruct ev0. destruct e.
  econstructor. apply IH. simpl. lia. easy. easy.
  econstructor. apply IH. simpl. lia. easy. easy.
  econstructor. apply IH. simpl. lia. easy. easy.
  dependent destruction H.
  econstructor. apply IH. simpl. lia. easy. easy.
  destruct ev0. destruct e.
  econstructor. apply IH. simpl. lia. easy. easy.
  econstructor. apply IH. simpl. lia. easy. easy.
  econstructor. apply IH. simpl. lia. easy. easy.
  destruct a. cbn in *. discriminate.
  destruct t, e, m; cbn in *; try discriminate.
  dependent destruction H.
  econstructor. apply IH. simpl. lia. easy. easy.
  dependent destruction H0.
  econstructor. apply IH. simpl. lia. easy. easy.
  dependent destruction H.
  econstructor. apply IH. simpl. lia. easy. easy.
  dependent destruction H0.
  econstructor. apply IH. simpl. lia. easy. easy.
}
Qed.

Theorem tensor_layer_funct_l {T E F E' F'}:   
  forall (specE : Spec T E) (specF : Spec T F) (M : Impl E E') (N : Impl F F'),
    ((specE ▷ M) ⊗ (specF ▷ N)) ⊑ ((specE ⊗ specF) ▷ (M :⊗: N)).
Proof.
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
    @tensor_system T E E' F F' (fun _ => None) (fun _ => None) x0 x a
  ).
  {
    apply InterSteps_system in H4, H2.
    unfold tensorActiveUnder, tensorActiveOver in *.
    cbn in *.
    clear H3 H5.
    assert (
      @all_active_square T E E' F F' (fun _ : Name T => None) (fun _ => None) (fun _ => None) (fun _ => None) (fun _ => None) (fun _ => None)
    ).
    constructor.
    generalize dependent (fun _ : Name T => @None {A & (E |+| F) A}).
    generalize dependent (fun _ : Name T => @None {A & E A}).
    generalize dependent (fun _ : Name T => @None {A & F A}).
    generalize dependent (fun _ : Name T => @None {A & E' A}).
    generalize dependent (fun _ : Name T => @None {A & F' A}).
    generalize dependent (fun _ : Name T => @None {A & (E' |+| F') A}).
    intros.
    assert (tensor_trace_square x0 x a).
    apply get_tensor_trace_square; easy.
    move H4 after H5. move H2 after H4.
    move H5 at bottom. move H0 before H4.
    generalize dependent o4. generalize dependent o3.
    generalize dependent o2. generalize dependent o1.
    generalize dependent o0. generalize dependent o.
    clear H H1 TActive LState RState.

    induction H5; try (rename IHtensor_trace_square into IH); cbn; intros.
    { constructor. }
    {
      dependent destruction H0. dependent destruction H4.
      econstructor.
      {
        eapply IH. exact H2. exact H3. exact H4.
        unfold all_active_square. intros. specialize (H10 i0).
        dec_eq_nats i i0.
        {
          rw_all. dependent destruction H10.
          rewrite <- x0. rewrite <- x2. rewrite <- x4.
          econstructor.
        }
        {
          rewrite H1. rewrite H6. easy. easy. easy.
        }
      }
      {
        specialize (H10 i). rw_all. dependent destruction H10. easy.
      }
      { easy. }
      { easy. }
      { easy. }
    }
    {
      dependent destruction H0. dependent destruction H4.
      econstructor.
      {
        eapply IH. exact H2. exact H3. exact H4.
        unfold all_active_square. intros. specialize (H10 i0).
        dec_eq_nats i i0.
        {
          rw_all. dependent destruction H10.
          rewrite <- x0. rewrite <- x2. rewrite <- x3.
          econstructor.
        }
        {
          rewrite H1. rewrite H6. easy. easy. easy.
        }
      }
      {
        specialize (H10 i). rw_all. dependent destruction H10. easy.
      }
      { easy. }
      { easy. }
      { easy. }
    }
    {
      dependent destruction H4.
      eapply TSLeftUnderCall with (ua':=fun j => if i =? j then Some (existT _ _ (inl m)) else o4 j).
      2:{
        specialize (H7 i). rw_all. dependent destruction H7.
        symmetry. exact x.
      }
      2:{
        specialize (H7 i). rw_all. dependent destruction H7.
        unfold differ_pointwise. intros. rewrite eqb_nid; easy.
      }
      {
        eapply IH. easy. exact H2. exact H4.
        unfold all_active_square. intros. specialize (H7 i0).
        dec_eq_nats i i0.
        {
          rewrite H6 in *. rewrite H3 in *. rewrite H1 in *.
          dependent destruction H7.
          rewrite <- x0. rewrite <- x2. rewrite <- x3. rewrite <- x.
          rewrite eqb_id. constructor.
        }
        {
          rewrite eqb_nid. rewrite H. easy. easy. easy.
        }
      }
      {
        specialize (H7 i). rw_all. dependent destruction H7. easy.
      }
      {
        rewrite eqb_id. easy.
      }
    }
    {
      dependent destruction H4.
      eapply TSLeftUnderRet with (ua':=fun j => if i =? j then None else o4 j).
      2:{
        specialize (H7 i). rw_all. dependent destruction H7.
        symmetry. exact x.
      }
      2:{
        specialize (H7 i). rw_all. dependent destruction H7.
        unfold differ_pointwise. intros. rewrite eqb_nid; easy.
      }
      {
        eapply IH. easy. exact H2. exact H4.
        unfold all_active_square. intros. specialize (H7 i0).
        dec_eq_nats i i0.
        {
          rewrite H6 in *. rewrite H3 in *. rewrite H1 in *.
          dependent destruction H7.
          rewrite <- x0. rewrite <- x2. rewrite <- x1. rewrite <- x.
          rewrite eqb_id. constructor.
        }
        {
          rewrite eqb_nid. rewrite H. easy. easy. easy.
        }
      }
      {
        specialize (H7 i). rw_all. dependent destruction H7. easy.
      }
      {
        rewrite eqb_id. easy.
      }
    }
    {
      dependent destruction H0. dependent destruction H3.
      eapply TSRightOverCall with (oa':=a').
      {
        eapply IH. easy. exact H3. exact H9.
        unfold all_active_square. intros. specialize (H10 i0).
        dec_eq_nats i i0.
        {
          rw_all. dependent destruction H10.
          rewrite <- x0. rewrite <- x1. rewrite <- x3.
          econstructor.
        }
        {
          rewrite H1. rewrite H4. easy. easy. easy.
        }
      }
      { specialize (H10 i). rw_all. dependent destruction H10. easy. }
      { easy. }
      { easy. }
      { easy. }
    }
    {
      dependent destruction H0. dependent destruction H3.
      eapply TSRightOverRet with (oa':=a').
      {
        eapply IH. easy. exact H3. exact H9.
        unfold all_active_square. intros. specialize (H10 i0).
        dec_eq_nats i i0.
        {
          rw_all. dependent destruction H10.
          rewrite <- x0. rewrite <- x1. rewrite <- x3.
          econstructor.
        }
        {
          rewrite H1. rewrite H4. easy. easy. easy.
        }
      }
      { specialize (H10 i). rw_all. dependent destruction H10. easy. }
      { easy. }
      { easy. }
      { easy. }
    }
    {
      dependent destruction H2.
      eapply TSRightUnderCall with (ua':=fun j => if i =? j then Some (existT _ _ (inr m)) else o4 j).
      2:{
        specialize (H7 i). rw_all. dependent destruction H7.
        symmetry. exact x.
      }
      2:{
        specialize (H7 i). rw_all. dependent destruction H7.
        unfold differ_pointwise. intros. rewrite eqb_nid; easy.
      }
      {
        eapply IH. easy. exact H2. exact H6.
        unfold all_active_square. intros. specialize (H7 i0).
        dec_eq_nats i i0.
        {
          rewrite eqb_id. rw_all. dependent destruction H7.
          rewrite <- x1. rewrite <- x3. rewrite <- x.
          econstructor.
        }
        {
          rewrite eqb_nid. rewrite H. easy. easy. easy.
        }
      }
      {
        specialize (H7 i). rw_all. dependent destruction H7. easy.
      }
      {
        rewrite eqb_id. easy.
      }
    }
    {
      dependent destruction H2.
      eapply TSRightUnderRet with (ua':=fun j => if i =? j then None else o4 j).
      2:{
        specialize (H7 i). rw_all. dependent destruction H7.
        symmetry. exact x.
      }
      2:{
        specialize (H7 i). rw_all. dependent destruction H7.
        unfold differ_pointwise. intros. rewrite eqb_nid; easy.
      }
      {
        eapply IH. easy. exact H2. exact H6.
        unfold all_active_square. intros. specialize (H7 i0).
        dec_eq_nats i i0.
        {
          rewrite eqb_id. rw_all. dependent destruction H7.
          rewrite <- x2. rewrite <- x1. rewrite <- x.
          econstructor.
        }
        {
          rewrite eqb_nid. rewrite H. easy. easy. easy.
        }
      }
      {
        specialize (H7 i). rw_all. dependent destruction H7. easy.
      }
      {
        rewrite eqb_id. easy.
      }
    }
    {
      dependent destruction H4.
      econstructor.
      {
        eapply IH. easy. exact H2. exact H4. easy.
      }
      {
        specialize (H3 i). rw_all. dependent destruction H3.
        symmetry. exact x. easy.
      }
    }
    {
      dependent destruction H2.
      econstructor.
      {
        eapply IH. easy. exact H2. exact H4. easy.
      }
      {
        specialize (H3 i). rw_all. dependent destruction H3.
        symmetry. exact x. easy.
      }
    }
  }
  assert (
    forall i : Name T,
      @over_rel E E' F F' ((fun _ => None) i) (allIdle i) (allIdle i)
  ).
  constructor.
  generalize dependent (fun _ : Name T => @None {A & (E |+| F) A}).
  generalize dependent (fun _ : Name T => @None {A & (E' |+| F') A}).
  change (@allIdle T (E |+| F) (E' |+| F'))
  with (fun i => tensorTS (@allIdle T E E' i) (@allIdle T F F' i)).
  generalize dependent (@allIdle T E E').
  generalize dependent (@allIdle T F F').
  intros.
  generalize dependent t. generalize dependent t0.
  generalize dependent (Init specE). generalize dependent (Init specF).
  generalize dependent a.
  clear TActive.
  intros.
  eapply funct_l_help.
  exact H6. exact H4. exact H2. easy.
Qed.

Lemma join_tensor_steps {T E F} :
  forall (specE : Spec T E) (specF : Spec T F),
  forall p a tL tR,
  SeqConsistent a p ->
  forall sL sR,
  Steps (Step specE) sL (projLeft p) tL ->
  Steps (Step specF) sR (projRight p) tR ->
  exists a',
    Steps (TensorStep specE specF) (MkTS a sL sR) p (MkTS a' tL tR).
Proof.
  intros specE specF p a tL tR. intro. induction H; cbn; intros.
  {
    dependent destruction H. dependent destruction H0.
    repeat econstructor.
  }
  {
    destruct m; cbn in *.
    {
      dependent destruction H3.
      eapply IHSeqConsistent in H4. 2: exact H5.
      destruct_all. exists x.
      eapply StepsMore with (st'':= MkTS a' _ _); cbn.
      split. exact H3.
      easy.
      easy.
    }
    {
      dependent destruction H4.
      eapply IHSeqConsistent in H5. 2: exact H3.
      destruct_all. exists x.
      eapply StepsMore with (st'':= MkTS a' _ _); cbn.
      split. exact H4.
      easy.
      easy.
    }
  }
  {
    destruct m; cbn in *.
    {
      dependent destruction H3.
      eapply IHSeqConsistent in H4. 2: exact H5.
      destruct_all. exists x.
      eapply StepsMore with (st'':= MkTS a' _ _); cbn.
      split. exact H3.
      easy.
      easy.
    }
    {
      dependent destruction H4.
      eapply IHSeqConsistent in H5. 2: exact H3.
      destruct_all. exists x.
      eapply StepsMore with (st'':= MkTS a' _ _); cbn.
      split. exact H4.
      easy.
      easy.
    }
  }
Qed.

Inductive left_constraint {E E' F F'} : Status (E |+| F) -> ThreadState (E |+| F) (E' |+| F') -> ThreadState E E' -> Prop :=
| LCIdle :
    left_constraint None Idle Idle
| LCLeftCont A (om : E' A) p :
    left_constraint None (Cont (inl om) (mapProg (fun _ => inl) p)) (Cont om p)
| LCLeftUCall A (om : E' A) B (um : E B) k :
    left_constraint (Some (existT _ _ (inl um))) (UCall (inl om) (inl um) (fun x => mapProg (fun _ => inl) (k x))) (UCall om um k)
| LCRightCont A (om : F' A) p :
    left_constraint None (Cont (inr om) (mapProg (fun _ => inr) p)) Idle
| LCRightUCall A (om : F' A) B (um : F B) k :
    left_constraint (Some (existT _ _ (inr um))) (UCall (inr om) (inr um) (fun x => mapProg (fun _ => inr) (k x))) Idle.

Inductive right_constraint {E E' F F'} : Status (E |+| F) -> ThreadState (E |+| F) (E' |+| F') -> ThreadState F F' -> Prop :=
| RCIdle :
    right_constraint None Idle Idle
| RCLeftCont A (om : F' A) p :
    right_constraint None (Cont (inr om) (mapProg (fun _ => inr) p)) (Cont om p)
| RCLeftUCall A (om : F' A) B (um : F B) k :
    right_constraint (Some (existT _ _ (inr um))) (UCall (inr om) (inr um) (fun x => mapProg (fun _ => inr) (k x))) (UCall om um k)
| RCRightCont A (om : E' A) p :
    right_constraint None (Cont (inl om) (mapProg (fun _ => inl) p)) Idle
| RCRightUCall A (om : E' A) B (um : E B) k :
    right_constraint (Some (existT _ _ (inl um))) (UCall (inl om) (inl um) (fun x => mapProg (fun _ => inl) (k x))) Idle.

Theorem tensor_layer_funct_r {T E F E' F'}:   
  forall (specE : Spec T E) (specF : Spec T F) (M : Impl E E') (N : Impl F F'),
  specRefines
    ((specE ⊗ specF) ▷ (M :⊗: N))
    ((specE ▷ M) ⊗ (specF ▷ N)).
Proof.
  unfold specRefines, Incl, IsTraceOfSpec. intros. destruct_all.
  simpl (Init _) in *.
  assert (H' := H).
  rewrite projInterSteps in H. destruct_all. subst. cbn.
  destruct x, s.
  cut (
    exists a' tL tR,
      Steps (TensorStep (overObj (specE:>M)) (overObj (specF:>N)))
        (MkTS (specL:= overObj (specE:>M)) (specR:= overObj (specF:>N)) (fun _ => None) (allIdle, Init specE) (allIdle, Init specF))
        (projOver x0)
        (MkTS (specL:= overObj (specE:>M)) (specR:= overObj (specF:>N)) a' (tL, LState) (tR, RState))
  ).
  { intros. destruct_all. eexists. exact H. }
  clear H1.
  cut (
    (exists tL,
      Steps (Step (overObj (specE:>M))) (allIdle, Init specE) (projLeft (projOver x0)) (tL, LState)) /\
    (exists tR,
      Steps (Step (overObj (specF:>N))) (allIdle, Init specF) (projRight (projOver x0)) (tR, RState))
  ).
  {
    intros. destruct_all.
    apply swapEx. exists x1. apply swapEx. exists x.
    repeat rewrite projInterSteps in H, H1. destruct_all.
    apply join_tensor_steps.
    eapply (seq_cons _). exact H'.
    easy.
    easy.
  }
  clear H'.
  repeat rewrite projInterSteps. split; cbn in *.
  cut (
    exists (tL : ThreadsSt T E E') (q : list (ThreadLEvent T E E')),
      projLeft (projOver x0) = projOver q /\
      InterSteps M (allIdle, Init specE) q (tL, LState)
  ).
  {
    intros. destruct_all. exists x, x1.
    split. easy.
    split. easy.
    dependent destruction H1.
    left. easy.
    unfold InterStep, ThreadsStep in H1. destruct_all.
    dependent destruction H1. unfold ThreadStep in H1.
    destruct ev, l; cbn in *.
    dependent destruction H1.
    right. repeat econstructor.
  }
  {
    assert (
      forall i : Name T,
        @left_constraint E E' F F' ((fun _ => None) i) (allIdle i) (allIdle i)
    ).
    { constructor. }
    generalize dependent (fun _ : Name T => @None {A & (E |+| F) A}).
    generalize dependent (@allIdle T E E').
    generalize dependent (@allIdle T (E |+| F) (E' |+| F')).
    generalize dependent (Init specE). generalize dependent (Init specF).
    intros.
    generalize dependent o. generalize dependent t1.
    generalize dependent t0. generalize dependent s0.
    generalize dependent s.
    induction x0; cbn; intros; destruct_steps.
    {
      repeat econstructor. easy.
    }
    {
      destruct a, l, ev; cbn in *.
      destruct e, m; cbn in *;
      destruct_all; subst;
      destruct_steps; cbn in *.
      {
        assert (H3' := H3). specialize (H3 n).
        rewrite H4 in *. rewrite <- x1 in *.
        dependent destruction H3.
        {
          destruct p;
          rewrite frobProgId in x4 at 1; cbn in x4; try discriminate.
          destruct s1. apply IHx0 with (t1:=fun i => if i =? n then UCall om0 e0 p else t1 i) in H1.
          destruct_all.
          2:{
            intros. specialize (H3' i). dec_eq_nats i n.
            rewrite eqb_id.
            rewrite <- x in *. rewrite <- x2 in *. rewrite <- x1 in *.
            rewrite H4 in *. cbn in *. rewrite H5.
            dependent destruction x4. econstructor.
            rewrite eqb_nid. cbn in *.
            rewrite H6. rewrite <- H0. easy. easy. easy. easy.
          }
          exists x5, ((n, UEvent (Some (CallEv e0))) :: x6).
          cbn in *. split. easy.
          dependent destruction x4.
          eapply StepsMore with (st'':=(fun i => if i =? n then UCall om0 e p else t1 i,_)); cbn.
          unfold InterStep, ThreadsStep, StateStep. cbn. split.
          econstructor. econstructor; cbn.
          symmetry. exact x.
          rewrite eqb_id. easy.
          intros. rewrite eqb_nid; easy.
          exact H2.
          easy.
        }
        {
          destruct p; rewrite frobProgId in x4 at 1;
          cbn in *; discriminate.
        }
      }
      {
        assert (H3' := H3). specialize (H3 n).
        rewrite H4 in *. rewrite <- x1 in *.
        dependent destruction H3.
        {
          destruct p;
          rewrite frobProgId in x4 at 1; cbn in x4; try discriminate.
        }
        {
          destruct s1; cbn in *. eapply IHx0 with (t1:=t1) in H1.
          2:{
            intros. specialize (H3' i). dec_eq_nats i n.
            rewrite H4 in *. rewrite H5 in *. rewrite <- x in *.
            rewrite <- x2 in *. rewrite <- x1 in *.
            destruct p; rewrite frobProgId in x4 at 1;
            cbn in x4; try discriminate.
            dependent destruction x4. econstructor.
            rewrite H6. rewrite <- H0. easy. easy. easy.
          }
          destruct_all.
          exists x5, x6. easy.
        }
      }
      {
        assert (H3' := H3). specialize (H3 n).
        rewrite H4 in *. rewrite <- x1 in *.
        dependent destruction H3.
        destruct s1. cbn in *. apply IHx0 with (t1:=fun i => if i =? n then Cont om0 (k0 n0) else t1 i) in H1.
        2:{
          intros. specialize (H3' i). dec_eq_nats i n.
          rewrite eqb_id. rewrite H5. rewrite <- x2.
          econstructor.
          rewrite eqb_nid. rewrite H6. rewrite <- H0.
          easy. easy. easy. easy.
        }
        destruct_all.
        exists x3, ((n, UEvent (Some (RetEv e n0))) :: x4).
        split. easy.
        eapply StepsMore with (st'':=(fun i : Name T => if i =? n then Cont om0 (k0 n0) else t1 i, _)).
        unfold InterStep, ThreadsStep. cbn. split.
        econstructor. econstructor.
        cbn. symmetry. exact x.
        cbn. rewrite eqb_id. easy.
        intros. rewrite eqb_nid. easy. easy.
        exact H2.
        easy.
      }
      {
        destruct s1. cbn in *. eapply IHx0 with (t1:=t1) in H1.
        2:{
          intros. specialize (H3 i). dec_eq_nats i n.
          rewrite H4 in *. rewrite <- x1 in *.
          dependent destruction H3. rewrite <- x. rewrite H5.
          rewrite <- x2. econstructor.
          rewrite H6. rewrite <- H0. easy. easy. easy.
        }
        destruct_all.
        exists x2, x3. easy.
      }
      {
        dependent destruction H. destruct s1. cbn in *.
        dependent destruction H2.
        assert (H3' := H3). specialize (H3 n). rewrite <- x1 in H3.
        dependent destruction H3.
        {
          rewrite frobProgId in x4 at 1.
          destruct p0; cbn in x4; try discriminate.
          dependent destruction x4.
          eapply IHx0 with (t1:=fun i => if i =? n then Cont om0 p0 else t1 i) in H1.
          2:{
            intros. specialize (H3' i). dec_eq_nats i n. rewrite eqb_id.
            rewrite <- x in *. rewrite <- x3 in *. rewrite <- x1 in *.
            rewrite <- x2. econstructor.
            rewrite eqb_nid. rewrite <- H0; easy. easy.
          }
          destruct_all. exists x4, ((n, UEvent None) :: x5).
          split. easy.
          eapply StepsMore with (st'':=(fun i => if i =? n then Cont om0 p0 else t1 i,_)).
          unfold InterStep, ThreadsStep. split.
          econstructor. econstructor.
          cbn. symmetry. exact x.
          cbn. rewrite eqb_id. easy.
          intros. cbn in *. rewrite eqb_nid; easy.
          easy.
          easy.
        }
        {
          rewrite frobProgId in x4 at 1.
          destruct p0; cbn in x4; try discriminate.
          dependent destruction x4.
          eapply IHx0 with (t1:=t1) in H1.
          2:{
            intros. specialize (H3' i). dec_eq_nats i n.
            rewrite <- x3. rewrite <- x2. rewrite <- x.
            econstructor.
            rewrite <- H0; easy.
          }
          destruct_all.
          exists x4, x5. easy.
        }
      }
      {
        destruct s1. cbn in *. dependent destruction H2.
        destruct m; cbn in *; dependent destruction H; cbn in *.
        {
          eapply IHx0 with (t1:=fun i => if i =? n then Cont e (M _ e) else t1 i) in H1.
          2:{
            intros. specialize (H3 i). dec_eq_nats i n.
            rewrite eqb_id. rewrite <- x1 in *. rewrite <- x in *.
            dependent destruction H3. rewrite <- x3.
            econstructor.
            rewrite eqb_nid. rewrite <- H0; easy. easy.
          }
          specialize (H3 n). rewrite <- x1 in H3.
          dependent destruction H3.
          destruct_all.
          exists x4, ((n, OEvent (CallEv e)) :: x5).
          split. cbn. f_equal. easy.
          eapply StepsMore with (st'':=(fun i => if i =? n then Cont e (M _ e) else t1 i, _)).
          unfold InterStep, ThreadsStep. split.
          econstructor. econstructor.
          cbn. easy.
          cbn. rewrite eqb_id. easy.
          cbn. intros. rewrite eqb_nid; easy.
          easy.
          easy.
        }
        {
          eapply IHx0 with (t1:=t1) in H1.
          2:{
            intros. specialize (H3 i). dec_eq_nats i n.
            rewrite <- x1 in *. dependent destruction H3.
            rewrite <- x3. rewrite <- x. rewrite <- x2.
            econstructor.
            rewrite <- H0; easy.
          }
          destruct_all.
          exists x2, x3. easy.
        }
      }
      {
        destruct s1. cbn in *. dependent destruction H2.
        destruct m; cbn in *; dependent destruction H; cbn in *.
        {
          eapply IHx0 with (t1:=fun i => if i =? n then Idle else t1 i) in H1.
          2:{
            intros. specialize (H3 i). dec_eq_nats i n.
            rewrite eqb_id. rewrite <- x1 in *. rewrite <- x.
            dependent destruction H3.
            symmetry in x4. rewrite <- x3.
            econstructor.
            rewrite eqb_nid. rewrite <- H0; easy. easy.
          }
          specialize (H3 n). rewrite <- x1 in H3.
          dependent destruction H3.
          destruct_all.
          exists x5, ((n, OEvent (RetEv e n0)) :: x6).
          split. cbn. f_equal. easy.
          eapply StepsMore with (st'':=(fun i => if i =? n then Idle else t1 i, _)).
          unfold InterStep, ThreadsStep. split.
          econstructor. econstructor.
          cbn. rewrite frobProgId in x4 at 1.
          destruct p; cbn in x4; try discriminate.
          dependent destruction x4. easy.
          cbn. rewrite eqb_id. easy.
          cbn. intros. rewrite eqb_nid; easy.
          cbn. easy.
          easy.
        }
        {
          eapply IHx0 with (t1:=t1) in H1.
          destruct_all.
          exists x2, x3. easy.
          intros. specialize (H3 i). dec_eq_nats i n.
          rewrite <- x1 in H3. dependent destruction H3.
          rewrite <- x3. rewrite <- x2. rewrite <- x.
          econstructor.
          rewrite <- H0; easy.
        }
      }
    }
  }
  cut (
    exists (tL : ThreadsSt T F F') (q : list (ThreadLEvent T F F')),
      projRight (projOver x0) = projOver q /\
      InterSteps N (allIdle, Init specF) q (tL, RState)
  ).
  {
    intros. destruct_all. exists x, x1.
    split. easy.
    split. easy.
    dependent destruction H1.
    left. easy.
    unfold InterStep, ThreadsStep in H1. destruct_all.
    dependent destruction H1. unfold ThreadStep in H1.
    destruct ev, l; cbn in *.
    dependent destruction H1.
    right. repeat econstructor.
  }
  {
    assert (
      forall i : Name T,
        @right_constraint E E' F F' ((fun _ => None) i) (allIdle i) (allIdle i)
    ).
    { constructor. }
    generalize dependent (fun _ : Name T => @None {A & (E |+| F) A}).
    generalize dependent (@allIdle T F F').
    generalize dependent (@allIdle T (E |+| F) (E' |+| F')).
    generalize dependent (Init specF). generalize dependent (Init specE).
    intros.
    generalize dependent o. generalize dependent t1.
    generalize dependent t0. generalize dependent s0.
    generalize dependent s.
    induction x0; cbn; intros; destruct_steps.
    {
      repeat econstructor. easy.
    }
    {
      destruct a, l, ev; cbn in *.
      destruct e, m; cbn in *;
      destruct_all; subst;
      destruct_steps; cbn in *.
      {
        destruct s1. cbn in *. eapply IHx0 with (t1:=t1) in H1.
        2:{
          intros. specialize (H3 i). dec_eq_nats i n.
          rewrite H4 in *. rewrite <- x1 in *. rewrite <- x.
          dependent destruction H3. rewrite frobProgId in x4 at 1.
          destruct p; cbn in x4.
          2: discriminate. 2: discriminate.
          dependent destruction x4.
          rewrite <- x.  rewrite frobProgId in x4 at 1.
          destruct p; cbn in x4; try discriminate.
          dependent destruction x4.
          rewrite H5. econstructor.
          rewrite <- H0. rewrite H6. easy. easy. easy.
        }
        destruct_all.
        exists x2, x3. easy.
      }
      {
        assert (H3' := H3). specialize (H3 n).
        rewrite H4 in *. rewrite <- x1 in *. dependent destruction H3.
        {
          rewrite frobProgId in x4 at 1.
          destruct p; cbn in x4; try discriminate.
          dependent destruction x4.
          destruct s1. cbn in *.
          eapply IHx0 with (t1:=fun i => if i =? n then UCall om0 f p else t1 i) in H1.
          2:{
            intros. specialize (H3' i). dec_eq_nats i n.
            rewrite eqb_id.
            rewrite H4 in *. rewrite <- x1 in *. rewrite <- x2.
            rewrite H5. econstructor.
            rewrite eqb_nid. rewrite H6. rewrite <- H0.
            easy. easy. easy. easy.
          }
          destruct_all.
          exists x4, ((n, UEvent (Some (CallEv f))) :: x5).
          split. easy.
          eapply StepsMore with (st'':=(fun i => if i =? n then UCall om0 f p else t1 i, _)).
          unfold InterStep, ThreadsStep. split.
          econstructor. econstructor.
          cbn. symmetry. exact x.
          cbn. rewrite eqb_id. easy.
          cbn. intros. rewrite eqb_nid; easy.
          cbn. exact H2.
          easy.
        }
        {
          rewrite frobProgId in x4 at 1.
          destruct p; cbn in x4; discriminate.
        }
      }
      {
        assert (H3' := H3).
        destruct s1. cbn in *.
        specialize (H3 n). rewrite <- x1 in H3. rewrite H4 in H3.
        dependent destruction H3.
        eapply IHx0 with (t1:=t1) in H1.
        2:{
          intros. specialize (H3' i). dec_eq_nats i n.
          rewrite H4 in *. rewrite <- x1 in *.
          dependent destruction H3'.
          rewrite H5. rewrite <- x. rewrite <- x2.
          econstructor.
          rewrite H6. rewrite <- H0. easy. easy. easy.
        }
        destruct_all.
        exists x3, x4. easy.
      }
      {
        assert (H3' := H3). specialize (H3 n). destruct s1. cbn in *.
        rewrite H4 in *. rewrite <- x1 in *. dependent destruction H3.
        eapply IHx0 with (t1:=fun i => if i =? n then Cont om0 (k0 n0) else t1 i) in H1.
        2:{
          intros. specialize (H3' i). dec_eq_nats i n.
          rewrite eqb_id. rewrite H4 in *. rewrite <- x1 in *.
          dependent destruction H3'. rewrite H5. rewrite <- x2.
          econstructor.
          rewrite eqb_nid. rewrite <- H0. rewrite H6.
          easy. easy. easy. easy.
        }
        destruct_all.
        exists x3, ((n, UEvent (Some (RetEv f n0))) :: x4).
        split. easy.
        eapply StepsMore with (st'':=(fun i => if i =? n then Cont om0 (k0 n0) else t1 i, _)).
        unfold InterStep, ThreadsStep. split.
        econstructor. econstructor.
        cbn. symmetry. exact x.
        cbn. rewrite eqb_id. easy.
        cbn. intros. rewrite eqb_nid; easy.
        cbn. exact H2.
        easy.
      }
      {
        dependent destruction H. destruct s1. cbn in *.
        dependent destruction H2.
        assert (H3' := H3). specialize (H3 n). rewrite <- x1 in H3.
        dependent destruction H3.
        {
          rewrite frobProgId in x4 at 1.
          destruct p0; cbn in x4; try discriminate.
          dependent destruction x4.
          eapply IHx0 with (t1:=fun i => if i =? n then Cont om0 p0 else t1 i) in H1.
          2:{
            intros. specialize (H3' i). dec_eq_nats i n. rewrite eqb_id.
            rewrite <- x in *. rewrite <- x3 in *. rewrite <- x1 in *.
            rewrite <- x2. econstructor.
            rewrite eqb_nid. rewrite <- H0; easy. easy.
          }
          destruct_all. exists x4, ((n, UEvent None) :: x5).
          split. easy.
          eapply StepsMore with (st'':=(fun i => if i =? n then Cont om0 p0 else t1 i,_)).
          unfold InterStep, ThreadsStep. split.
          econstructor. econstructor.
          cbn. symmetry. exact x.
          cbn. rewrite eqb_id. easy.
          intros. cbn in *. rewrite eqb_nid; easy.
          easy.
          easy.
        }
        {
          rewrite frobProgId in x4 at 1.
          destruct p0; cbn in x4; try discriminate.
          dependent destruction x4.
          eapply IHx0 with (t1:=t1) in H1.
          2:{
            intros. specialize (H3' i). dec_eq_nats i n.
            rewrite <- x3. rewrite <- x2. rewrite <- x.
            econstructor.
            rewrite <- H0; easy.
          }
          destruct_all.
          exists x4, x5. easy.
        }
      }
      {
        destruct s1. cbn in *. dependent destruction H2.
        destruct m; cbn in *; dependent destruction H; cbn in *.
        {
          eapply IHx0 with (t1:=t1) in H1.
          destruct_all.
          exists x2, x3. easy.
          intros. specialize (H3 i). dec_eq_nats i n.
          rewrite <- x1 in H3. dependent destruction H3.
          rewrite <- x3. rewrite <- x2. rewrite <- x.
          econstructor.
          rewrite <- H0; easy.
        }
        {
          eapply IHx0 with (t1:=fun i => if i =? n then Cont f (N _ f) else t1 i) in H1.
          2:{
            intros. specialize (H3 i). dec_eq_nats i n.
            rewrite eqb_id. rewrite <- x1 in *. rewrite <- x in *.
            dependent destruction H3. rewrite <- x3.
            econstructor.
            rewrite eqb_nid. rewrite <- H0; easy. easy.
          }
          specialize (H3 n). rewrite <- x1 in H3.
          dependent destruction H3.
          destruct_all.
          exists x4, ((n, OEvent (CallEv f)) :: x5).
          split. cbn. f_equal. easy.
          eapply StepsMore with (st'':=(fun i => if i =? n then Cont f (N _ f) else t1 i, _)).
          unfold InterStep, ThreadsStep. split.
          econstructor. econstructor.
          cbn. easy.
          cbn. rewrite eqb_id. easy.
          cbn. intros. rewrite eqb_nid; easy.
          easy.
          easy.
        }
      }
      {
        destruct s1. cbn in *. dependent destruction H2.
        destruct m; cbn in *; dependent destruction H; cbn in *.
        {
          eapply IHx0 with (t1:=t1) in H1.
          destruct_all.
          exists x2, x3. easy.
          intros. specialize (H3 i). dec_eq_nats i n.
          rewrite <- x1 in H3. dependent destruction H3.
          rewrite <- x3. rewrite <- x2. rewrite <- x.
          econstructor.
          rewrite <- H0; easy.
        }
        {
          eapply IHx0 with (t1:=fun i => if i =? n then Idle else t1 i) in H1.
          2:{
            intros. specialize (H3 i). dec_eq_nats i n.
            rewrite eqb_id. rewrite <- x1 in *. rewrite <- x.
            dependent destruction H3.
            symmetry in x4. rewrite <- x3.
            econstructor.
            rewrite eqb_nid. rewrite <- H0; easy. easy.
          }
          specialize (H3 n). rewrite <- x1 in H3.
          dependent destruction H3.
          destruct_all.
          exists x5, ((n, OEvent (RetEv f n0)) :: x6).
          split. cbn. f_equal. easy.
          eapply StepsMore with (st'':=(fun i => if i =? n then Idle else t1 i, _)).
          unfold InterStep, ThreadsStep. split.
          econstructor. econstructor.
          cbn. rewrite frobProgId in x4 at 1.
          destruct p; cbn in x4; try discriminate.
          dependent destruction x4. easy.
          cbn. rewrite eqb_id. easy.
          cbn. intros. rewrite eqb_nid; easy.
          cbn. easy.
          easy.
        }
      }
    }
  }
Qed.