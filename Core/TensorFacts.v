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
  Bool.Bool
  Arith.PeanoNat
  Logic.FunctionalExtensionality.

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

(* Lemma tensor_liftRight_trivial {E F} :
  forall (specE : Spec E) (specF : Spec F),
  forall s t c p,
  Steps (StepTensor specE specF) (c, s) (liftRight p) (c, t) <->
  Steps (Step specF) s p t.
split; intros.
{
  generalize dependent s. induction p; cbn; intros.
  {
    dependent destruction H.
    constructor.
  }
  {
    destruct a, e.
    dependent destruction H. unfold StepTensor in H. cbn in *.
    destruct_all. subst. destruct st''. cbn in *.
    econstructor. exact H. apply IHp. easy.
    dependent destruction H. unfold StepTensor in H. cbn in *.
    destruct_all. subst. destruct st''. cbn in *.
    econstructor. exact H. apply IHp. easy.
  }
}
{
  generalize dependent s. induction p; cbn; intros.
  {
    dependent destruction H.
    constructor.
  }
  {
    destruct a, e; cbn in *; dependent destruction H.
    eapply StepsMore with (st'':=(c, st'')).
    easy. apply IHp. easy.
    eapply StepsMore with (st'':=(c, st'')).
    easy. apply IHp. easy.
  }
}
Qed.

Lemma tensor_liftLeft_const {E F} :
  forall (specE : Spec E) (specF : Spec F),
  forall s t c c' p,
  Steps (TensorStep specE specF) (s, c) (liftLeft p) (t, c') ->
  c = c'.
intros. generalize dependent s. generalize dependent c.
induction p; cbn; intros.
{
  dependent destruction H.
  easy.
}
{
  destruct a, e; dependent destruction H;
  cbn in *; destruct_all; subst; destruct st''; cbn in *;
  eapply IHp; exact H0.
}
Qed.

Lemma tensor_liftRight_const {E F} :
  forall (specE : Spec E) (specF : Spec F),
  forall s t c c' p,
  Steps (StepTensor specE specF) (c, s) (liftRight p) (c', t) ->
  c = c'.
intros. generalize dependent s. generalize dependent c.
induction p; cbn; intros.
{
  dependent destruction H.
  easy.
}
{
  destruct a, e; dependent destruction H;
  cbn in *; destruct_all; subst; destruct st''; cbn in *;
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
    exists st, Steps (StepTensor specE' specF') (Init specE', Init specF') (liftLeft a) st
  ).
  {
    apply H.
    exists (x, Init specF).
    rewrite tensor_liftLeft_trivial. easy.
  }
  destruct_all.
  destruct x0.
  exists s.
  rewrite <- (tensor_liftLeft_trivial (F:=F)) with
    (specF:= specF')
    (c:= Init specF').
  assert (Init specF' = s0).
  eapply tensor_liftLeft_const. exact H1.
  subst. easy.
}
{
  intros. destruct_all. specialize (H (liftRight a)). cbn in *.
  assert (
    exists st, Steps (StepTensor specE' specF') (Init specE', Init specF') (liftRight a) st
  ).
  {
    apply H.
    exists (Init specE, x).
    rewrite tensor_liftRight_trivial. easy.
  }
  destruct_all.
  destruct x0.
  exists s0.
  rewrite <- (tensor_liftRight_trivial (E:=E)) with
    (specE:=specE')
    (c:= Init specE').
  assert (Init specE' = s).
  eapply tensor_liftRight_const. exact H1.
  subst. easy.
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
  forall p tL tR sL sR,
  Steps (StepTensor specE specF) (sL, sR) p (tL, tR) ->
  Steps (Step specE) sL (projLeft p) tL /\
  Steps (Step specF) sR (projRight p) tR.
intros specE specF p tL tR. induction p;
intros; cbn in *; dependent destruction H.
{
  repeat constructor.
}
{
  destruct a, e, m; unfold StepTensor in H;
  destruct_all; destruct st''; cbn in *; subst;
  apply IHp in H0; destruct_all.
  split. econstructor. exact H. easy. easy.
  split. easy. econstructor. exact H. easy.
  split. econstructor. exact H. easy. easy.
  split. easy. econstructor. exact H. easy.
}
Qed.

(* Lemma complete_square {E E' F F'} :
  forall p : Trace (ThreadEvent (E' |+| F')),
  forall l : Trace (ThreadLEvent E E'),
  forall r : Trace (ThreadLEvent F F'),
  projLeft p = projOver l ->
  projRight p = projOver r ->
  exists q : Trace (ThreadLEvent (E |+| F) (E' |+| F')),
    projOver q = p /\
    projLeft (projUnderThr q)  = projUnderThr l /\
    projRight (projUnderThr q) = projUnderThr r.
intros.
induction p; cbn in *; intros.
{
  
} *)

Theorem tensor_layer_funct_l {E F E' F'}:   
  forall (specE : Spec E) (specF : Spec F) (M : Impl E E') (N : Impl F F'),
  specRefines
    (tensorSpec (overObj (specE :> M)) (overObj (specF :> N)))
    (overObj (tensorLayer (specE :> M) (specF :> N))).
unfold specRefines, Incl, IsTraceOfSpec. intros.
destruct_all. destruct x.
eapply split_tensor_steps with
  (specE:= overObj (specE :> M))
  (specF:= overObj (specF :> N))
  in H.
repeat rewrite projInterSteps in *.
destruct_all. cbn in *.
clear H2 H4.


Theorem tensor_layer_funct_r {E F E' F'}:   
  forall (specE : Spec E) (specF : Spec F) (M : Impl E E') (N : Impl F F'),
  specRefines
    (overObj (tensorLayer (specE :> M) (specF :> N)))
    (tensorSpec (overObj (specE :> M)) (overObj (specF :> N))).
unfold specRefines, Incl, IsTraceOfSpec. intros. destruct_all.
simpl (Init _) in *. *)