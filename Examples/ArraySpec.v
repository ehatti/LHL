From LHL.Core Require Import
  Program
  ProgramRules
  Specs
  Logic
  LogicFacts
  Tensor
  Traces
  Linearizability.

From LHL.Util Require Import
  Tactics
  TransUtil
  Util.

From Coq Require Import
  Logic.FunctionalExtensionality
  Bool.Bool
  Program.Equality.

Definition Index N := {i | i < N}.

Variant ArraySig {E} {N : nat} : ESig :=
| At {A} (i : Index N) (m : E A) : ArraySig A.
Arguments ArraySig : clear implicits.

Record ArrayState {E N T} {V : Spec T E} := MkArr {
  arr_st :> Index N -> State V;
  arr_active : ActiveMap T (ArraySig E N)
}.
Arguments ArrayState : clear implicits.
Arguments MkArr {E N T V}.

Variant ActiveMapStep {T E} : ActiveMap T E -> ThreadEvent T E -> ActiveMap T E -> Prop :=
| AMCall i A m s : ActiveMapStep
  (fun j => if i =? j then None else s j)
  (i, CallEv m)
  (fun j => if i =? j then Some (existT _ A m) else s j)
| AMRet i A m v s : ActiveMapStep
  (fun j => if i =? j then Some (existT _ A m) else s j)
  (i, RetEv m v)
  (fun j => if i =? j then None else s j).

Variant ArrayStep {T E N} {V : Spec T E} :
  ArrayState E N T V ->
  ThreadEvent T (ArraySig E N) ->
  ArrayState E N T V ->
  Prop :=
| ArrayCall i A (m : E A) s t x y n :
    (* n < N -> *)
    ActiveMapStep s.(arr_active) (i, CallEv (At n m)) t.(arr_active) ->
    s.(arr_st) n = x ->
    t.(arr_st) n = y ->
    differ_pointwise s.(arr_st) t.(arr_st) n ->
    V.(Step) x (i, CallEv m) y ->
    ArrayStep s (i, CallEv (At n m)) t
| ArrayRet i A (m : E A) v s t x y n :
    (* n < N -> *)
    ActiveMapStep s.(arr_active) (i, RetEv (At n m) v) t.(arr_active) ->
    s.(arr_st) n = x ->
    t.(arr_st) n = y ->
    differ_pointwise s.(arr_st) t.(arr_st) n ->
    V.(Step) x (i, RetEv m v) y ->
    ArrayStep s (i, RetEv (At n m) v) t.
Arguments ArrayStep {T E N} V.

Fixpoint strip_arr {T N E}
  (x : Index N)
  (p : Trace (ThreadEvent T (ArraySig E N)))
: Trace (ThreadEvent T E) :=
  match p with
  | nil => nil
  | cons (i, CallEv (At y m)) p =>
    if x =? y then
      cons (i, CallEv m) (strip_arr x p)
    else
      strip_arr x p
  | cons (i, RetEv (At y m) v) p =>
    if x =? y then
      cons (i, RetEv m v) (strip_arr x p)
    else
      strip_arr x p
  end.

Lemma dpt_inplace {A B} {f : A -> B} {i : A} {x y : B} :
  differ_pointwise
    (fun j => if i =? j then x else f j)
    (fun j => if i =? j then y else f j)
    i.
Proof.
  intros. unfold differ_pointwise.
  intros. now rewrite eqb_nid.
Qed.

Lemma triv_heq {A} :
  forall x y : A,
  x = y -> x ~= y.
Proof.
  intros. now rewrite H.
Qed.

Lemma arrSC {T E N} {V : Spec T E} :
  forall p : list (ThreadEvent T (ArraySig E N)),
  forall s,
  Steps (ArrayStep V) (MkArr (fun _ => Init V) (fun _ => None)) p s ->
  SeqConsistent (fun _ : Name T => None) p.
Proof.
  intros.
  generalize dependent (fun _ : Name T => @None {A & ArraySig E N A}).
  generalize dependent (fun _ : Index N => Init V).
  intros. remember ({|arr_st := s0; arr_active := o|}).
  generalize dependent a. rename s into t.
  generalize dependent o. generalize dependent s0.
  induction p; subst; intros. constructor.
  ddestruct H. subst. ddestruct H;
  cbn in *; ddestruct H; destruct t0;
  cbn in *; subst.
  {
    eapply SCCall with
      (a':=fun j =>
        if i =? j then
          Some (existT _ _ (At n m))
        else
          s j).
    { now rewrite eqb_id. }
    { now rewrite eqb_id. }
    { apply dpt_inplace. }
    eapply IHp. easy. exact H0.
  }
  {
    eapply SCRet with
      (a':=fun j =>
        if i =? j then
          None
        else
          s j).
    { now rewrite eqb_id. }
    { now rewrite eqb_id. }
    { apply dpt_inplace. }
    eapply IHp. easy. exact H0.
  }
Qed.

Program Definition arraySpec {T E} N (V : Spec T E) : Spec T (ArraySig E N) := {|
  State := ArrayState E N T V;
  Step := ArrayStep V;
  Init := MkArr (fun _ => Init V) (fun _ => None)
|}.

Next Obligation.
Proof.
  now apply arrSC with (s:=s).
Qed.