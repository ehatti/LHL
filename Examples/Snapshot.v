From LHL.Core Require Import
  ProgramRules
  LogicFacts
  SingConds
  Program
  VisPoss
  Tensor
  Traces
  Specs
  Logic.

From LHL.Examples Require Import
  SnapshotSpec
  ArraySpec
  NameSpec
  RegSpec.

From LHL.Util Require Import
  TransUtil
  Tactics
  Util.

Record reg_st {A} := {
  val : option A;
  ran : bool
}.
Arguments reg_st : clear implicits.

Definition E T A :=
  NameSig T |+|
  ArraySig (RegSig (reg_st A)) T.

Definition VE T A : Spec T (E T A) :=
  tensorSpec
    nameSpec
    (arraySpec T (regSpec {| val := None; ran := false |})).

Definition F A := SnapSig A.
Definition VF T A := @snapSpec T A.

Notation valSt s i := (
  match RState (snd s) i with
  | RegDef s _ => s.(val)
  end
).

Notation ranSt s i := (
  match RState (snd s) i with
  | RegDef s _ => s.(ran)
  end
).

Notation snapSt x := (
  match PState x with
  | SnapDef s _ _ => s
  end
).

Definition StateM E A R :=
  A -> Prog E (R * A).

Definition runStateM {E A R} (a : A) (m : StateM E A R) : Prog E R :=
  p <- m a;
  ret (fst p).

Definition get {E A} : StateM E A A :=
  fun a => ret (a, a).

Definition put {E A} (s : A) : StateM E A unit :=
  fun _ => ret (tt, s).

Definition upd {E A} (f : A -> A) : StateM E A unit :=
  fun s => ret (tt, f s).

Definition bindM {E A B C}
  (m : StateM E A B)
  (k : B -> StateM E A C)
: StateM E A C :=
  fun s =>
    p <- m s;
    k (fst p) (snd p).

Definition retM {E A R} (x : R) : StateM E A R :=
  fun s => ret (x, s).

Definition lift {E A R} (p : Prog E R) : StateM E A R :=
  fun s =>
    r <- p;
    ret (r, s).

Notation "x <- f ;' m" := (bindM f (fun x => m)) (at level 80, right associativity).
Notation "f ;;' m" := (bindM f (fun _ => m)) (at level 80, right associativity).

Section while.

Context {E A} (b : A -> bool) (e : StateM E A unit).

CoFixpoint whileAux (e' : Prog E (unit * A)) : Prog E (unit * A) :=
  match e' with
  | Return (tt, t) =>
    if b t then
      NoOp (whileAux (e t))
    else
      ret (tt, t)
  | Bind m k =>
    Bind m (fun x => whileAux (k x))
  | NoOp e' => NoOp (whileAux e')
  end.

Definition while s := NoOp (whileAux (e s)).

End while.

Fixpoint range {E A} (n : nat) (e : nat -> StateM E A unit) : StateM E A unit :=
  match n with
  | 0 => retM tt
  | S n => e n ;;' range n e
  end.

Definition prop (P : Prop) : bool :=
  if classicT P then true else false.

Lemma prop_split P :
  (P /\ prop P = true) \/ (~P /\ prop P = false).
Proof.
  unfold prop.
  destruct (classicT P).
  now left.
  now right.
Qed.

Record loop_st {A} := {
  old : set A;
  new : set A
}.
Arguments loop_st : clear implicits.

(* fst is old, snd is new *)
Definition write_snapshot {T A} (v : A) : Prog (E T A) (option (set A)) :=
  i <- call Self;
  let i := proj1_sig i in
  st <- call (At i Read);
  if st.(ran) then
    ret None
  else
    call (At i (Write {| val := Some v; ran := true |}));;
    runStateM {| old := emp; new := emp |} (
      while (fun s => prop (s.(new) <> s.(old))) (
        s <- get;'
        put {| old := s.(new); new := emp |};;'
        range T (fun i =>
          v <- lift (call (At i Read));'
          s <- get;'
          match v.(val) with
          | Some v => put {| old := s.(old); new := insert v s.(new)|}
          | None => retM tt
          end
        )
      );;'
      s <- get;'
      retM (Some s.(new))
    ).

Definition snapImpl T A : Impl (E T A) (SnapSig A) :=
  fun _ m => match m with
  | WriteSnap v => write_snapshot v
  end.

Definition Relt T A := SRelt (VE T A) (VF T A).
Definition Prec T A := SPrec (VE T A) (VF T A).

Notation "x ⊆ y" :=
  (forall v, v ∈ x -> v ∈ y)
  (at level 40).

Record Guar {T A} (i : Name T)
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
  (t : InterState (F A) (VE T A)) (y : Poss (VF T A))
:= {
  increasing : snapSt x ⊆ snapSt y;
  call_pres : forall j, i <> j -> PCalls x j = PCalls y j;
  ret_pres : forall j, i <> j -> PRets x j = PRets y j
}.

Record Rely {T A} (i : Name T)
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
  (t : InterState (F A) (VE T A)) (y : Poss (VF T A))
:= {
  increases : snapSt x ⊆ snapSt y;
  call_stay : PCalls x i = PCalls y i;
  ret_stay : PRets x i = PRets y i
}.

Record Inv {T A}
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
:= {
  consistent :
    forall v, (exists i, valSt s i = Some v) <-> v ∈ snapSt x
}.

Record InvW {T A} (i : Name T) (v : A)
  (ls : loop_st A)
  (s : InterState (F A) (VE T A)) (x : Poss (VF T A))
  (b : bool)
:= {
  inv_holds : Inv s x;
  old_sub : ls.(old) ⊆ snapSt x;
  poss_status :
    if b then
      Waiting i (WriteSnap v) x
    else
      Done i (WriteSnap v) (Some ls.(new)) x
}.

Lemma ws_correct {T A} (i : Name T) (v : A) :
  VerifyProg i (LiftSRelt (Rely i)) (LiftSRelt (Guar i))
      (prComp
        (LiftSPrec Inv)
        (TInvoke (snapImpl T A) i _ (WriteSnap v)) ->>
        LiftSRelt (Rely i))
      (write_snapshot v)
      (fun _ _ _ => LiftSPrec Inv).