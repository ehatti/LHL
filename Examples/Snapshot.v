From LHL.Core Require Import
  Program
  ProgramRules
  Specs
  Logic
  LogicFacts
  Tensor
  Traces
  Linearizability.

From LHL.Examples Require Import
  OMemSpec
  LocalVarSpec
  ThreadLocal
  NameSpec
  SnapshotSpec.

From LHL.Util Require Import
  Tactics
  TransUtil
  Util.

Definition E T A :=
  LocalSig (OMemSig A) |+|
  LocalSig (VarSig (set A * set A)) |+|
  LocalSig (VarSig nat) |+|
  NameSig T.

Definition VE T A : Spec T (E T A) :=
  tensorSpec
    (localSpec omemSpec)
    (tensorSpec
      (localSpec varSpec)
      (tensorSpec
        (localSpec varSpec)
        nameSpec)).

Definition F A := SnapshotSig A.
Definition VF T A := @snapshotSpec T A.

Definition bool_prop (P : Prop) : bool :=
  if classicT P then true else false.

Definition cellsState {T A} (s : InterState (F A) (VE T A)) : Name T -> State omemSpec :=
  LState (snd s).

Definition setsState {T A} (s : InterState (F A) (VE T A)) : Name T -> State varSpec :=
  LState (RState (snd s)).

Definition ixState {T A} (s : InterState (F A) (VE T A)) : Name T -> State varSpec :=
  LState (RState (RState (snd s))).

Definition nameState {T A} (s : InterState (F A) (VE T A)) : State nameSpec :=
  RState (RState (RState (snd s))).

(* fst is old, snd is new *)
Definition update {T A} (v : A) : Prog (E T A) (set A) :=
  self <- call Self;
  let self := proj1_sig self in
  call (At self (Write v));;
  call (At self (Put (emp, insert v emp)));;
  while (
    sets <- call (At self Get);
    ret (bool_prop (fst sets <> snd sets))
  ) (
    call (At self (Put 0));;
    (* get old *)
    while (
      i <- call (At self Get);
      ret (bool_prop (i < T))
    ) (
      i <- call (At self Get);
      v <- call (At i Read);
      sets <- call (At self Get);
      call (At self (Put (insert v (fst sets), snd sets)))
    );;
    call (At self (Put 0));;
    (* get new *)
    while (
      i <- call (At self Get);
      ret (bool_prop (i < T))
    ) (
      i <- call (At self Get);
      v <- call (At i Read);
      sets <- call (At self Get);
      call (At self (Put (fst sets, insert v (snd sets))))
    )
  );;
  old_new <- call (At self Get);
  ret (snd old_new).

Definition snapshotImpl T A : Impl (E T A) (SnapshotSig A) :=
  fun i m => match m with
  | Update v => update v
  end.

Definition Relt T A := Relt (VE T A) (VF T A).
Definition Prec T A := Prec (VE T A) (VF T A).
Definition Post T A := Post (VE T A) (VF T A).

Definition Inv {T A} : Prec T A :=
  fun s ρs => exists ρ, ρs = eq ρ /\ (
    forall v,
      (exists i b, cellsState s i = OMemCanRead v b) <->
      (exists vs m,
        PState ρ = SnapDef vs m /\
        v ∈ vs)
  ).

Definition InvN {T A} : Prec T A :=
  fun s ρs => exists ρ, ρs = eq ρ /\ (
    
  ).