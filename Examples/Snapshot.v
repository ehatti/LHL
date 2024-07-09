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
  MRSWCellSpec
  LocalVarSpec
  ThreadLocal
  NameSpec
  SnapshotSpec.

From LHL.Util Require Import
  Tactics
  TransUtil
  Util.

Definition E T A :=
  LocalSig (CellSig A) |+|
  LocalSig (VarSig (set A * set A)) |+|
  LocalSig (VarSig nat) |+|
  NameSig T.

Definition VE T A : Spec T (E T A) :=
  tensorSpec
    (localSpec cellSpec)
    (tensorSpec
      (localSpec varSpec)
      (tensorSpec
        (localSpec varSpec)
        nameSpec)).

Definition F A := SnapshotSig A.
Definition VF T A := @snapshotSpec T A.

Definition bool_prop (P : Prop) : bool :=
  if classicT P then true else false.

Definition cellsState {T A} (s : InterState (F A) (VE T A)) : Name T -> State cellSpec :=
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
    old_new <- call (At self Get);
    ret (bool_prop (fst old_new <> snd old_new))
  ) (
    call (At self (Put 0));;
    old_new <- call (At self Get);
    call (At self (Put (snd old_new, emp)));;
    while (
      i <- call (At self Get);
      ret (bool_prop (i < T))
    ) (
      i <- call (At self Get);
      v <- call (At i Read);
      old_new <- call (At self Get);
      call (At self (Put (fst old_new, insert v (snd old_new))));;
      call (At self (Put (i + 1)))
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

Definition Inv {T A}
  (sm : VarPend T (set A * set A))
  (am : VarPend T nat)
  (cm : CellPend T A)
  : Name T -> Prec T A :=
  fun i s ρs =>
    True.