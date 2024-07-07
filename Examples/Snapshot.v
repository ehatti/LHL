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
  CellSpec
  ThreadLocal
  WriteSnapshotSpec.

From LHL.Util Require Import
  Tactics
  TransUtil
  Util.

From Coq Require Import
  Strings.String.

Definition Underlay A :=
  LocalSig (CellSig A) |+| LocalSig (CellSig (set A * set A)) |+| LocalSig (CellSig nat).
Definition VE A : Spec (Underlay A) :=
  tensorSpec (localSpec (cellSpec _))(tensorSpec (localSpec (cellSpec _)) (localSpec (cellSpec _))).

Definition bool_prop (P : Prop) : bool :=
  if classicT P then true else false.

(* fst is old, snd is new *)
Definition query {n} {A} self : Prog (Underlay A) (set A) :=
  call (At self (Write (emp, emp)));;
  while (
    sets <- call (At self Read);
    ret (fst sets /=? snd sets)
  ) (
    call (At self (Write 0));;
    (* get old *)
    while (
      i <- call (At self Read);
      ret (bool_prop (i < n))
    ) (
      i <- call (At self Read);
      v <- call (At i Read);
      sets <- call (At self Read);
      call (At self (Write (insert (fst sets) v, snd sets)))
    );;
    call (At self (Write 0));;
    (* get new *)
    while (
      i <- call (At self Read);
      ret (bool_prop (i < n))
    ) (
      i <- call (At self Read);
      v <- call (At i Read);
      sets <- call (At self Read);
      call (At self (Write (fst sets, insert (snd sets) v)))
    )
  );;
  sets <- call (At self Read);
  ret (fst sets).

Definition update {A} self (v : A) : Prog (Underlay A) unit :=
  call (At self (Write v)).

(* Definition snapshotImpl n A : Impl (Underlay A) (SnapshotSig A) :=
  fun i m => match m with
  | Update v => update v
  end. *)