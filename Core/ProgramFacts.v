From LHL Require Import
    Program.

Definition frobProgram {E Ret} (p : Prog E Ret) :
  Prog E Ret :=
  match p with
    | Bind e f => Bind e f
    | Return a => Return a
    | NoOp p' => NoOp p'
  end.

Theorem frobProgId {E Ret} (p : Prog E Ret) :
  p = frobProgram p.
Proof.
  destruct p; reflexivity.
Defined.