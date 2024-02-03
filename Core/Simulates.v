From LHL.Core Require Import
    Specs
    Program.

Section Sim.

  Context {E: ESig}
          (spec : Spec E) (* concrete *)
          (spec' : Spec E) (* abstract *).

  CoInductive Simulates_ (s1 : spec.(State)) (s1' : spec'.(State)) : Prop :=
  | SimStep :
      (forall ev s2,
         spec.(Step) s1 ev s2 ->
         exists2 s2',
           spec'.(Step) s1' ev s2' &
           Simulates_ s2 s2') ->
      Simulates_ s1 s1'.

  Definition Simulates : Prop := Simulates_ spec.(Init) spec'.(Init).

End Sim.