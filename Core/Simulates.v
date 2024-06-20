From LHL.Core Require Import
    Specs
    Program.

Section Sim.

  Context {T E}
          (spec : Spec T E) (* concrete *)
          (spec' : Spec T E) (* abstract *).

  CoInductive Simulates (s1 : spec.(State)) (s1' : spec'.(State)) : Prop :=
  | SimStep :
      (forall ev s2,
         spec.(Step) s1 ev s2 ->
         exists s2',
           spec'.(Step) s1' ev s2' /\
           Simulates s2 s2') ->
      Simulates s1 s1'.

End Sim.