(* LHL: Linearizability Hoare Logic *)

Require Import LHL.Core.Program.
Require Import LHL.Core.VCompFacts.
Require Import LHL.Core.Specs.
Require Import LHL.Core.Traces.
Require Import LHL.Util.TransUtil.
Require Import LHL.Core.RefinesFacts.
Require Import LHL.Core.Tensor.
Require Import LHL.Core.TensorFacts.
Require Import LHL.Core.Linearizability.
Require Import LHL.Core.LinFacts.
Require Import LHL.Core.Logic.
Require Import LHL.Core.LogicFacts.
Require Import LHL.Core.VisPoss.
Require Import LHL.Core.ProgramRules.
Require Import LHL.Examples.LockAround.AtomicSpec.
Require Import LHL.Examples.LockAround.LockAround.
Require Import LHL.Examples.Lock.TicketLock.
Require Import LHL.Examples.WriteSnapshot.Snapshot.
Require Import LHL.Examples.Stack.EBStack.
Require Import LHL.Examples.Stack.AtomicStackSpec.
Require Import LHL.Examples.Stack.EBLin.
Require Import LHL.Examples.Exchanger.Exchanger.
Require Import LHL.Examples.Exchanger.ElimArray.

(* This file connects the main points of the paper to the artefact. *)

(* Section 2: Motivating Example *)

(* In the paper this section gives a rough overview of the EB stack. We will cover that at the end of this file *)
(* For now, the diagram in Fig. 1 depicting the structure of the EB stack is reflected in the `EBLin` file, and the linearizability proof connecting all the independent components of the EB stack may be found there *)
Check EBStack_lin.

(* Section 3: Programming Language *)

(* Section 3.1: Effect Signature *)

(* The paper writes effect signatures as sets of operations, but defining them as `Type -> Type` type constructors is more typical in Rocq. *)
Print ESig.

(* Section 3.2: Programs *)

(* Interaction trees are defined the same as in the paper except for a minor discrepancy: the `Ret` constructor in the paper is named `Return` in the code. *)
Print Prog.

(* Section 3.3: Modules *)

(* Modules are called `Mod` in the paper, but `Impl` in this artefact. Otherwise the definition is the same. *)
Print Impl.

(* Vertical composition of modules `:▷` in the paper is notated `|>` in the artefact, and the function itself is called `implVComp` *)
Print "|>".

(* `idM` in the paper is called `idImpl` in the artefact *)
Print idImpl.

Print idProg.

(* `idM :▷ M ≈ M` in the paper *)
Check idImpl_is_identity_l.

(* `M :▷ idM ≈ M` in the paper *)
Check idImpl_is_identity_r.

(* `(M1 :▷ M2) :▷ M3 ≈ M1 :▷ (M2 :▷ M3)` in the paper *)
Check implVComp_assoc.

(* Section 3.4: Specifications *)

(* The set of thread names `𝒯` in the paper is `Name T` in the artefact,where `T : nat`. *)
Print Name.

(* The artefact defines events slightly different from the paper. Instead of a single `TEvent := α:e(a) | α:e(a).v`, we have `Event := e(a) | e(a).v` and `ThreadEvent := α:Event`. This just makes it cleaner to project the thread name off an event, which is a very frequent operation. *)
Print Event.
Print CallEv.
Print RetEv.
Print ThreadEvent.

(* Defined the same as in the paper. The `seq_cons` side-condition is only mentioned briefly in the paper as it is typically very straightfoward to prove. It just states that if a `(i, RetEv m v)` event occurs, a `(i, CallEv m)` must have happened prior. *)
Print Spec.

(* Section 3.5 *)

(* Traces are just lists. *)
Print Trace.

(* Defines paths in a labelled transition system. Used by both the `Spec` transition systems and the operational semantics. *)
Print Steps.

(* Path concatenation *)
Check Steps_app.

(* Refinement -- behavior containment *)
Print "⊑".

(* Refinement is a preorder *)
Check specRefines_refl.
Check specRefines_trans.

(* Section 3.6 *)

(* `TState` in the paper is called `ThreadState` *)
Print ThreadState.
Print ThreadsSt.
Print InterState.

(* The artefact organizes the transition rules a little differently. *)

(* We first split out the operational semantics into underlay and overlay semantics that operate on `Event`s rather than `ThreadEvent`s *)
Print UnderThreadStep.
Print OverThreadStep.
Print ThreadStep.

(* Then we lift them into `ThreadEvent`s with `PointStep`, and combine that with `StateStep` to get the full operational semantics, called `InterSteps` *)
Print ThreadsStep.
Print StateStep.
Print InterStep.
Print InterSteps.
(* This makes many of the definitions and proofs much cleaner *)

(* Same as in the paper: The object implemented by running `M` on top of `V`. It *)
Print overObj.
Locate "▷".

(* The properties of vertical composition in this section, in order from left to right. Difference: The associativity property is split out into the two sides of the two-way refinement *)
Check eutt_layerRefines.
Check mkLayer_monotonic.
Check layerRefines_VComp_assoc.
Check layerRefines_VComp_assoc_inv.

(* Section 3.7 *)

(* Module horizontal composition `M + N` in the paper is denoted `M :⊗: N` in the artefact *)
Print ":⊗:".

(* Object horizontal composition is the same as in the paper *)
Print "⊗".

(* The properties of horizontal composition in this section, again in order from left to right, top to bottom. Again the equivalence is split out into its two components *)
Check tensor_monotonic.
Check tensor_layer_funct_l.
Check tensor_layer_funct_r.
Check tensor_neutral.

(* Section 4: Linearizability and Possibilities *)

(* Section 4.1 *)

(* Definition of linearizability, same as in the paper *)
Print "↝".

(* Observational refinement and locality, also same as in the paper *)
Check lin_obs_ref.
Check locality.

(* Additionally we prove these two lemmas, which are very handy in linearizability proofs involving lots of compositions, and are straightforward applications of observational refinement and locality *)
Check vcomp_lin.
Check hcomp_lin.

(* Definition of possibilities. Same as in the paper -- a triple of the state, pending calls, and pending returns *)
Print Poss.

(* Slight departure from the paper: This transition system does not include all the rules stated in the paper, and this omission simplifies the program logic. The rules not included in this definition are handled by the `TInvoke` and `TReturn` relations *)
Print PossStep.
Print TInvoke.
Print TReturn.

(* This transition system -- which allows the user to explicitly specify the generated trace and is used to make program logic proofs easier -- does include all the rules in the paper *)
Print VisPossStep.

(* The `↠` relation in the paper is not explicitly defined, but may be seen in the `Commit` rule *)

(* Section 5: Program Logic *)

(* Section 5.3 *)

(* The module judgement -- same definition as in the paper *)
Check VerifyImpl.

(* The definition of the `ReturnStep` side condition. This side condition is omitted in the paper as it is trivially proven for nearly all objects (the only place we have had to use it in a nontrivial way is the completeness proof) *)
Print ReturnStep.

(* Section 5.4 *)

(* The program judgement -- also same as in the paper. The actual definition is called `SafeProg`, and `VerifyProg` is an alias *)
Print SafeProg.
Print VerifyProg.

(* In order from left to right top to bottom in the paper, the rules of the program judgement. Same as in the paper *)
Check SafeReturn.
Check SafeTau.
Check SafeVis.

(* The derived rules presented in the paper. There are a few more derived rules in this artefact, as well as a few ad-hoc ones proven in the `Examples` files *)
Check lemVis.
Check lemCall.

(* Section 5.5 *)

(* The commit judgement. Minor difference from the paper is that the definition of `↠` is inlined into the rule rather than being a separate definition *)
Print Commit.

(* Section 5.6: Further Examples *)

(* All examples may be found in the `Examples` folder. Here are the ones mentioned in this section *)

(* The family of lock-protected objects *)

Print AtomicSpec.
Declare Module Params : LOCK_AROUND_PARAMS.
Module LA := LockAround.Lock_Around Params.
Check LA.lockAroundLin.

(* A ticket lock implementation for use in the lock-protected family *)
Check ticketLockLin.

(* The one-shot write-snapshot mentioned in the paper *)
Check snapshotLin.

(* Verification of the EB Stack *)

(* --- As mentioned in the beginning of this file, `EBLin.v` connects all the components of the EB stack together to assemble the full linearizability proof --- *)

(* Linearizability proof for the exchanger *)
Check oneCellExchLin.

(* Linearizability of wait-free stack *)
Lemma WFStackLin T A :
  WaitFreeStack.VE (T:=T) ▷ WaitFreeStack.WFStack A ↝ WaitFreeStack.VF.
Proof.
  eapply soundness.
  apply WaitFreeStack.WFStackCorrect.
Qed.

(* Linearizability of exchanger array *)
Check elimArrayLin.

(* Linearizability of toplevel EB stack component *)
Check EBStackLin.

(* Finally, linearizability of the _linked_ EB stack, which links together all the components *)
Check LinkedEBStack_lin.
Print LinkedEBUnderlay.
Print atomicStackSpec.

(* Section 5.7 *)

(* Soundness and completeness of the program logic, same as in the paper *)
Check soundness.
Check completeness.