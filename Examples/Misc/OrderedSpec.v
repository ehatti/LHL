From LHL.Core Require Import
  Program
  Specs
  LogicFacts.

From LHL.Util Require Import
  TransUtil
  Tactics
  Util.

From LHL.Core Require Import
  Traces.

From Coq Require Import
  Unicode.Utf8.

Record OrdState {T} {E : ESig} {A : Type} := MkOS {
  os_st : A;
  os_ord : list (Name T * {R & prod (E R) R})
}.
Arguments OrdState : clear implicits.
Arguments MkOS {T E A}.

Variant OrdStep {T E} {VE : Spec T E} :
  OrdState T E VE.(State) ->
  ThreadEvent T E ->
  OrdState T E VE.(State) ->
  Prop :=
| OrdCall i x y o R (m : E R) :
  VE.(Step) x (i, CallEv m) y ->
  OrdStep
    (MkOS x o)
    (i, CallEv m)
    (MkOS y o)
| OrdRet i x y o R (m : E R) (r : R) :
  VE.(Step) x (i, RetEv m r) y ->
  OrdStep
    (MkOS x o)
    (i, RetEv m r)
    (MkOS y (app o (cons (i, existT _ R (m, r)) nil))).

Program Definition ordSpec {T E} (VE : Spec T E)
: Spec T E := {|
  State := OrdState T E VE.(State);
  Step := OrdStep;
  Init := MkOS VE.(Init) nil
|}.

Next Obligation.
  assert (Steps VE.(Step) VE.(Init) p s.(os_st)).
  {
    generalize dependent (Init VE).
    generalize dependent (@nil (Name T * {R & prod (E R) R})).
    induction p; intros; ddestruct H; simpl in *.
    { constructor. }
    {
      ddestruct H.
      {
        econstructor.
        { exact H. }
        {
          eapply IHp.
          exact H0.
        }
      }
      {
        econstructor.
        { exact H. }
        {
          eapply IHp.
          exact H0.
        }
      }
    }
  }
  eapply VE.(seq_cons).
  exact H0.
Qed.

Theorem ordspec_ref {T E} :
  ∀ VE : Spec T E,
    VE ⊑ ordSpec VE.
Proof.
  unfold specRefines, Incl, IsTraceOfSpec. psimpl.
  generalize dependent (@nil (Name T * {R & prod (E R) R})).
  intros. psimpl. generalize dependent VE.(Init).
  generalize dependent l. induction a; intros; ddestruct H.
  { repeat econstructor. }
  {
    destruct a, e.
    {
      apply IHa with
        (l:=l)
        in H0.
      psimpl. exists x0.
      econstructor.
      { constructor. exact H. }
      { easy. }
    }
    {
      apply IHa with
        (l:= app l (cons (n, existT _ _ (m, n0)) nil))
        in H0.
      psimpl. exists x0.
      econstructor.
      { constructor. exact H. }
      { easy. }
    }
  }
Qed.