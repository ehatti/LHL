From LHL.Core Require Import
  Program
  Specs.

From LHL.Util Require Import
  TransUtil
  Tactics
  Util.

Variant SnapSig {A} : ESig :=
| WriteSnap (v : A) : SnapSig (option (set A)).
Arguments SnapSig : clear implicits.

Variant SnapPend {A} :=
| SnapIdle
| SnapExec (v : A)
| SnapDone.
Arguments SnapPend : clear implicits.

Variant SnapState {T A} :=
| SnapDef (vs : set A) (m : Name T -> SnapPend A) (c : Name T -> bool).
Arguments SnapState : clear implicits.

Variant SnapStep {T A} : SnapState T A -> ThreadEvent T (SnapSig A) -> SnapState T A -> Prop :=
| SnapCall i v vs m m' c :
    c i = false ->
    m i = SnapIdle ->
    m' i = SnapExec v ->
    differ_pointwise m m' i ->
    SnapStep (SnapDef vs m c) (i, CallEv (WriteSnap v)) (SnapDef (insert v vs) m' c)
| SnapRetPass i v vs m m' c c' :
    c i = false ->
    c' i = true ->
    differ_pointwise c c' i ->
    m i = SnapExec v ->
    m' i = SnapDone ->
    differ_pointwise m m' i ->
    SnapStep (SnapDef vs m c) (i, RetEv (WriteSnap v) (Some vs)) (SnapDef vs m' c')
| SnapRetFail i v vs m m' c :
    c i = true ->
    m i = SnapExec v ->
    m' i = SnapDone ->
    differ_pointwise m m' i ->
    SnapStep (SnapDef vs m c) (i, RetEv (WriteSnap v) None) (SnapDef vs m' c).

Program Definition snapSpec {T A} : Spec T (SnapSig A) := {|
  State := SnapState T A;
  Step := SnapStep;
  Init := SnapDef emp (fun _ => SnapIdle) (fun _ => false)
|}.

Next Obligation.
revert H.
pose (map (m : Name T -> SnapPend A) :=
  (fun i => match m i with
  | SnapIdle | SnapDone => None
  | SnapExec v => Some (existT _ _ (WriteSnap v))
  end) : ActiveMap T (SnapSig A)
).
cut (
  forall p vs m c,
  Steps SnapStep (SnapDef vs m c) p s ->
  SeqConsistent (map m) p
).
{
  intros.
  now apply H with
    (vs:=emp)
    (c:=fun _ => false)
    (m:=fun _ => SnapIdle).
}
clear. intro p.
induction p; intros;
ddestruct H.
{ constructor. }
{
  ddestruct H.
  {
    eapply SCCall with (a':=map m').
    { unfold map. now rewrite H0. }
    { unfold map. now rewrite H1. }
    {
      unfold differ_pointwise, map.
      intros. now rewrite H2.
    }
    { eapply IHp. exact H3. }
  }
  {
    eapply SCRet with (a':=map m').
    { unfold map. now rewrite H2. }
    { unfold map. now rewrite H3. }
    {
      unfold differ_pointwise, map.
      intros. now rewrite H4.
    }
    { eapply IHp. exact H5. }
  }
  {
    eapply SCRet with (a':=map m').
    { unfold map. now rewrite H0. }
    { unfold map. now rewrite H1. }
    {
      unfold differ_pointwise, map.
      intros. now rewrite H2.
    }
    { eapply IHp. exact H3. }
  }
}
Qed.