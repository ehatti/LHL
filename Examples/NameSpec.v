From LHL.Core Require Import
  Program
  Specs
  Logic.

From LHL.Util Require Import
  Tactics
  TransUtil
  Util.

Variant NameSig {T} : ESig :=
| Self : NameSig (Name T).
Arguments NameSig : clear implicits.

Definition NameState T := ActiveMap T (NameSig T).

Variant NameStep {T} : NameState T -> ThreadEvent T (NameSig T) -> NameState T -> Prop :=
| CallSelf i m m' :
    m i = None ->
    m' i = Some (existT _ _ Self) ->
    differ_pointwise m m' i ->
    NameStep m (i, CallEv Self) m'
| RetSelf i m m' :
    m i = Some (existT _ _ Self) ->
    m' i = None ->
    differ_pointwise m m' i ->
    NameStep m (i, RetEv Self i) m'.

Program Definition nameSpec {T} : Spec T (NameSig T) := {|
  State := NameState T;
  Step := NameStep;
  Init _ := None
|}.

Admit Obligations.