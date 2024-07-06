From LHL.Core Require Import
  Program
  Specs.

From LHL.Examples Require Import
  OMemSpec.

From LHL.Util Require Import
  Util.

Variant WSSig {A} : ESig :=
| WS (n : A) : WSSig (list A).
Arguments WSSig : clear implicits.

Variant WSState {A} :=
| WSUB
| WSDef (* change to set *) (vs : list A) (m : ThreadName -> bool).
Arguments WSState : clear implicits.

Variant WSStep {A} : WSState A -> ThreadEvent (WSSig A) -> WSState A -> Prop :=
| WSCall i vs v m m' :
    m i = false ->
    m' i = true ->
    differ_pointwise m m' i ->
    WSStep (WSDef vs m) (i, CallEv (WS v)) (WSDef (cons v vs) m')
| WSRet i v vs m :
    m i = true ->
    WSStep (WSDef vs m) (i, RetEv (WS v) vs) (WSDef vs m)
| WSDouble i v vs m :
    m i = true ->
    WSStep (WSDef vs m) (i, CallEv (WS v)) WSUB
| WSStepUB e :
    WSStep WSUB e WSUB.