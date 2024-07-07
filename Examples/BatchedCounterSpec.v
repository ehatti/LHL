From LHL.Core Require Import
  Program
  Specs.

From LHL.Examples Require Import
  OMemSpec.

From LHL.Util Require Import
  Util.

Variant BCSig {A} : ESig :=
| Update (v : A) : BCSig unit
| Query : BCSig nat.

Variant BCState