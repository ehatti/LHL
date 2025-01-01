From LHL.Core Require Import
  Program.

Variant CounterSig : ESig :=
| Inc : CounterSig unit
| Get : CounterSig nat.