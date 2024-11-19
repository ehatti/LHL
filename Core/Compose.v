From Core Require Import
  Signature
  Transition
  Program.

(* Definition of vertical composition on modules *)

CoFixpoint substProg {E F R}
  (mod : Mod E F) (p : Prog F R) : Prog E R :=
  match p with
    | Vis m f => Tau (bindSubstProg mod f (mod _ m))
    | Ret a => Ret a
    | Tau p' => Tau (substProg mod p')
  end

with bindSubstProg
    {F F'} (impl : forall A, F' A -> Prog F A)
    {R R'} (f: R -> Prog F' R') (p: Prog F R) :=
  match p with
  | Vis m' f' => Vis m' (fun r => bindSubstProg impl f (f' r))
  | Ret a => Tau (substProg impl (f a))
  | Tau p'' => Tau (bindSubstProg impl f p'')
  end.

Definition mvcomp {E F G} (Ml : Mod E F) (Mr : Mod F G) : Mod E G :=
  fun _ g => substProg Ml (Mr _ g).
Infix "▷" := mvcomp (at level 45, right associativity).

(* Definition of horizontal composition on modules *)

CoFixpoint mapProg {E E' R}
  (f : forall A, E A -> E' A) (p : Prog E R) : Prog E' R :=
  match p with
    | Vis e f' => Vis (f _ e) (fun a => mapProg f (f' a))
    | Ret r => Ret r
    | Tau p' => Tau (mapProg f p')
  end.

Definition mhcomp {EL FL ER FR}
  (Ml : Mod EL FL) (Mr : Mod ER FR) : Mod (EL ∪ ER) (FL ∪ FR) :=
  fun _ m =>
    match m with
      | inl mL => mapProg (fun _ => inl) (Ml _ mL)
      | inr mR => mapProg (fun _ => inr) (Mr _ mR)
    end.

(* Definition of vertical composition on specifications *)

Program Definition mscomp