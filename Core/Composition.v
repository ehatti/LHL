From Core Require Import
  Specification
  Interaction
  Signature
  Program.

From Util Require Import
  Relation.

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
Infix "⊗" := mhcomp (at level 45, right associativity).

(* Definition of vertical composition on specifications *)

Definition svcomp {T E F}
  (V : Spec T E) (M : Mod E F)
: Spec T F :=  {|
  State := InterState T E F V.(State);
  Init := ((fun _ => Idle), V.(Init));
  Step '(ths, s) e thtt :=
    exists ths',
      PtRel (OSeqAgentStep M) ths e ths' /\
      exists p,
        Steps (UnderInterStep V) (ths', s) p thtt
|}.
Infix ":▷" := svcomp (at level 46, left associativity).

(* Definition of horizontal composition on specifications *)

Definition shcomp {T E F}
  (VE : Spec T E) (VF : Spec T F)
: Spec T (E ∪ F) := {|
  State := prod VE.(State) VF.(State);
  Init := (VE.(Init), VF.(Init));
  Step '(sl, sr) '(i, Evt m r) '(tl, tr) :=
    match m with
    | inl m => tr = sr /\ VE.(Step) sl (i, Evt m r) tl
    | inr m => tl = sl /\ VF.(Step) sr (i, Evt m r) tr
    end
|}.
Infix ":⊗:" := shcomp (at level 45, right associativity).