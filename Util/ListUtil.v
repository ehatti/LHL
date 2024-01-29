From Coq Require Import
    List.

Fixpoint mapfilter {A B} (f : A -> option B) (xs : list A) : list B :=
  match xs with
  | nil => nil
  | x :: xs =>
    match f x with
    | None => mapfilter f xs
    | Some y => y :: mapfilter f xs
    end
  end.
