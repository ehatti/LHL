Require Import Coq.Arith.PeanoNat.

Definition Addr := nat.

Definition Heap {V : Type} : Type := Addr -> option V.
Definition heap_update {V : Type} (addr : Addr) (val : V) (h : Heap) : Heap :=
  fun addr' => if Nat.eqb addr addr' then Some val else h addr'.
Definition empty_heap {V : Type} : Heap := fun _ => @None V.

Lemma HeapUpdateOther {V : Type} (l1 l2: Addr) (val : V) (h : Heap):
  l1 <> l2 -> heap_update l1 val h l2 = h l2.
Proof.
  unfold heap_update. intros.
  destruct (Nat.eqb l1 l2) eqn:eq; auto.
  apply Nat.eqb_eq in eq. congruence.
Qed.

Lemma HeapUpdateSelf {V : Type} (l: Addr) (val : V) (h : Heap):
  heap_update l val h l = Some val.
Proof.
  unfold heap_update.
  now rewrite Nat.eqb_refl.
Qed.

