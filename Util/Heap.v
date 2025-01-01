Definition Addr := nat.

Definition Heap {V : Type} : Type := Addr -> option V.
Definition heap_update {V : Type} (addr : Addr) (val : V) (h : Heap) : Heap :=
  fun addr' => if Nat.eqb addr addr' then Some val else h addr'.
Definition empty_heap {V : Type} : Heap := fun _ => @None V.