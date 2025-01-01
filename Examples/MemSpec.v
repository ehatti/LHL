From LHL.Core Require Import
  Program
  Specs
  Logic.

From LHL.Util Require Import
  Tactics
  TransUtil
  Util
  Heap.

Require Import Coq.Logic.FunctionalExtensionality.

Variant MemSig {V} : ESig :=
| MAlloc : MemSig Addr
| MWrite (addr : Addr) (val : V) : MemSig unit
| MRead (addr : Addr) : MemSig V.
Arguments MemSig : clear implicits.

Module WriteRacyMem.
  Variant MemState {T V} :=
  | MsIdle (heap : @Heap V)
  | MsAllocPend (t : Name T) (heap : @Heap V)
  | MsReadPend (t : Name T) (heap : @Heap V) (addr : Addr)
  | MsWritePend (t : Name T) (heap : @Heap V) (addr : Addr) (val : V)
  | MsUBIdle
  | MsUBPend (t : Name T) {R : Type} (m : MemSig V R)
  | MsUBWritePend (t : Name T) {R : Type} (m : MemSig V R)
                  (t' : Name T) {R' : Type} (m' : MemSig V R').
  Arguments MemState : clear implicits.

  Definition eval_heap {T V} (st : MemState T V) : option (@Heap V) :=
    match st with
    | MsIdle h | MsAllocPend _ h | MsReadPend _ h _ | MsWritePend _ h _ _ => Some h
    | _ => None
    end.

  Variant MemStep {T V} : MemState T V -> (ThreadEvent T (MemSig V)) -> MemState T V -> Prop :=
    (* alloc steps *)
    | MemMAllocCall i h:
      MemStep (MsIdle h) (i, CallEv MAlloc) (MsAllocPend i h)
    | MemMAllocRet i h (v:V) (l:Addr):
      (* allocate a new location *)
      h l = None ->
      MemStep (MsAllocPend i h)
              (i, RetEv MAlloc l) 
              (* instantiate the location with some arbitrary value *)
              (MsIdle (heap_update l v h))
    (* read steps *)
    | MemReadCall i h l:
      MemStep (MsIdle h) (i, CallEv (MRead l)) (MsReadPend i h l)
    | MemReadRet i h l v:
      (* can only read locations that are ready *)
      (* read pending values is undefined because the spec needs to ensure this will never happen *)
      h l = Some v ->
      MemStep (MsReadPend i h l) (i, RetEv (MRead l) v) (MsIdle h)
    | MemReadUndefined i h l v:
      (* read undefined locations cause UB *)
      h l = None ->
      (* read value is random *)
      MemStep (MsReadPend i h l) (i, RetEv (MRead l) v) MsUBIdle
    (* write steps *)
    | MemWriteCall i h l v:
      MemStep (MsIdle h)
              (i, CallEv (MWrite l v))
              (MsWritePend i h l v)
    | MemWriteCallRace i h l v j v':
      i <> j ->
      MemStep (MsWritePend j h l v')
              (i, CallEv (MWrite l v))
              (MsUBWritePend j (MWrite l v') i (MWrite l v))
    | MemWriteRetUndef i h l v:
      h l = None ->
      MemStep (MsWritePend i h l v) (i, RetEv (MWrite l v) tt) MsUBIdle
    | MemWriteRet i h l v v':
      h l = Some v' ->
      MemStep (MsWritePend i h l v)
              (i, RetEv (MWrite l v) tt)
              (* update the location to ready value after return *)
              (MsIdle (heap_update l v h))
    (* UB steps *)
    | MemStepUBCall i R (m : MemSig _ R):
      MemStep MsUBIdle (i, CallEv m) (MsUBPend i m)
    | MemStepUBRet i R (m : MemSig _ R) v:
      MemStep (MsUBPend i m) (i, RetEv m v) MsUBIdle
    | MemStepUBWriteRet i R (m : MemSig _ R) v j R' (m' : MemSig _ R'):
      i <> j ->
      MemStep (MsUBWritePend i m j m') (i, RetEv m v) (MsUBPend j m').
  Arguments MemStep : clear implicits.

  Definition mst2tst {T V} (st : MemState T V) (i : Name T) : option {R : Type & MemSig V R} :=
    match st with
    | MsIdle _ | MsUBIdle => None
    | MsAllocPend j _ =>
        if i =? j then Some (existT _ _ MAlloc) else None
    | MsReadPend j _ l =>
        if i =? j then Some (existT _ _ (MRead l)) else None
    | MsWritePend j _ l v =>
        if i =? j then Some (existT _ _ (MWrite l v)) else None
    | MsUBPend j m => 
        if i =? j then Some (existT _ _ m) else None
    | MsUBWritePend j1 m1 j2 m2 => 
        if i =? j1 then Some (existT _ _ m1) else
          if i =? j2 then Some (existT _ _ m2) else None
    end.


  Program Definition memSpec {T A} : Spec T (MemSig A) := {|
    State := MemState T A;
    Step := MemStep T A;
    Init := MsIdle empty_heap
  |}.
  Next Obligation.
    remember (fun _ : Name T => None) as tst.
    remember (MsIdle empty_heap) as mst.
    assert (tst = mst2tst mst);
    [apply functional_extensionality; intros; subst; auto|].
    rewrite H0.
    clear dependent tst.
    clear Heqmst.

    generalize dependent mst.
    induction p; intros; try constructor.

    inversion H; subst; clear H.
    inversion H2; subst;
    try (eapply SCCall; eauto;
    [simpl; rewrite eqb_id; auto|]);
    try (eapply SCRet; eauto;
    [simpl; rewrite eqb_id; auto|
    simpl; auto|]);
    try (unfold differ_pointwise; simpl;
    intros ? Hineq; apply eqb_nid in Hineq; now rewrite Hineq).
    {
      eapply SCCall with (a' := mst2tst (MsUBWritePend j (MWrite l v') i (MWrite l v))); simpl; auto.
      - apply eqb_nid in H; now rewrite H.
      - apply eqb_nid in H; rewrite H; now rewrite eqb_id.
      - unfold differ_pointwise; simpl; intros.
        apply eqb_nid in H0; now rewrite H0.
    }
    {
      apply eqb_nid in H; now rewrite H.
    }
  Defined.
End WriteRacyMem.