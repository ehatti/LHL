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

Variant LocStat {T} :=
| LEmp | LAlloc (i : Name T) | LWritten.

Module WriteRacyMem.
  Variant MemState {T V} :=
  | MsIdle (heap : @Heap V) (loc : @Heap (@LocStat T))
  | MsAllocPend (t : Name T) (heap : @Heap V) (loc : @Heap (@LocStat T))
  | MsReadPend (t : Name T) (heap : @Heap V) (loc : @Heap (@LocStat T)) (addr : Addr)
  | MsWritePend (t : Name T) (heap : @Heap V) (loc : @Heap (@LocStat T)) (addr : Addr) (val : V)
  | MsUBIdle
  | MsUBPend (t : Name T) {R : Type} (m : MemSig V R)
  | MsUBWritePend (t : Name T) {R : Type} (m : MemSig V R)
                  (t' : Name T) {R' : Type} (m' : MemSig V R').
  Arguments MemState : clear implicits.

  Definition eval_heap {T V} (st : MemState T V) : option (@Heap V) :=
    match st with
    | MsIdle h _ | MsAllocPend _ h _ | MsReadPend _ h _ _ | MsWritePend _ h _ _ _ => Some h
    | _ => None
    end.
  
  Definition eval_loc {T V} (st : MemState T V) : (@Heap (@LocStat T)) :=
    match st with
    | MsIdle _ loc | MsAllocPend _ _ loc | MsReadPend _ _ loc _ | MsWritePend _ _ loc _ _ => loc
    | _ => empty_heap
    end.
  

  Variant MemStep {T V} : MemState T V -> (ThreadEvent T (MemSig V)) -> MemState T V -> Prop :=
    (* alloc steps *)
    | MemMAllocCall i h loc:
      MemStep (MsIdle h loc) (i, CallEv MAlloc) (MsAllocPend i h loc)
    | MemMAllocRet i h loc (v:V) (l:Addr):
      (* allocate a new location *)
      h l = None ->
      MemStep (MsAllocPend i h loc)
              (i, RetEv MAlloc l) 
              (* instantiate the location with some arbitrary value *)
              (MsIdle (heap_update l v h) (heap_update l (LAlloc i) loc))
    (* read steps *)
    | MemReadCall i h l loc:
      MemStep (MsIdle h loc) (i, CallEv (MRead l)) (MsReadPend i h loc l)
    | MemReadRet i h l v loc:
      (* can only read locations that are ready *)
      (* read pending values is undefined because the spec needs to ensure this will never happen *)
      h l = Some v ->
      MemStep (MsReadPend i h loc l) (i, RetEv (MRead l) v) (MsIdle h loc)
    | MemReadUndefined i h l v loc:
      (* read undefined locations cause UB *)
      h l = None ->
      (* read value is random *)
      MemStep (MsReadPend i h loc l) (i, RetEv (MRead l) v) MsUBIdle
    (* write steps *)
    | MemWriteCall i h l v loc:
      MemStep (MsIdle h loc)
              (i, CallEv (MWrite l v))
              (MsWritePend i h loc l v)
    | MemWriteCallRace i h l v j v' loc:
      i <> j ->
      MemStep (MsWritePend j h loc l v')
              (i, CallEv (MWrite l v))
              (MsUBWritePend j (MWrite l v') i (MWrite l v))
    | MemWriteRetUndef i h l v loc:
      h l = None ->
      MemStep (MsWritePend i h loc l v) (i, RetEv (MWrite l v) tt) MsUBIdle
    | MemWriteRet i h l v v' loc:
      h l = Some v' ->
      MemStep (MsWritePend i h loc l v)
              (i, RetEv (MWrite l v) tt)
              (* update the location to ready value after return *)
              (MsIdle (heap_update l v h) (heap_update l LWritten loc))
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
    | MsIdle _ _ | MsUBIdle => None
    | MsAllocPend j _ _ =>
        if i =? j then Some (existT _ _ MAlloc) else None
    | MsReadPend j _ _ l =>
        if i =? j then Some (existT _ _ (MRead l)) else None
    | MsWritePend j _ _ l v =>
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
    Init := MsIdle empty_heap empty_heap
  |}.
  Next Obligation.
    remember (fun _ : Name T => None) as tst.
    remember (MsIdle empty_heap empty_heap) as mst.
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