Require Import List.
Require Import Datatypes.
Require Import ZArith.
Require Import String.
Require Import Ascii.

Require Import VTypes.
Require Import VUtils.

Module Export HeapImpl.

Inductive tFreeStore : Type := 
    | FreeStore : tAddrs -> tAddr -> tFreeStore.

Definition fsGetStart (fs : tFreeStore) : tAddr :=
    match fs with
    | FreeStore _ start => start
    end.

Definition fsGetFreeList (fs : tFreeStore) : tAddrs :=
    match fs with 
    | FreeStore freeList _ => freeList
    end.

Definition fsPutStart (start : tAddr) (fs : tFreeStore) : tFreeStore :=
    (FreeStore (fsGetFreeList fs) start).

Definition fsPutFreeList (freeList : tAddrs) (fs : tFreeStore) : tFreeStore :=
    (FreeStore freeList (fsGetStart fs)).

Definition fsIncrStart (fs : tFreeStore) : tFreeStore :=
    fsPutStart (S (fsGetStart fs)) fs.

Definition fsAllocateAddr (fs : tFreeStore) : (tAddr * tFreeStore) :=
    match fs with
    | FreeStore nil start => (start, fsIncrStart fs)
    | FreeStore (fAddr::fAddrs) start => (fAddr, fsPutFreeList fAddrs fs)
    end.

Definition fsFreeAddr (addr : tAddr) (fs : tFreeStore) : tFreeStore :=
    (FreeStore (addr::(fsGetFreeList fs)) (fsGetStart fs)).

Inductive tHeap (X : Type) : Type :=
    | Heap : nat -> tFreeStore -> tAssocs tAddr X -> tHeap X.
    
Implicit Arguments Heap [[X]].

Definition getHeapSize {X : Type} (h : tHeap X) : nat :=
    match h with
    | Heap size freeaddrs assocs => size
    end.

Definition getHeapFreeStore {X : Type} (h : tHeap X) : tFreeStore :=
    match h with
    | Heap size freeStore assocs => freeStore
    end.

Definition getHeapAssocs {X : Type} (h : tHeap X) : tAssocs tAddr X :=
    match h with
    | Heap size freeStore assocs => assocs
    end.

Definition putHeapSize {X : Type} (size : nat) (h : tHeap X) : tHeap X :=
    (Heap size (getHeapFreeStore h) (getHeapAssocs h)).

Definition putHeapFreeStore (fs : tFreeStore) {X : Type} (h : tHeap X) : tHeap X :=
    (Heap (getHeapSize h) fs (getHeapAssocs h)).

Definition putHeapAssocs {X : Type} (assocs : tAssocs tAddr X) (h : tHeap X) : tHeap X :=
    (Heap (getHeapSize h) (getHeapFreeStore h) assocs).

Definition addrComparator (addr1 addr2 : tAddr) : bool :=
    beq_nat addr1 addr2.

Definition incrHeapSize {X : Type} (h : tHeap X) : tHeap X :=
    putHeapSize (S (getHeapSize h)) h.

Definition decrHeapSize {X : Type} (h : tHeap X) : tHeap X :=
    match getHeapSize h with
    | O => h
    | S n => putHeapSize n h
    end.

Definition allocateAddr {X : Type} (h : tHeap X) : option ((tHeap X) * tAddr) :=
    match (fsAllocateAddr (getHeapFreeStore h)) with
    | (free, freeStore) => Some (putHeapFreeStore freeStore (incrHeapSize h), free)
    end.

Definition hAlloc {X : Type} (h : tHeap X) (a : X) : option ((tHeap X) * tAddr) :=
    match allocateAddr h with
    | Some (h', newaddr) => Some (putHeapAssocs ((newaddr, a)::(getHeapAssocs h')) h', newaddr)
    | None => None
    end.

Definition hLookup {X : Type} (h : tHeap X) (addr : tAddr) : option X :=
    assocLookup (getHeapAssocs h) addr beq_nat.

Definition hUpdate {X : Type} (h : tHeap X) (addr : tAddr) (x : X) : tHeap X :=
    putHeapAssocs ((addr, x) :: (assocRemove (getHeapAssocs h) addr beq_nat)) h.

Definition hFree (X : Type) (h : tHeap X) (addr : tAddr) : tHeap X :=
    putHeapFreeStore
        (fsFreeAddr addr (getHeapFreeStore h)) 
        (putHeapAssocs 
            (assocRemove 
                (getHeapAssocs h) 
                addr 
                beq_nat) 
            (decrHeapSize h)
        ).

End HeapImpl.
