Require Import String.
Require Import Ascii.
Require Import List.

Module Export Typesi.

Definition tAddr := nat.

(** Heap addresses start from 1. The address 0 distinguished as
    [NullAddr] is reserved for error conditions and for pre-allocated nodes.
*)
Definition NullAddr : tAddr := 0%nat.

Definition tAddrs := list tAddr.

Definition tName := string.

Definition tAssocs (X Y : Type) := list (X * Y).

Fixpoint assocLookup {X Y : Type} 
    (assocs : tAssocs X Y) 
    (key : X) 
    (comparator : X -> X -> bool) : option Y :=
    match assocs with
    | nil => None
    | assoc :: assocs' =>
        if (comparator (fst assoc) key) 
        then 
            Some (snd assoc)
        else
            assocLookup assocs' key comparator
    end.

Fixpoint assocRemove {X Y : Type} 
    (assocs : tAssocs X Y) 
    (key : X) 
    (comparator : X -> X -> bool) : tAssocs X Y :=
    match assocs with
    | nil => nil
    | assoc :: assocs' =>
        if (comparator (fst assoc) key) 
        then 
            assocs'
        else
            assoc :: (assocRemove assocs' key comparator)
    end.

End Typesi.
