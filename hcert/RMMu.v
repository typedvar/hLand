Require Import VUtils.
Require Import VHeap.
Require Import RM.
Require Import List.
Require Import ZArith.

(** * Minimal empty register machine definition
*)

Module Export RMMui.

Import ListNotations.

Open Scope Z_scope.

Definition regSet : tRegVals :=
    [0; 0; 0; 0; 0; 0; 0].

Open Local Scope nat_scope.

(** Our first machine, $\mu$-RM, is defined as follows:
*)

Definition muHeapData : tHeapData := 
(Heap 0 (FreeStore [] 1) []).

Definition muHeap : tRMHeap := mkHeap 0 muHeapData.

Definition muStack : tRMStack := mkStack 100 (nil).

Definition muRM : tRMState :=
    ((regSet, regSet, regSet), (nil), 0, (nil), (nil), muHeap, muStack).

Close Local Scope nat_scope.

Close Local Scope Z_scope.

End RMMui.
