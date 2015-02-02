Require Import VUtils.
Require Import VHeap.
Require Import RM.
Require Import List.
Require Import ZArith.

Module Export RMOuti.

Import ListNotations.

Open Scope Z_scope.
Open Local Scope nat_scope.
Open Local Scope string_scope.

Definition symTable :=
    [
        (pair "fact" 10);
        (pair "factret" 12);
        (pair "factrec" 13);
        (pair "end" 19)
    ].
Definition prog (num : tRegVal) : tRMCode :=
    [
(* 00 *)    (Const (V, 2) num);
(*  1 *)    (Invoke_static [(V, 2)] "fact");
(*  2 *)    (Move_result (V, 0));
(*  3 *)    (Goto "end");
(*  4 *)    (Noop);
(*  5 *)    (Noop);
(*  6 *)    (Noop);
(*  7 *)    (Noop);
(*  8 *)    (Noop);
(*  9 *)    (Noop);
(* 10 *)    (If_gtz (P, 0) "factrec");
(*  1 *)    (Const (V, 0) 1);
(*  2 *)    (Ret_val (V, 0));
(*  3 *)    (Const (V, 1) (-1));
(*  4 *)    (Add (V, 0) (P, 0) (V, 1));
(*  5 *)    (Invoke_static [(V, 0)] "fact");
(*  6 *)    (Move_result (V, 0));
(*  7 *)    (Mul (V, 0) (V, 0) (P, 0));
(*  8 *)    (Goto "factret");
(*  9 *)    (Halt)
    ].
Close Local Scope nat_scope.

End RMOuti.
