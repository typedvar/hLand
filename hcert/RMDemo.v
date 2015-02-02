Require Import VUtils.
Require Import VHeap.
Require Import RM.
Require Import List.
Require Import ZArith.
Require Import RMMu.
Require Import RMOut.

Import ListNotations.

Open Scope Z_scope.
Open Local Scope string_scope.

Definition fact10 := loadRM (prog 10%Z) symTable muRM.

Eval compute in (runRM 10 fact10).
Eval compute in (runRM 100 fact10).
Eval compute in (runRM 1000 fact10).