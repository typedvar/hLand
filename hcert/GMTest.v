Require Import List.
Require Import ZArith.

Require Import VUtils.
Require Import VHeap.
Require Import GM.
Require Import String.
Require Import Ascii.
Require Import FImplTest.

Import ListNotations.

Definition m2 : tGMState := testGM.

Eval compute in (runGM 0 m2).
Eval compute in (runGM 1 m2).
Eval compute in (runGM 2 m2).
Eval compute in (runGM 3 m2).
Eval compute in (runGM 4 m2).
Eval compute in (runGM 5 m2).
Eval compute in (runGM 6 m2).
Eval compute in (runGM 7 m2).
Eval compute in (runGM 8 m2).
Eval compute in (runGM 9 m2).
Eval compute in (runGM 10 m2).
Eval compute in (runGM 11 m2).
Eval compute in (runGM 12 m2).
Eval compute in (runGM 13 m2).
Eval compute in (runGM 14 m2).
Eval compute in (runGM 15 m2).
Eval compute in (runGM 16 m2).
Eval compute in (runGM 17 m2).
Eval compute in (runGM 18 m2).
Eval compute in (runGM 412 m2).
Eval compute in (runGM 413 m2).
Eval compute in (runGM 5000 m2).