Require Import VUtils.
Require Import List.
Require Import GM.
Require Import ZArith.
Require Import FImplTest.

Import ListNotations.

Open Local Scope nat_scope.
Open Local Scope string_scope.

Require Import Xlator.
Require Import RM.

Definition muXlator (m : tGMState) : tXlator := 
    mkXlator 0 0 0 [] [] [] [] m.
    
Open Scope Z_scope.
Definition regSet : tRegVals :=
    [0; 0; 0; 0; 0; 0; 0].

Open Local Scope nat_scope.

Definition muRM : tRMState :=
    ((regSet, regSet, regSet), (nil), (nil), 0, (nil), (nil)).

Definition convertGM2RM (gm : tGMState) (rm : tRMState) : tRMState := 
    let
        xlator := translate (muXlator gm)
    in
        RMi.loadMachine xlator.(fCode) xlator.(fCodeTable) rm.

Definition testConversion : tRMState :=
    convertGM2RM testGM muRM.

Open Scope Z_scope.

Eval compute in (runMachine 200 testConversion).

Close Local Scope nat_scope.
Close Local Scope string_scope.
