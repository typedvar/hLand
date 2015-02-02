Require Import VUtils.
Require Import List.
Require Import GM.
Require Import ZArith.
Require Import FImplTest.
Require Import RM.
Require Import RMMu.

Import ListNotations.

Open Local Scope nat_scope.
Open Local Scope string_scope.

Require Import Xlator.
Require Import RM.

Definition muXlator (m : tGMState) : tXlator := 
    mkXlator 0 0 0 [] [] [] [] m.
    
Eval compute in (translate (muXlator testGM)).

(****************** CODE TO TEST RM **********************)   
Definition muRM : tRMState := muRM.

Definition convertGM2RM (gm : tGMState) (rm : tRMState) : tRMState := 
    let
        xlator := translate (muXlator gm)
    in
        RMi.loadRM xlator.(fCode) xlator.(fCodeTable) rm.

Definition testConversion : tRMState :=
    convertGM2RM testGM muRM.

Open Scope Z_scope.

Eval compute in (testGM).

Definition testAssocXlation (xlator : tXlator) : tXlator :=
    translateAssocs (GMi.getGlobals xlator.(fGM)) xlator.

Eval compute in (testAssocXlation (muXlator testGM)).

Eval compute in (testConversion).

Eval compute in (runRM 0 testConversion).
Eval compute in (runRM 1 testConversion).
Eval compute in (runRM 2 testConversion).
Eval compute in (runRM 3 testConversion).
Eval compute in (runRM 4 testConversion).
Eval compute in (runRM 200 testConversion).