Require Import List.
Require Import ZArith.
Require Import VUtils.
Require Import VHeap.
Require Import GM.

Module Export FImplTesti.
Import ListNotations.

Open Local Scope nat_scope.
Open Local Scope string_scope.

Definition testGM : tGMState :=
(
0%Z, 
[PushGlobal "main"; Eval; Print], 
nil, 
nil, 
(Heap 
 20
 (FreeStore [] 21)
 [
    (1, (NGlobal 1 [Push 0; Eval; Update 1; Pop 1; Unwind])); 
    (2, (NGlobal 2 [Push 0; Eval; Update 2; Pop 2; Unwind])); 
    (3, (NGlobal 2 [Push 1; Eval; Update 2; Pop 2; Unwind])); 
    (4, (NGlobal 3 [Push 2; Push 2; MkAp; Push 3; Push 2; MkAp; MkAp; Eval; Update 3; Pop 3; Unwind])); 
    (5, (NGlobal 3 [Push 2; Push 2; MkAp; Push 1; MkAp; Eval; Update 3; Pop 3; Unwind])); 
    (6, (NGlobal 1 [Push 0; Push 1; PushGlobal "compose"; MkAp; MkAp; Eval; Update 1; Pop 1; Unwind])); 
    (7, (NGlobal 2 [Push 1; Eval; Push 1; Eval; Add ; Update 2; Pop 2; Unwind])); 
    (8, (NGlobal 2 [Push 1; Eval; Push 1; Eval; Sub ; Update 2; Pop 2; Unwind])); 
    (9, (NGlobal 2 [Push 1; Eval; Push 1; Eval; Mul ; Update 2; Pop 2; Unwind])); 
    (10, (NGlobal 2 [Push 1; Eval; Push 1; Eval; Div ; Update 2; Pop 2; Unwind])); 
    (11, (NGlobal 1 [Push 0; Eval; Neg ; Update 1; Pop 1; Unwind])); 
    (12, (NGlobal 2 [Push 1; Eval; Push 1; Eval; Eq ; Update 2; Pop 2; Unwind])); 
    (13, (NGlobal 2 [Push 1; Eval; Push 1; Eval; Ne ; Update 2; Pop 2; Unwind])); 
    (14, (NGlobal 2 [Push 1; Eval; Push 1; Eval; Lt ; Update 2; Pop 2; Unwind])); 
    (15, (NGlobal 2 [Push 1; Eval; Push 1; Eval; Le ; Update 2; Pop 2; Unwind])); 
    (16, (NGlobal 2 [Push 1; Eval; Push 1; Eval; Gt ; Update 2; Pop 2; Unwind])); 
    (17, (NGlobal 2 [Push 1; Eval; Push 1; Eval; Ge ; Update 2; Pop 2; Unwind])); 
    (18, (NGlobal 3 [Push 0; Eval; Cond [Push 1] [Push 2]; Update 3; Pop 3; Unwind])); 
    (19, (NGlobal 0 [PushInt 10; PushGlobal "fac"; MkAp; Eval; Update 0; Pop 0; Unwind])); 
    (20, (NGlobal 1 [PushInt 0; Push 1; Eval; Eq ; Cond [PushInt 1] [PushInt 1; Push 1; PushGlobal "-"; MkAp; MkAp; PushGlobal "fac"; MkAp; Eval; Push 1; Eval; Mul ]; Update 1; Pop 1; Unwind]))
 ]
), 
[("I", 1); ("K", 2); ("K1", 3); ("S", 4); ("compose", 5); ("twice", 6); ("+", 7); ("-", 8); ("*", 9); ("/", 10); ("negate", 11); ("==", 12); ("~=", 13); ("<", 14); ("<=", 15); (">", 16); (">=", 17); ("if", 18); ("main", 19); ("fac", 20)], 
0
).

End FImplTesti.