(* begin hide *)
Require Import VUtils.
Require Import VHeap.
Require Import RM.
Require Import List.
Require Import ZArith.
Require Import RMMu.
(* end hide *)
(** * Running Programs on the R-Machine
To run the register machine we need a configuration. This configuration is
defined by the number of value, parameter and return type registers present.
For our examples, we define a machine with seven registers each for the 
value, parameter and return types.

*)
(* begin hide *)
Import ListNotations.
Open Scope Z_scope.
(* end hide *)
(** ** Arithmetic, Conditional and Unconditional Jumps
Program A demonstrates basic arithmetic, %\textbf{if-then}% instruction, and 
the unconditional jump [goto]. 

<<
        00 v0 = 2
        01 v1 = 3
        02 v2 = v0 + v1 // 2 + 3 = 5
        03 v3 = v2 + v1 // 5 + 3 = 8
        04 v4 = v3 * v3 // 8 * 8 = 64
        05 v0 = 64
        06 if v4 == v0 then 11 // true branch will be taken
        07 v2 = 6 
        08 goto 12
        09 Noop
        10 Noop
        11 v2 = 9
        12 Halt
>>
As a result of running this program register [v2] should contain a 
value of [9] as the [if] conditional evaluated to true.

*)
(* begin hide *)
Open Local Scope nat_scope.
Open Local Scope string_scope.
(* end hide *)
Definition ctA : tCodeTable :=
    [(pair "moveRes" 11);
     (pair "end" 12)
    ].

Definition programA: tRMCode :=
[ 
    (Const (V, 0) 2);
    (Const (V, 1) 3);
    (Add (V, 2) (V, 0) (V, 1));
    (Add (V, 3) (V, 2) (V, 1));
    (Mul (V, 4) (V, 3) (V, 3));
    (Const (V, 0) 64);
    (If_eq (V, 4) (V, 0) "moveRes");
    (Const (V, 2) 6);
    (Goto "end");
    (Noop);
    (Noop);
    (Const (V, 2) 9);
    (Halt)
].
Close Local Scope nat_scope.

Definition machine1 := loadRM programA ctA muRM.

(** The entire machine is dumped at each step. This lets us verify that the 
program counter is correctly incremented, and allows us to inspect the 
register values at each step of machine execution.

*)
Eval compute in (runRM 1 machine1).
Eval compute in (runRM 2 machine1).
Eval compute in (runRM 3 machine1).
Eval compute in (runRM 4 machine1).
Eval compute in (runRM 5 machine1).
Eval compute in (runRM 6 machine1).
Eval compute in (runRM 7 machine1).
Eval compute in (runRM 8 machine1).
Eval compute in (runRM 9 machine1).

Eval compute in (runRM 10 machine1).
(** The above commands perform 10 execution steps and 
     yield the following machine state:
<<
    (([64; 3; 9; 8; 64; 0; 0], [0; 0; 0; 0; 0; 0; 0],
      [0; 0; 0; 0; 0; 0; 0]), [],
       [Const (V, 0%nat) 2; Const (V, 1%nat) 3;
       Add (V, 2%nat) (V, 0%nat) (V, 1%nat);
       Add (V, 3%nat) (V, 2%nat) (V, 1%nat);
       Mul (V, 4%nat) (V, 3%nat) (V, 3%nat); Const (V, 0%nat) 64;
       If_eq (V, 4%nat) (V, 0%nat) "move"; Const (V, 2%nat) 6; Goto "end";
       Noop; Noop; Const (V, 2%nat) 9; Halt], 12%nat, [],
       [("move", 11%nat); ("end", 12%nat)])
     : tRMState
>>
As a result of running this program, we have a value of 9 in v2.
Note that the value of PC is 12, which points to the [Halt] instruction. This is
a terminal state of the machine, the [haltState], and performing 
further execution will not change the machine state.

Let us illustrate this by running the machine 10,000 times.

*)
Eval compute in (runRM 5000 machine1).
(** As expected, the machine state after 10,000 steps was identical to the first 
time we encountered the halt instruction:

<<
     = (([64; 3; 9; 8; 64; 0; 0], [0; 0; 0; 0; 0; 0; 0],
        [0; 0; 0; 0; 0; 0; 0]), [],
       [Const (V, 0%nat) 2; Const (V, 1%nat) 3;
       Add (V, 2%nat) (V, 0%nat) (V, 1%nat);
       Add (V, 3%nat) (V, 2%nat) (V, 1%nat);
       Mul (V, 4%nat) (V, 3%nat) (V, 3%nat); Const (V, 0%nat) 64;
       If_eq (V, 4%nat) (V, 0%nat) 11%nat; Const (V, 2%nat) 6; Goto 12%nat;
       Noop; Noop; Const (V, 2%nat) 9; Halt], 12%nat, [])
     : tRMState
>>

*)

(** ** Function Calls
In this section we demonstrate the function call mechanism in PVRM.
In [programB] a function [MyAdd] is defined at address [05].
At address [02] [MyAdd] is called with value 2 in [v0] and 3 in [v1].
The value returned from [MyAdd] is stored in [v2] (instruction 03),
followed by a jump to the [Halt] instruction at 08.

*)
Open Local Scope nat_scope.
Definition ctB :=
[
    (pair "myadd" 5);
    (pair "end" 8)
].
Definition programB : tRMCode :=
[
    (Const (V, 0) 2);
    (Const (V, 1) 3);
    (Invoke_static [(V, 0); (V, 1)] "myadd");
    (Move_result (V, 2));
    (Goto "end");
    (Add (V, 2) (P, 0) (P, 1));
    (Ret_val (V, 2));
    (Noop);
    (Halt)
].                   
Close Local Scope nat_scope.

Definition machine2 := loadRM programB ctB muRM.

Eval compute in (runRM 1 machine2).
Eval compute in (runRM 2 machine2).
Eval compute in (runRM 3 machine2).
Eval compute in (runRM 4 machine2).
Eval compute in (runRM 5 machine2).
Eval compute in (runRM 6 machine2).
Eval compute in (runRM 7 machine2).
Eval compute in (runRM 8 machine2).
Eval compute in (runRM 9 machine2).

(** The outcome of running this program is a value of 5 in register [v2] and the
value of [PC] set to 8.
<<
     = (([2; 3; 5; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0], [5; 0; 0; 0; 0; 0; 0]),
       [],
       [Const (V, 0%nat) 2; Const (V, 1%nat) 3;
       Invoke_static [(V, 0%nat); (V, 1%nat)] "myadd";
       Move_result (V, 2%nat); Goto "end";
       Add (V, 2%nat) (P, 0%nat) (P, 1%nat); Ret_val (V, 2%nat); Noop; Halt],
       8%nat, [], [("myadd", 5%nat); ("end", 8%nat)])
     : tRMState
>>

*)
(** ** Recursion
The next example program demonstrates the use of recursive function calls.
The register machine code for the factorial program is defined below. This 
program code is parameterized to accept an argument.

*)
Open Local Scope nat_scope.
Definition ctFact :=
[
    (pair "fact" 10);
    (pair "factret" 12);
    (pair "factrec" 13);
    (pair "end" 19)
].
Definition programFact (num : tRegVal) : tRMCode :=
[
    (Const (V, 2) num);
    (Invoke_static [(V, 2)] "fact");
    (Move_result (V, 0));
    (Goto "end");
    (Noop);
    (Noop);
    (Noop);
    (Noop);
    (Noop);
    (Noop);
    (If_gtz (P, 0) "factrec");
    (Const (V, 0) 1);
    (Ret_val (V, 0));
    (Const (V, 1) (-1));
    (Add (V, 0) (P, 0) (V, 1));
    (Invoke_static [(V, 0)] "fact");
    (Move_result (V, 0));
    (Mul (V, 0) (V, 0) (P, 0));
    (Goto "factret");
    (Halt)
].
Close Local Scope nat_scope.

Definition fact7 := loadRM (programFact 7%Z) ctFact muRM.
Eval compute in (runRM 100 fact7).

Definition fact10 := loadRM (programFact 10%Z) ctFact muRM.
Eval compute in (runRM 100 fact10).
Eval compute in (runRM 1000 fact10).

(** The outcome of running the factorial program for 10 leaves a value of 3628800 
in register [v0] and the value of [PC] set to 19.
<<
     = (([3628800; 0; 10; 0; 0; 0; 0], [0; 0; 0; 0; 0; 0; 0],
        [3628800; 0; 0; 0; 0; 0; 0]), [],
       [Const (V, 2%nat) 10; Invoke_static [(V, 2%nat)] "fact";
       Move_result (V, 0%nat); Goto "end"; Noop; Noop; Noop; Noop; Noop;
       Noop; If_gtz (P, 0%nat) "factrec"; Const (V, 0%nat) 1;
       Ret_val (V, 0%nat); Const (V, 1%nat) (-1);
       Add (V, 0%nat) (P, 0%nat) (V, 1%nat);
       Invoke_static [(V, 0%nat)] "fact"; Move_result (V, 0%nat);
       Mul (V, 0%nat) (V, 0%nat) (P, 0%nat); Goto "factret"; Halt], 19%nat,
       [],
       [("fact", 10%nat); ("factret", 12%nat); ("factrec", 13%nat);
       ("end", 19%nat)])
     : tRMState
>>

*)   
