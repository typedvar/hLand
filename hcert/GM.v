(** * Verified G-Machine Implementation
We implement the G-machine in Coq. The Graph process VM is a 
stack machine (PSVM) in which the operands of an instruction are pushed on a stack. 
When the instruction is processed the operands are popped from the stack and the
return value is pushed onto a stack.

We begin with the general behavior of this machine. The execution of the machine 
proceeds as follows:

%
\begin{itemize}
  \item Load an instruction from the code stream $\kappa$
  \item Process instruction based on rules defined in \S\ref{gm:transitions}
  \item Loop till $\kappa$ is empty
\end{itemize}
%
For simplicity of presentation the graph machine 
implementation handles the integer datatype. Support for floating point 
datatype can be achieved by adding floating point variants of each 
instruction. This extension however does not require changes to the core 
functionality of the system.

*)
(* begin hide *)
Require Import List.
Require Import Datatypes.
Require Import ZArith.
Require Import String.
Require Import Ascii.
Require Import SfLib.
Require Import VTypes.
Require Import VUtils.
Require Import VHeap.

Module Export GMi.
(* end hide *)
(** * Instruction Set 
We start by defining the instruction set for built-in arithmetic.

*)
Inductive tGMInstr : Type := 
    | Add : tGMInstr
    | Sub : tGMInstr
    | Mul : tGMInstr
    | Div : tGMInstr
(** The [Neg] instruction is unary and negates its argument.

*)
    | Neg : tGMInstr
(** The [Alloc] instruction allocates indirection nodes on the heap pointing to 
a distiguished %$\varnothing$% address.

*)
    | Alloc : nat -> tGMInstr
(** The [Cond] instruction evaluates its first argument and if the result is 
true, replaces $\kappa$ with the second argument, otherwise with the third
argument. Each of these arguments are list of instructions.
    
*)
    | Cond : list tGMInstr -> list tGMInstr -> tGMInstr
(** The following family of boolean binary instructions have the standard 
boolean semantics.
    
*)
    | Eq : tGMInstr
    | Ne : tGMInstr
    | Lt : tGMInstr
    | Le : tGMInstr
    | Gt : tGMInstr
    | Ge : tGMInstr
(** The [Eval] instruction is analogous to a function call. The current code 
segment and the elements of the stack, except the stack top, are removed 
and pushed onto the dump %$\delta$%. The code segment is populated with the
[Unwind] instruction.
    
*)
    | Eval : tGMInstr
(** The [MkAp] instruction pops off the top two entries from the stack and 
creates an application node [NAp] on the heap; the address of the created 
node is pushed onto the stack.

*)    
    | MkAp : tGMInstr
(** The [Pop] and [Push] instructions operate on the stack and each take a 
positive numeric argument [n]. [Pop] instruction removes [n] addresses from 
the stack, whereas [Push], retrieves the %$n^{th}$% address from the top of
the stack and pushes it onto the stack top.

*)    
    | Pop : nat -> tGMInstr
    | Push : nat -> tGMInstr
(** The [PushGlobal] instruction takes a string argument, representing a 
supercombinator name, looks up its address in the global section and pushes
it on the top of the stack. [PushInt] allocates a numeric node on the heap 
with the passed argument and pushes the address of the node onto the stack.

*)    
    | PushGlobal : tName -> tGMInstr
    | PushInt : Z -> tGMInstr
(**
The [Slide] instruction takes a positive numeric argument [n], and removes 
as many elements starting from below the top of the stack. Effectively it 
%\textit{slides}% the stack top down by [n] elements. The [Unwind] 
instruction finds the next [redex] on the G-machine spine.

*)
    | Slide : nat -> tGMInstr
    | Unwind : tGMInstr
(** The [Update] instruction modifies the stack top with a \textit{reference} 
to the element in the stack which the result of an evaluation.

*)
    | Update : nat -> tGMInstr
(** The [Pack] instruction introduces a data type.

*)
    | Pack : nat -> nat -> tGMInstr
    | Split : nat -> tGMInstr
(**
The [Print] instruction reads the object at the top of the stack, converts 
it to a string representation and appends it to the output string, 

*)
    | Print : tGMInstr.
(** This ends the instruction set for the G-machine. We now define the 
components of the G-machine. The code stream is a list of G-machine
instructions.

*)    
Definition tGMCode := list tGMInstr.
(** The G-machine heap %$\eta$%, stores objects of the type [tNode]. [tNode] 
objects represent the nodes in the logical graph, embodied as the heap 
in a G-machine state.

*)    
Inductive tNode : Type := 
    | NAp : tAddr -> tAddr -> tNode
    | NNum : Z -> tNode
    | NInd : tAddr -> tNode
    | NGlobal : nat -> tGMCode -> tNode
    | NConstr : nat -> list tAddr -> tNode.
(**
The stack is implemented as a list of addresses. The statistics section
%$\tau$%, represented by the type [tGMStats] stores the state number of a
G-machine state. The state number is a count of the number of steps taken 
by the machine since the initial configuration %\textit{I}% was loaded into 
it. The [tGMGlobals] section is an associative container of supercombinator
names to their addresses in the heap, and the dump is a list of G-code 
instructions and a stack pair. The output is repsented by an integer.

*)
Definition tGMHeap := tHeap tNode.
Definition tGMStack := list tAddr.
Definition tGMStats := nat.
Definition tGMGlobals := tAssocs tName tAddr.
Definition tGMDump := list (tGMCode * tGMStack).
Definition tGMOutput := Z.
(** * G-Machine State 
The G-machine state is inductively defined as the type [tGMState]. The elements
of the G-machine are read and modified using individual accessor functions. A 
7-tuple shorthand is employed for defining G-machine states.

*)
Inductive tGMState : Type := 
    | GMState : tGMOutput
             -> tGMCode
             -> tGMStack
             -> tGMDump
             -> tGMHeap
             -> tGMGlobals
             -> tGMStats
             -> tGMState.
(* begin hide *)
Notation "( output , code , stack , dump , heap , globals , stats )" := 
    (GMState output code stack dump heap globals stats).

Definition getOutput (m : tGMState) : tGMOutput :=
    match m with
    | (GMState output code stack dump heap globals stats) => output
    end.

Definition getCode (m : tGMState) : tGMCode :=
    match m with
    | (GMState output code stack dump heap globals stats) => code
    end.

Definition getStack (m : tGMState) : tGMStack :=
    match m with
    | (GMState output code stack dump heap globals stats) => stack
    end.

Definition getDump (m : tGMState) : tGMDump :=
    match m with
    | (GMState output code stack dump heap globals stats) => dump
    end.

Definition getHeap (m : tGMState) : tGMHeap :=
    match m with
    | (GMState output code stack dump heap globals stats) => heap
    end.

Definition getGlobals (m : tGMState) : tGMGlobals :=
    match m with
    | (GMState output code stack dump heap globals stats) => globals
    end.

Definition getStats (m : tGMState) : tGMStats :=
    match m with
    | (GMState output code stack dump heap globals stats) => stats
    end.

Definition putOutput (output : tGMOutput) (m : tGMState) : tGMState :=
    (output, getCode m, getStack m, getDump m, getHeap m, getGlobals m, getStats m).

Definition putCode (code : tGMCode) (m : tGMState) : tGMState :=
    (getOutput m, code, getStack m, getDump m, getHeap m, getGlobals m, getStats m).

Definition putStack (stack : tGMStack) (m : tGMState) : tGMState :=
    (getOutput m, getCode m, stack, getDump m, getHeap m, getGlobals m, getStats m).

Definition putDump (dump : tGMDump) (m : tGMState) : tGMState :=
    (getOutput m, getCode m, getStack m, dump, getHeap m, getGlobals m, getStats m).

Definition putHeap (heap : tGMHeap) (m : tGMState) : tGMState :=
    (getOutput m, getCode m, getStack m, getDump m, heap, getGlobals m, getStats m).

Definition putGlobals (globals : tGMGlobals) (m : tGMState) : tGMState :=
    (getOutput m, getCode m, getStack m, getDump m, getHeap m, globals, getStats m).

Definition putStats (stats : tGMStats) (m : tGMState) : tGMState :=
    (getOutput m, getCode m, getStack m, getDump m, getHeap m, getGlobals m, stats).

Definition incrSteps (m : tGMState) : tGMState :=
    putStats (S (getStats m)) m.

Import ListNotations.
(* end hide *)
(** The arithmetic and comparison operations are implemented 
below. These functions are used to define the machine's instruction set
implementation for arithmetic and unary operations.

*)
Open Scope Z_scope.

Definition opAdd (arg1 : Z) (arg2 : Z) : Z :=
    arg1 + arg2.

Definition opSub (arg1 : Z) (arg2 : Z) : Z :=
    arg1 - arg2.

Definition opMul (arg1 : Z) (arg2 : Z) : Z :=
    arg1 * arg2.

Definition opDiv (arg1 : Z) (arg2 : Z) : Z :=
    arg1 / arg2.

Definition opNeg (arg1 : Z) : Z :=
    0 - arg1.

Close Scope Z_scope.
(** Heap nodes are allocated using the [allocNodes] function. 
On successful allocation, the function returns the new heap and the 
newly allocated addresses; otherwise it returns a [None] value in the 
[option] monad.

*)
Fixpoint allocNodes (n : nat) (h : tGMHeap) : option (tGMHeap * tAddrs) :=
    match n with
    | O => Some (h, [])
    | S n' =>
        match allocNodes n' h with
        | Some (h', addrs) =>
            match  hAlloc h' (NInd NullAddr) with
            | Some (h'', a) => Some (h'', a::addrs)
            | _ => None
            end
        | _ => None
        end
    end.
(** * Instruction Set Implementation 
The instruction set for the G-machine is implemented in accordance with the 
semantic rules defined in %\S\ref{gm:transitions}%. Instead of returning a
value of type [tGMState], the implementing functions return an [option] monad 
containing a [GMState] or [None] to indicate error conditions.

*)
Definition alloc (n : nat) (m : tGMState) : option tGMState :=
    match allocNodes n (getHeap m) with
    | Some (heap', addrs) => 
        let
            stack' := app addrs (getStack m)
        in
            Some (putStack stack' (putHeap heap' m))
    | _ => None
    end.

Definition pushGlobal (f : string) (m : tGMState) : option tGMState :=
    match assocLookup (getGlobals m) f stringComp with
    | Some addr => Some (putStack (addr :: getStack m) m)
    | _ => None
    end.

Definition pushInt (n : Z) (m : tGMState) : option tGMState :=
    match hAlloc (getHeap m) (NNum n) with
    | Some (newHeap, addr) => Some (putHeap newHeap (putStack (addr :: getStack m) m))
    | _ => None
    end.

Definition push (n : nat) (m : tGMState) : option tGMState :=
    let
        stack := getStack m
    in
        let
            a := nth n stack 0%nat
        in
            Some (putStack (a::stack) m).

Definition mkAp (m : tGMState) : option tGMState :=
    match (getStack m) with
    | nil => None
    | a1::as' =>
        match as' with
        | nil => Some m
        | a2::as''=>
            match hAlloc (getHeap m) (NAp a1 a2) with
            | Some (modifiedHeap, addr) => 
                Some (putHeap 
                        modifiedHeap 
                            (putStack (addr::as'') m))
            | _ => None
            end
        end
    end.
    
Definition pop (n : nat) (m : tGMState) : option tGMState :=
    Some (putStack (drop n (getStack m)) m).

Definition update (n : nat) (m : tGMState) : option tGMState :=
    match (getStack m) with
    | nil      => None
    | a :: as' => 
        let
            heap' := hUpdate (getHeap m) (nth n as' 0%nat) (NInd a)
        in
            Some (putHeap heap' (putStack as' m))
    end.

Definition getArg (node : option tNode) : option tAddr :=
    match node with
    | Some (NAp a1 a2) => Some a2
    | _ => None
    end.

Definition rearrange (n : nat) (heap : tGMHeap) (stack : tGMStack) : option tGMStack :=
    match optMap (compose getArg (hLookup heap)) (tail stack) with
    | Some stack' => Some (app (take n stack') (drop n stack))
    | _ => None
    end.

(** ** Unwinding the spine 
As discussed in %\S\ref{gm:transitions}%, the [Unwind] function is complex.
This functionality is encoded in the following auxiliary
function [unwindHelper] which performs the major processing involved in 
unwinding the G-machine spine.

*)
Definition unwindHelper 
    (stack : tGMStack) 
    (heap : tGMHeap)
    (dump : tGMDump) 
    (m : tGMState) : option tGMState :=
    match stack with
    | nil => None
    | addr :: addrs => 
        match dump with
        | nil => None
        | (i, dstack) :: dump' =>
            match (hLookup heap addr) with
            | Some node =>
                match node with
                | NNum n               => 
                    Some (putCode 
                            i 
                            (putStack 
                                (addr :: dstack) 
                                (putDump dump' m)))
                | NAp a1 a2            => 
                    Some (putCode 
                            [Unwind] 
                            (putStack (a1 :: addr :: addrs) m))
                | NInd ind             => 
                    Some (putCode 
                            [Unwind] 
                            (putStack (ind :: addrs) m))
                | NConstr t addrs      => 
                    Some (putCode 
                            i 
                            (putStack 
                                (addr :: dstack) 
                                (putDump dump' m)))
                | NGlobal numArgs code => 
                    if (ble_nat numArgs (List.length addrs))
                    then
                        match rearrange numArgs heap (addr :: addrs) 
                        with
                        | Some newStack => 
                            Some (putCode code (putStack newStack m))
                        | _ => None
                        end
                    else
                        match head (rev stack) with
                        | Some a => 
                            Some (putCode 
                                    i 
                                    (putStack 
                                        (a :: dstack) 
                                        (putDump dump' m)))
                        | _         => None
                        end
                 end
            | _ => None
            end
        end
    end.

Definition unwind (m : tGMState) : option tGMState :=
    unwindHelper (getStack m) (getHeap m) (getDump m) m.

Definition slide (n : nat) (m : tGMState) : option tGMState :=
    match (getStack m) with
    | a :: as' => Some (putStack (a :: drop n as') m)
    | _        => None
    end.
(** ** Weak Head Normal Form
In a lazy implementation of %\textbf{H}% it important to ascertain to which
degree an expression is evaluated. We evaluate an expression till it 
reaches its weak-head normal form and no further.

*)
Definition eval2WHNF (m : tGMState) : option tGMState :=
    match getStack m with
    | addr :: addrs =>
        let
            frame := (getCode m, addrs)
        in
            Some 
                (putDump 
                    (frame :: getDump m) 
                    (putStack [addr] (putCode [Unwind] m)))
    | _ => None
    end.
(** ** Boxed Representation of Integers and Booleans 
Integers and booleans in the G-machine are represented as boxed in [NNum]
nodes. Thus, for arithmetic and boolean operations to function correctly, 
an %\textit{unboxing}% operation is required on the data. The result of
such an operation, when being written back to the heap requires a 
complementary %\textit{boxing}% operation.

*)
Definition boxInteger (v : Z) (m : tGMState) : option tGMState :=
    match hAlloc (getHeap m) (NNum v) with
    | Some (h, addr) => Some (putStack (addr :: getStack m) (putHeap h m))
    | _ => None
    end.

Definition unboxInteger (addr : tAddr) (m : tGMState) : option Z :=
    match (hLookup (getHeap m) addr) with
    | Some (NNum i) => Some i
    | _ => None
    end.

Definition boxBoolean (v : bool) (m : tGMState) : option tGMState :=
    let
        ctorTag := 
        match v with
        | true => S(S(O))
        | _ => S(O)
        end
    in
        match hAlloc (getHeap m) (NConstr ctorTag []) with
        | Some (h, addr) => Some (putStack 
                                    (addr :: getStack m) 
                                    (putHeap h m))
        | _ => None
        end.
(** We now define the general form of dyadic arithmetic and boolean operations.
[dyadic] takes a boxing function, an unboxing function, a binary operation 
and a G-machine state. It pops off the top two elements on the stack, 
unboxes them, and applies the binary operation on the unboxed 
representations of these elements. It then boxes the result and the address 
of the boxed representation is pushed onto the stack.

The [monadic] function behaves in a similar manner, except that the applied
operation is unary.

*)
Definition dyadic 
    {X Y : Type} 
    (box : Y -> tGMState -> option tGMState) 
    (unbox : tAddr -> tGMState -> option X)
    (op : X -> X -> Y)
    (m : tGMState) : option tGMState :=
    match getStack m with
    | a0 :: a1 :: as' =>
        match (unbox a0 m) with
        | Some v1 =>
            match (unbox a1 m) with
            | Some v2 => box (op v1 v2) (putStack as' m)
            | _ => None
            end
        | _ => None
        end
    | _ => None
    end.        

Definition monadic
    {X Y : Type} 
    (box : Y -> tGMState -> option tGMState) 
    (unbox : tAddr -> tGMState -> option X)
    (op : X -> Y)
    (m : tGMState) : option tGMState :=
    match getStack m with
    | a :: as' =>
        match (unbox a m) with
        | Some result => box (op result) (putStack as' m)
        | _ => None
        end
    | _ => None
    end.
(** The binary arithmetic, boolean and unary arithmetic operations are defined 
in terms of the generic [dyadic] and [monadic] functions.

*)    
Definition arithmetic2 (op : Z -> Z -> Z) (m : tGMState) : option tGMState :=
    dyadic boxInteger unboxInteger op m.

Definition arithmetic1 (op : Z -> Z) (m : tGMState) : option tGMState :=
    monadic boxInteger unboxInteger op m.

Definition comparison (op : Z -> Z -> bool) (m : tGMState) : option tGMState :=
    dyadic boxBoolean unboxInteger op m.

Definition pack (tag : nat ) (arity : nat) (m : tGMState) : option tGMState :=
    let
        stack := getStack m
    in
        match hAlloc (getHeap m) (NConstr tag (take arity stack)) with
        | Some (heap', addr) => Some (putHeap heap' (putStack (addr :: (drop arity stack)) m))
        | _ => None
        end.         

Definition splitter (n : nat) (m : tGMState) : option tGMState :=
    match getStack m with
    | a :: as' =>
        match hLookup (getHeap m) a with
        | Some (NConstr _ as'') => Some (putStack (app as'' as') m)
        | _ => None
        end
    | _ => None
    end.

Definition printer (m : tGMState) : option tGMState :=
    match getStack m with
    | addr :: _ => 
        match hLookup (getHeap m) addr with
        | Some (NNum val) => Some (putOutput val m)
        | _ => Some m
        end
    | _ => Some m
    end.

Definition getCodeStream (i1 i2 : tGMCode) (node : tNode) : tGMCode :=
    match node with
    | NConstr 2%nat _ => i1 (* NConstr 0 _ is false *)
    | _ => i2
    end.

Definition cond 
    (code1 code2 : tGMCode) 
    (m : tGMState) 
    : option tGMState :=
    match getStack m with
    | addr :: addrs =>
        match hLookup (getHeap m) addr with
        | Some node => 
            Some (putCode (app (getCodeStream code1 code2 node) (getCode m)) (putStack addrs m))
        | _ => None
        end
    | _ => None
    end.
(** ** The Dispatch Function 
The [dispatch] function takes as an input a G-machine instruction, a 
G-machine state and applies the appropriate instruction implementor function
to produce a resulting state.

*)
Definition dispatch (instruction : tGMInstr) (m : tGMState) : option tGMState :=
    match instruction with
    | PushGlobal f => pushGlobal f m
    | PushInt n => pushInt n m
    | MkAp => mkAp m
    | Push n => push n m
    | Update n => update n m
    | Pop n => pop n m
    | Unwind => unwind m
    | Slide n => slide n m
    | Alloc n => alloc n m
    | Eval => eval2WHNF m
    | Add => arithmetic2 opAdd m
    | Sub => arithmetic2 opSub m
    | Mul => arithmetic2 opMul m
    | Div => arithmetic2 opDiv m
    | Neg => arithmetic1 opNeg m
    | Cond i1 i2 => cond i1 i2 m
    | Eq => comparison beq_Z m
    | Ne => comparison bneq_Z m
    | Lt => comparison blt_Z m
    | Le => comparison ble_Z m
    | Gt => comparison bgt_Z m
    | Ge => comparison bge_Z m
    | Pack t arity => pack t arity m
    | Split n => splitter n m
    | Print => printer m
    end.
(** %\label{gm:nonterm}% *)
(** * Modeling Execution and Non-termination 
The naive idea of defining program execution as a recursive function fails since [Fixpoint] functions in Coq are
required to satisfy the property of structural recursion. This does not fit
with programs containing jumps and loops as these constructs might lead to the 
possibility of non-termination and hence a predefined number of steps required
by the structural recursion criterion cannot possibly model this behavior 
%\cite{Bertot:2008:ICC:1379918.1380269}%.
The problem lies in the fact that a program can run indefinitely if it 
contains infinite loops or mutual jumps and thus should be modeled as an 
%\textbf{infinite trace}%. The Coq co-inductive type is the right candidate 
for representing such traces.
We define the function [haltState] as a identity function such that given a 
G-machine state it returns an identical state. We also define the 
[errorState] function to intialize the output to a zero value.

*)
Definition haltState (m : tGMState) : tGMState :=
    m.

Definition errorState (m : tGMState) : tGMState :=
    putOutput 0%Z m.
(** The [stepFunc] take a G-machine state. If the code stream is empty, the 
[haltState] function is called. Otherwise, an instruction is removed 
from the code stream and the [dispatch] function is called
with the instruction as an argument. The number of steps executed by the 
G-machine is incremented for bookkeeping. The resulting state is returned.

*)
Definition stepFunc (m : tGMState) : tGMState :=
    let
        code := (getCode m)
    in
        match code with
        | nil => haltState m
        | instr::instrs => 
            match dispatch instr (putCode instrs (incrSteps m)) with
            | Some m' => m'
            | _ => errorState m
            end
        end.
(** We now define the [step] relation based on [stepFunc]. The
[stepRule] proposition defines that given any machine state [m], [stepFunc]
can be applied to [m]. The notation serves as shorthand for this 
proposition.

*)
(* begin hide *)
Reserved Notation "m1 '==>' m2" (at level 40).
(* end hide *)
(** printing ==> %$\Longrightarrow$% *)
Inductive step : tGMState -> tGMState -> Prop :=
    | stepRule : forall m, m ==> stepFunc m

where "m1 '==>' m2" := (step m1 m2).
(** We also define the [multistep] notation and a corresponding shorthand, 
as an application of [multi], defined in [SfLib], on the relation [step] 
indicating one or more application of the [step] relation.

*)
(* begin hide *)
Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).
(* end hide *)
(** * Determinism of G-machine 
The G machine is deterministic. We prove this by observing that [stepFunc] dispatches
the instruction found at the head of the code stream to the appropriate function, otherwise if the
code stream is empty the machine steps to the haltstate. Since the step function is deterministic,
the machine execution is deterministic too.
** Valid Program Trace
We now define the notion of a valid trace. 
For a machine [gm], the start state forms a valid program trace. 
Similarly, the start state and its next state forms a valid program trace. 
Finally, [forall] traces [t], 
and machine states [gm], [gm'], [gm''], if a machine in state [gm'] steps to [gm''] and [gm'] followed by 
trace [t] forms a valid trace, then [gm''] followed by the state [gm'] followed by the trace [t] is also
a valid trace.

*)
Inductive tProgramTrace2 : Type :=
    | start : tProgramTrace2
    | next  : tGMState -> tProgramTrace2 -> tProgramTrace2.

Inductive validTrace : tGMState -> tProgramTrace2 -> Prop :=
    | startValid : forall gm, (validTrace gm start)
    | nextValid  : forall gm, (validTrace gm (next gm start))
    | stepValid  : forall gm gm' gm'' t, 
        gm' ==> gm'' -> 
        validTrace gm (next gm' t) -> 
        validTrace gm (next gm'' (next gm' t)).
(** ** Stepping through a G-machine 
We now prove that the [step] relation is deterministic. We use the function
[deterministic] defined in [SfLib].

*)    
Theorem deterministicStep :
    (deterministic step).
Proof.
    intros gm gm1 gm2.
    induction gm as [O C STK D HP G STS].
    destruct C; intros.
    inversion H. inversion H0. reflexivity.
    inversion H. inversion H0. reflexivity.
Qed.
(** We define the [halted] property of the G-machine, when the instruction 
stream is empty.

*)
Definition halted (gm : tGMState) : Prop :=
    nil = getCode gm.
(** * Progress in G Machine 
The progress theorem states that given a G-machine state [gm], either it 
has halted, or it steps to another state [gm']. A G-machine halts when its 
instruction stream is empty.

*)
Theorem progressGM :
    forall gm, (halted gm) \/ (exists gm', (step gm gm')).
Proof.
    intros. destruct gm as [O C STK D HP G STS].
    destruct STK. right. eapply ex_intro. constructor.
    destruct STK; try right; eapply ex_intro; constructor.
Qed.

CoInductive tProgramTrace : Type :=
    | NextGM : tGMState -> tProgramTrace -> tProgramTrace.
(** The [generateTrace] function, given a G-machine state,
creates a program trace

*)
CoFixpoint generateTrace (m : tGMState) : tProgramTrace := 
    NextGM m (generateTrace (stepFunc m)).

Definition traceHead (x:tProgramTrace) := let (a,s) := x in a.

Definition traceTail (x:tProgramTrace) := let (a,s) := x in s.
(** Using [traceHead] and [traceTail] functions, we define the [nthTrace]
function that extracts the $n^{th}$ element from a trace and is analogous 
to the $n^{th}$ function that operate on lists. We declare that the program
has finished executing if the following condition holds true:
   
% 
For a program trace P, 
\begin{equation}
\forall i, \mathrm{if} \: \mathtt{nthTrace}(i, P) \: = \: \mathtt{nthTrace}((i+1), P) \: 
\mathrm{then} \: \mathtt{nthTrace}(i, P) \: = \: \mathtt{haltState}
\end{equation}
%

*)
Fixpoint nthTrace (n : nat) (trace: tProgramTrace) : tGMState :=
    match n with
    | O => traceHead trace
    | S n' => nthTrace n' (traceTail trace)
    end.

Definition run (m : tGMState) : tProgramTrace:=
    generateTrace m.
(** Finally to test the G-machine, we define the [runGM] function that 
takes a G-machine configuration and a step number [n] and generates a trace, 
and returns state of the machine after the %$n^{th}$% step.

*)    
Definition runGM 
    (numSteps : nat) 
    (machine : tGMState) : tGMState :=
    nthTrace numSteps (run machine).    

End GMi.
