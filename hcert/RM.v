(** * Verified Register VM Implementation
The R-machine is a subset of the Dalvik register VM. In register machines, the 
operands of an instruction are loaded into registers as opposed to stack 
machines where the operands are loaded on the stack.

In the following sections we present the R-machine formalization in Coq. 
*)

(** * Behavior
We begin with the general behavior of this machine. The execution of the machine 
proceeds as follows:

%
\begin{itemize}
  \item Load a instruction from the instruction sequence
  \item Process the instruction
  \item Loop till the \texttt{Halt} instruction is encountered
\end{itemize}
%
*)

(** We import the required modules. We limit the register 
    machine implementation to the integer datatype, and define it within the
    [Z_scope]. Support for floating point datatype could be achieved by adding 
    floating point variants of each instruction (as noted earlier).
*)

Require Import List.
Require Import Datatypes.
Require Import ZArith.
Require Import SfLib.

Require Import VUtils.
Require Import VTypes.
Require Import VHeap.

Require Import GM.

Module Export RMi.

(** * R-machine Components %\label{rm:components}%
    We now describe the types of registers in the R-machine.    
    There are three distinct types of registers; general 
    purpose registers denoted by [V], parameter registers, denoted by [P], and return value type 
    registers, denoted by [R]. Arguments to function calls are stored in the parameter 
    registers, whereas return value registers hold the value returned from a 
    function call. All other values are stored in general purpose registers.
    
    A register is uniquely identified by its type and index. The type [tReg]
    is thus a tuple of a register's type and its index.

    The registers available in an R-machine are stored as lists, [tRegs].
*)

Inductive tRegType : Type :=
   | V : tRegType
   | P : tRegType
   | R : tRegType.

Definition tRegIndex := nat.

Inductive tReg : Type := 
   | Reg : tRegType -> tRegIndex -> tReg.

Notation "( type , index )" := (Reg type index).

Definition getRegType (reg : tReg) : tRegType :=
    match reg with
    | (Reg type index) => type
    end.

Definition getRegIndex (reg : tReg) : tRegIndex :=
    match reg with
    | (Reg type index) => index
    end.

Definition tRegs := list tReg.

Definition tRegVal := Z.

Definition tRegVals := list tRegVal.

(** 
%
\bigskip
%
    The state of the registers in an R-machine is defined by the type 
    [tRegState], a triple containing the values in [V], [P] and [R] register 
    set. Generic getters and setters allow read and write access to these 
    registers.
*)

Inductive tRegState : Type :=
    | RegState : tRegVals-> tRegVals -> tRegVals -> tRegState.

Notation "( gpregs , paramregs , retregs )" := (RegState gpregs paramregs retregs).

Definition getRegVals (type: tRegType) (rs : tRegState) : tRegVals :=
    let 
        (gpregs, paramregs, retregs) := rs
    in
        match type with
        | V => gpregs
        | P => paramregs
        | R => retregs
        end. 

Definition putRegVals (type: tRegType) (newvals : tRegVals) (rs : tRegState) : tRegState :=
    let 
        (gpregs, paramregs, retregs) := rs
    in
        match type with
        | V => (RegState newvals paramregs retregs)
        | P => (RegState gpregs newvals retregs)
        | R => (RegState gpregs paramregs newvals)
        end.

Definition getGPRegVals (rs : tRegState) : tRegVals :=
    getRegVals V rs.

Definition getParamRegVals (rs : tRegState) : tRegVals :=
    getRegVals P rs.

Definition getRetRegVals (rs : tRegState) : tRegVals :=
    getRegVals R rs.

Definition putGPRegVals (newvals : tRegVals) (rs : tRegState) : tRegState :=
    putRegVals V newvals rs.

Definition putParamRegVals (newvals : tRegVals) (rs : tRegState) : tRegState :=
    putRegVals P newvals rs.

Definition putRetRegVals (newvals : tRegVals) (rs : tRegState) : tRegState :=
    putRegVals R newvals rs.

(** The program counter (PC) is of type [nat] and [tPCVal] represents the 
    corresponding datatype. 
*)

Definition tPCVal := nat.

(** Before executing a function call the current call state, or the activation 
    state, is pushed onto a stack denoted by the type [tCallStateStack]. When 
    the function call returns the saved state is restored. The saved state 
    consists of the registers, the values in registers, and the program counter 
    value.
    %\bigskip%
*)

Inductive tCallState : Type :=
    | CallState : tRegState -> tPCVal -> tCallState.

Definition tCallStateStack := list tCallState.

(** The [UndefinedCallState] function denotes an error condition and passed to 
    the [getHeadCallStateStack] function. If the [getHeadCallStateStack] function
    encounters a stack underflow it returns this value to the caller 
    indicating an exceptional program state
    %\bigskip%
*)
    
Definition UndefinedCallState : tCallState :=
    (CallState (RegState nil nil nil) 0%nat).

(** The code table maintains an associative table of string labels, [tLabel], 
    to their addresses in the code segment. The labels point to target 
    addresses of function calls, conditional and unconditional jumps. 
    %\bigskip%
*)

Definition tLabel := tName.

Definition tCodeTable := tAssocs tLabel tAddr.

(** * Instruction Set
The instruction set definition for the register machine is a subset of 
the Dalvik VM instruction set and is defined as the Coq inductive type [instr]
defined below. 
*)

Inductive tRMInstr : Type :=
    | Noop : tRMInstr
    | Move : tReg -> tReg -> tRMInstr 
    | Move_object : tReg -> tReg -> tRMInstr
    | Move_result : tReg -> tRMInstr
    | Move_object_result : tReg -> tRMInstr
    | Const : tReg -> Z -> tRMInstr
    | CmpEq : tReg -> tReg -> tReg -> tRMInstr
    | CmpNe : tReg -> tReg -> tReg -> tRMInstr
    | CmpLt : tReg -> tReg -> tReg -> tRMInstr
    | CmpLe : tReg -> tReg -> tReg -> tRMInstr
    | CmpGt : tReg -> tReg -> tReg -> tRMInstr
    | CmpGe : tReg -> tReg -> tReg -> tRMInstr
    | If_eq : tReg -> tReg -> tLabel -> tRMInstr
    | If_eqz : tReg -> tLabel -> tRMInstr
    | If_nez : tReg -> tLabel -> tRMInstr
    | If_ne : tReg -> tReg -> tLabel -> tRMInstr
    | If_lt : tReg -> tReg -> tLabel -> tRMInstr
    | If_le : tReg -> tReg -> tLabel -> tRMInstr
    | If_gt : tReg -> tReg -> tLabel -> tRMInstr
    | If_ge : tReg -> tReg -> tLabel -> tRMInstr
    | If_gtz : tReg -> tLabel -> tRMInstr
    | Neg : tReg -> tReg -> tRMInstr
    | Add : tReg -> tReg -> tReg -> tRMInstr
    | Sub : tReg -> tReg -> tReg -> tRMInstr
    | Mul : tReg -> tReg -> tReg -> tRMInstr
    | Div : tReg -> tReg -> tReg -> tRMInstr
    | Rem : tReg -> tReg -> tReg -> tRMInstr
    | And : tReg -> tReg -> tReg -> tRMInstr
    | Or : tReg -> tReg -> tReg -> tRMInstr
    | Xor : tReg -> tReg -> tReg -> tRMInstr
    | Invoke_static : tRegs -> tName -> tRMInstr
    | Ret_void : tRMInstr
    | Ret_val : tReg -> tRMInstr
    | Ret_object : tReg -> tRMInstr
    | Goto : tLabel -> tRMInstr
    | Array_length : tReg -> tReg -> tRMInstr
    | New_array : tReg -> tReg -> tReg -> tRMInstr
    | Aget : tReg -> tReg -> tReg -> tRMInstr
    | Aput : tReg -> tReg -> tReg -> tRMInstr
    | Halt : tRMInstr.

(** The G-code corresponding to a %\textbf{H}% program is translated into a list of R-machine 
instructions represented by [tRMCode].
*)

Definition tRMCode := list tRMInstr.

(** The register machine heap holds objects of Node type. The heap data is
    stored in the generic [tHeap] container.
*)

Definition tHeapData := tHeap GMi.tNode.

Definition tHPtr := nat.

Definition tSPtr := nat.

Record tRMHeap : Type := mkHeap
    { fHeapPointer : tHPtr;
      fHeapData : tHeapData }.

Definition putHeapPointer (newHP : tHPtr) (heap : tRMHeap) : tRMHeap :=
    match heap with
    | {| fHeapPointer := _;
    fHeapData := data |}
    => 
    {| fHeapPointer := newHP;
    fHeapData := data |}
    end.

Definition putHeapData (newData : tHeapData) (heap : tRMHeap) : tRMHeap :=
    match heap with
    | {| fHeapPointer := hp;
    fHeapData := _ |}
    => 
    {| fHeapPointer := hp;
    fHeapData := newData |}
    end.

Record tRMStack : Type := mkStack
    { fStackPointer : tSPtr;
      fStackData : tRegs }.

Definition putStackPointer (newSP : tSPtr) (stack : tRMStack) : tRMStack :=
    match stack with
    | {| fStackPointer := _;
    fStackData := pData |}
    => 
    {| fStackPointer := newSP;
    fStackData := pData |}
    end.

Definition putStackData (newData : tRegs) (stack : tRMStack) : tRMStack :=
    match stack with
    | {| fStackPointer := sp;
    fStackData := _ |}
    => 
    {| fStackPointer := sp;
    fStackData := newData |}
    end.

Definition initialStack : tRMStack := 
    mkStack 0 (nil).

(** * R-machine State
The register machine state is represented by an seven-tuple consisting of the
register states [rs], a list of instructions [ins], a program counter [pc], 
and a stack of states [ss]. A predefined register [retval] is set aside for 
the purpose of storing return values from functions. The [codeTable] acts as
the code segment for the machine. A heap and a stack is also part of the machine.
The type [tRMState] represents the machine state.
*)

Inductive tRMState : Type :=
    | RMState : tRegState
        -> tRMCode 
        -> tPCVal 
        -> tCallStateStack 
        -> tCodeTable
        -> tRMHeap
        -> tRMStack
        -> tRMState.
 
(** We introduce this shorthand notation to represent the machine tuple. 
*)

Notation "( rs , ins , pc , ss , ct , hp , stk )" := 
    (RMState rs ins pc ss ct hp stk).

(** To access the machine for a read or write operation, we define the accessor
    functions for each of the register machine fields. 
*)

Definition getRegState (m : tRMState ) : tRegState :=
    match m with
    | (RMState rs ins pc ss ct hp stk) => rs
    end.

Definition getCode (m : tRMState ) : tRMCode :=
    match m with
    | (RMState rs ins pc ss ct hp stk) => ins
    end.

Definition getPC (m : tRMState ) : tPCVal :=
    match m with
    | (RMState rs ins pc ss ct hp stk) => pc
    end.
    
Definition getCallSS (m : tRMState ) : tCallStateStack :=
    match m with
    | (RMState rs ins pc ss ct hp stk) => ss
    end.

Definition getCodeTable (m : tRMState ) : tCodeTable :=
    match m with
    | (RMState rs ins pc ss ct hp stk) => ct
    end.

Definition getHeap (m : tRMState ) : tRMHeap :=
    match m with
    | (RMState rs ins pc ss ct hp stk) => hp
    end.

Definition getStack (m : tRMState ) : tRMStack :=
    match m with
    | (RMState rs ins pc ss ct hp stk) => stk
    end.

Definition getCallStateRegState (cs : tCallState) : tRegState :=
    match cs with 
    | (CallState rs pc) => rs
    end.

Definition getCallStatePC (cs : tCallState) : tPCVal :=
    match cs with 
    | (CallState rs pc) => pc
    end.    

Definition getHeadCallStateStack (css : tCallStateStack) : tCallState :=
    hd UndefinedCallState css.

(** 
%
\bigskip
%
    The put functions writes back to the registers and updates the 
    components of the machine state. 
%
\bigskip
%
*)
    
Definition putRegState (rs : tRegState ) (m : tRMState ) : tRMState :=
    (rs, getCode m, getPC m, getCallSS m, getCodeTable m, getHeap m, getStack m).

Definition putCode (code : tRMCode ) (m : tRMState ) : tRMState :=
    (getRegState m, code, getPC m, getCallSS m, getCodeTable m, getHeap m, getStack m).

Definition putPC (pc : tPCVal) (m : tRMState) : tRMState :=
    (getRegState m, getCode m, pc, getCallSS m, getCodeTable m, getHeap m, getStack m).

Definition putCallSS (ss : tCallStateStack) (m : tRMState) : tRMState :=
    (getRegState m, getCode m, getPC m, ss, getCodeTable m, getHeap m, getStack m).

Definition putCodeTable (ct : tCodeTable) (m : tRMState) : tRMState :=
    (getRegState m, getCode m, getPC m, getCallSS m, ct, getHeap m, getStack m).

Definition putHeap (heap : tRMHeap) (m : tRMState) : tRMState :=
    (getRegState m, getCode m, getPC m, getCallSS m, getCodeTable m, heap, getStack m).

Definition putStack (stack : tRMStack) (m : tRMState) : tRMState :=
    (getRegState m, getCode m, getPC m, getCallSS m, getCodeTable m, getHeap m, stack).

Definition getHP (m : tRMState) : tHPtr :=
    (getHeap m).(fHeapPointer).

Definition putHP (newHP : tHPtr) (m : tRMState) : tRMState :=
    putHeap (putHeapPointer newHP (getHeap m)) m.

Definition getSP (m : tRMState) : tSPtr :=
    (getStack m).(fStackPointer).

Definition putSP (newSP : tSPtr) (m : tRMState) : tRMState :=
    putStack (putStackPointer newSP (getStack m)) m.

Definition incrementSP (m : tRMState) : tRMState :=
    putSP (S (getSP m)) m.

Definition decrementSP (m : tRMState) : option tRMState :=
    match getSP m with
    | S n => Some (putSP n m)
    | _ => None
    end.
 
(** The helper function [incrementPC] steps the program counter up by one.
    The auxiliary functions [getRegVal] and [putRegVal] read from and write to
    registers respectively.
*)

Definition incrementPC (m : tRMState) : tRMState :=
    (putPC (S (getPC m)) m).

(** To work with the call state stack, we define the [pushCallState] and [popCallState]
    functions.
*)

Definition pushCallState (cs : tCallState) (css : tCallStateStack) : tCallStateStack :=
    cs :: css.

Definition popCallState (css : tCallStateStack) : tCallStateStack :=
    match css with
    | nil => nil
    | h :: t => t
    end.

Definition getRegVal (r : tReg) (m : tRMState) : tRegVal :=
    nth (getRegIndex r) (getRegVals (getRegType r) (getRegState m)) 0%Z.

Definition putRegVal (r : tReg) (v : tRegVal) (m : tRMState) : tRMState :=
    let 
        regstate := getRegState m
    in
        let
            (type, index) := r
        in
            let
            regvals := getRegVals type regstate
            in
            putRegState 
                (putRegVals 
                    type 
                    (app 
                        (take index regvals) 
                        (v :: (drop (S index) regvals))
                    )
                    regstate
                ) 
                m.

Definition getLabelAddr (label : tLabel) (m : tRMState) : tAddr :=
    match assocLookup (getCodeTable m) label stringComp with
    | Some addr => addr
    | _ => NullAddr
    end.

(** A singular instance of the return value register is defined 
    by [iRetReg].
*)

Definition iRetReg : tReg :=
    (Reg R 0%nat).

Definition getRetVal (m : tRMState ) : tRegVal :=
    getRegVal iRetReg m.

Definition putRetVal (retval : tRegVal) (m : tRMState) : tRMState :=
    putRegVal iRetReg retval m.

(** * Instruction Set Implementation
    We now define the implementation of the register machine instruction set. 
    The [add] instruction stores the result of adding the contents of registers 
    [a] and [b] into the [dest] register.
*)

Open Scope Z_scope.

Definition add (dest a b: tReg) (m : tRMState) : tRMState :=
    putRegVal dest ((getRegVal a m) + (getRegVal b m)) m.

(** Similarly, the [mul] instruction multiplies the operands in registers [a] 
    and [b] and writes the result into the [dest] register. *)

Definition mul (dest a b: tReg) (m : tRMState) : tRMState :=
    putRegVal dest ((getRegVal a m) * (getRegVal b m)) m.

(** The move instruction copies the value from src to dest. 
*)

Definition move (dest src : tReg) (m : tRMState) : tRMState :=
    putRegVal dest (getRegVal src m) m.

(** The const instruction loads a value into the dest register. 
*)

Definition const (dest : tReg) (val : Z) (m : tRMState) : tRMState :=
    putRegVal dest val m.

(** The noop instruction increments the value of the program counter. 
*)

Definition noop (m : tRMState) : tRMState :=
    incrementPC m.

(** Once the machine returns from a function call, the call state is 
    restored by assigning the value of PC to the one pushed on the 
    call-state stack along with with the values of registers.
*)
    
Definition restoreCallState (m : tRMState) : tRMState :=
    let css :=
        getCallSS m
    in
        let cs := 
            getHeadCallStateStack css
        in
            putCallSS 
                (popCallState css)
                (putPC
                    (S (getCallStatePC cs))
                    (putRegState
                        (getCallStateRegState cs)
                        m
                    )
                ). 

(** Once the body of a method is executed, the control is transferred back to
    the calling code using the %\textbf{retType}% instruction. If the
    method returns a value to the caller, the [ret_val] instruction is executed,
    which puts the value in the argument register into the predefined [retval]
    register of the machine. Once control is transferred back to the calling
    code, the [move-result] instruction is used to load the value from the 
    [retval] register into an argument register %\cite{Dalvik}%.
*)

Definition ret_void (m : tRMState) : tRMState :=
    let cs := 
        getHeadCallStateStack (getCallSS m)
    in 
        restoreCallState m.

Definition ret_val (r : tReg) (m : tRMState) : tRMState :=
    let rval := 
        getRegVal r m
    in
        let cs := 
            getHeadCallStateStack (getCallSS m)
        in
            putRetVal rval (restoreCallState m).

Definition move_result (dest : tReg) (m : tRMState) : tRMState :=
    putRegVal dest (getRetVal m) m.

(** The [ifeq] implementation is defined as follows: 
    if the value of the register r1 matches r2 then the value of the program 
    counter (PC) is updated with the value given by label, otherwise the value 
    of PC is incremented. 

    Instead of an if-then-else construct, we model the equality check of the two 
    register values with a match on their difference. This seemingly 
    circumlocutary construct makes up for the lack of an integer equality 
    operator. 
*)

Definition ifeq (r1 r2: tReg) (label: tLabel) (m : tRMState) : tRMState :=
    match ((getRegVal r1 m) - (getRegVal r2 m)) with
    | 0 => putPC (getLabelAddr label m) m 
    | _ => incrementPC m
    end.

Definition ifgtz (r1 : tReg) (label: tLabel) (m : tRMState) : tRMState :=
    let
        val := (getRegVal r1 m)
    in
        match (val - 0) with
        | 0 => incrementPC m
        | _ => putPC (getLabelAddr label m) m
        end.

(** We implement the %\textbf{invoke-static}% instruction of the Dalvik VM. This
    instruction allows us to call any function that has been translated from
    %\textbf{H}% into the register machine bytecode. 
    
    Of the many variants in the %\textbf{Invoke}% family of instructions, 
    we choose [Invoke_static] for implementing the function calling mechanism
    in the R-machine. This is largely due to the fact that %\textbf{H}% is a 
    functional language and does not require object oriented semantics offered 
    by the other variants %\cite{Dalvik}%.
    
    The helper function [saveCallState] records the current activation frame in
    the [callStateStack] of the R-machine. 
*)

Definition saveCallState (m : tRMState) : tRMState :=
    putCallSS 
        (pushCallState 
            (CallState (getRegState m) (getPC m))
            (getCallSS m)
        ) 
        m.

Fixpoint loadRegVals (regs: tRegs) (m : tRMState) : tRegVals :=
    match regs with
    | nil => nil
    | r :: rs => (getRegVal r m) :: loadRegVals rs m
    end.


Definition invoke_static (regs: tRegs) (label: tLabel) (m: tRMState) : tRMState :=
    let
        m' := (saveCallState m)
    in
        (putPC 
            (getLabelAddr label m)
            (putRegState
                (putParamRegVals 
                    (loadRegVals regs m')
                    (getRegState m')
                )
                m'
            )
        ).
        
Definition array_length (dest src: tReg) (m : tRMState) : tRMState :=
m.

Definition new_array (dest numels type: tReg) (m : tRMState) : tRMState :=
m.

Definition aget (dest a b: tReg) (m : tRMState) : tRMState :=
m.

Definition aput (dest a b: tReg) (m : tRMState) : tRMState :=
m.

Definition goto (label : tLabel) (m : tRMState) : tRMState :=
    putPC (getLabelAddr label m) m.        

(** Once we have defined the implementation of the instructions, we are left 
    with defining the state transition mechanics of the register machine itself. 
    The operation of a register machine can be described as a 
    fetch-decode-execute-loop cycle.
    
    We begin with the [fetch] operation. As the name suggests, [fetch] gets the 
    next instruction that is to be executed. It does so by taking a machine 
    state, retrieving the instruction at the address pointed by the value in PC 
    and returning it. 
*)

Definition fetch (m : tRMState) : tRMInstr :=
    nth (getPC m) (getCode m) Noop.

(** The [decode] step in this machine is not required, and we proceed to define the 
    [execute] step. The [execute] step takes an instruction, an input machine state, 
    calls the appropriate instruction handler and returns the resulting machine 
    state after the instruction has been processed.
*)

Definition execute (i : tRMInstr) (m : tRMState) : tRMState :=
    match i with
    | Const r v                => incrementPC (const r v m)
    | Move r1 r2               => incrementPC (move r1 r2 m)
    | Move_result r1           => incrementPC (move_result r1 m)
    | Add a b dest             => incrementPC (add a b dest m)
    | Mul a b dest             => incrementPC (mul a b dest m)
    | Noop                     => noop m
    | If_eq r1 r2 label        => ifeq r1 r2 label m
    | If_gtz r1 label          => ifgtz r1 label m
    | Invoke_static regs label => invoke_static regs label m
    | Ret_void                 => ret_void m
    | Ret_val r                => ret_val r m
    | Array_length r1 r2       => array_length r1 r2 m
    | New_array r1 r2 r3       => new_array r1 r2 r3 m
    | Aget r1 r2 r3            => aget r1 r2 r3 m
    | Aput r1 r2 r3            => aput r1 r2 r3 m    
    | Goto label               => goto label m
    | _                        => m
    end.

(** * Program Termination State
    We model the termination state of the machine by the special marker 
    [haltState]. In this state we preserve the values within the
    registers and wipe out all other state data.
*)

Definition haltState (m : tRMState) : tRMState :=
    (getRegState m, getCode m, getPC m, (nil), getCodeTable m, getHeap m, initialStack).

(** During a single step, we fetch the next instruction from the instruction
    list. If we encounter the [halt] instruction, we return the 
    [haltState], otherwise, we execute the instruction.
*)

Definition stepFunc (m : tRMState) : tRMState :=
    match fetch(m) with
    | Halt => haltState m
    | i => execute i m
    end.

Reserved Notation "m1 '==>' m2" (at level 40).

Inductive step : tRMState -> tRMState -> Prop :=
    | stepRule : forall m, m ==> stepFunc m

where "m1 '==>' m2" := (step m1 m2).

(** We also define the [multistep] notation and a corresponding shorthand, 
    as an application of [multi], defined in [SfLib], on the relation [step] 
    indicating one or more application of the [step] relation.
*)

Theorem deterministicStep :
    (deterministic step).
Proof.
    intros rm rm1 rm2.
    induction rm as [RegState CodeStream PC CallDump SymTable Heap Stack].
    destruct CodeStream; intros.
    inversion H. inversion H0. reflexivity.
    inversion H. inversion H0. reflexivity.
Qed.

(** * Progress in R Machine 
    The progress theorem states that given a R-machine state [rm], either it 
    has halted, or it steps to another state [rm']. A R-machine halts when it 
    encounters the [HALT] instruction.
*)

Definition halted (rm : tRMState) : Prop :=
    Halt = fetch rm.
    
Theorem progressRM :
    forall rm, (halted rm) \/ (exists rm', (step rm rm')).
Proof.
    intros. destruct rm as [RegState CodeStream PC CallDump SymTable Heap Stack].
    destruct CodeStream. right. eapply ex_intro. constructor.
    destruct CodeStream; try right; eapply ex_intro; constructor.
Qed.

(** * Modeling Program Execution and Non-termination
    As explained in %\S\ref{gm:nonterm}%, to model realistic programs we take into 
    account the non-terminating nature of programs and represent such behavior 
    through Coq co-inductive types. For the R-machine we define such a type 
    [tRMProgramTrace]. 
*)

CoInductive tRMProgramTrace : Type :=
    | NextRM : tRMState -> tRMProgramTrace -> tRMProgramTrace.

(** We now define a [CoFixpoint] function which generates an infinite trace of run 
    states given an initial machine state.
*)

CoFixpoint generateTrace (rm : tRMState) : tRMProgramTrace := NextRM rm (generateTrace (stepFunc rm)).

(** The [run] function that starts the machine and uses the lazy [generateTrace] 
    to create a program trace.
*)

Definition run (m : tRMState) : tRMProgramTrace:=
    generateTrace m.

(** In order to do meaningful operations on the trace, we define [traceHead] and 
    [traceTail] functions on the program trace. These are analogous to the
    well known head and tail functions that operate on lists.
*)

Definition traceHead (x:tRMProgramTrace) := let (a,s) := x in a.

Definition traceTail (x:tRMProgramTrace) := let (a,s) := x in s.

(** Using [traceHead] and [traceTail] functions, we define the [nthTrace]
    function that extracts the $n^{th}$ element from a trace and is analogous 
    to the $n^{th}$ function that operate on lists. We declare that the program
    has finished executing if equation %\ref{rm:termstate}% is satisfied.
*)

Fixpoint nthTrace (n : nat) (trace: tRMProgramTrace) : tRMState :=
    match n with
    | O => traceHead trace
    | S n' => nthTrace n' (traceTail trace)
    end.

Close Scope Z_scope.

(** The [loadMachine] helper function sets up an R-machine configuration with the
    input program.
*)
     
Definition loadRM 
    (code : tRMCode) 
    (codeTable : tCodeTable) 
    (machine : tRMState) : tRMState :=
    putCodeTable codeTable (putCode code machine).
    
(** The [runRM] function executes an R-machine for a defined number of 
    steps.
*)
     
Definition runRM 
    (numSteps : nat) 
    (machine : tRMState) : tRMState :=
    nthTrace numSteps (run machine).    

End RMi.

(** With this we complete the definition of the register machine. In the 
    following section we run the machine through a set of sample programs. 
*)
