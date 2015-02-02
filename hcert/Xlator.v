(** * Verified Translator 
    The G-code to R-code translator is written in Coq. As the translator accesses
    the internal structures of both the G-machine and R-machine, we reuse these
    structures and definitions to implement the translator. We also reuse the
    parameterized heap defined in the [VHeap] modules to represent the heaps used in
    the G-machine and R-machine. In the case of the G-machine the heap structure
    contained nodes of types [tNode], whereas in the case of the R-machine, the
    nodes are of type [tRMNodes].
*)


Require Import List.
Require Import ZArith.
Require Import String.
Require Import Ascii.
Require Import Coq.ZArith.Znat.

Require Import VTypes.
Require Import VUtils.
Require Import VHeap.
Require Import GM.
Require Import RM.

Module Export XlatorImpl.

(** The code-table is defined as an associative container of labels to addresses
    in the R-machine heap. In the present implementation we use an associative
    container that employs a linear lookup technique yielding a running time 
    of %$O(n)$% for querying a key. This can be optimized by replacing the 
    internal implementation of the associative container [tAssocs] with a hash 
    table.
    %\bigskip%
*)

Definition tCodeTable := tAssocs tName tAddr.

(** As presented in section %\S\ref{tx:txapproach}%, the [tCodeSegmentZone] indicates 
    the zone to which the translator appends the generated code in the 
    code-segment of %$\rho$%.
    %\bigskip%
*)

Inductive tCodeSegmentZone : Type :=
    | Prefix : tCodeSegmentZone
    | Suffix : tCodeSegmentZone.

(** * Translator State
    The translator is modeled as an 8-tuple Coq record. Translating the stack-based
    G-code instuctions to R-code involves register allocation. As defined in 
    section %\S\ref{rm:components}%, for each type of register in the R-machine,
    the translator uses a simple register allocation strategy of incrementing 
    the last allocated index while allocating a new register. The fields [fVC], 
    [fPC] and [fRC] are used for bookkeeping the value of the last allocated 
    index for each register type. 
    
    [fCode] represents the code-segment, a list of R-code instructions,
    and [fCodeTable] represents the code-table of an R-machine. The types 
    [tRMCode] [tRegs] and [tCodeTable] are defined in section 
    %\S\ref{rm:components}%. Once translation completes, these fields are 
    loaded into the R-machine configuration.
    
    [fStack] is a list of R-code instructions manipulated as a stack. During the 
    translation process, the intermediate R-code generated as a result of 
    translating the [PushInt] G-code instruction is pushed onto the [fStack]. 
    The [fRegStack] is an intermediate structure and is used during register 
    allocation. The last field [fGM] is the G-machine configuration being 
    translated.
    %\bigskip%
*)

Record tXlator : Type := mkXlator
    { fVC : nat;
      fPC : nat;
      fRC : nat;
      fCode : tRMCode;
      fStack : tRMCode;
      fRegStack : tRegs;
      fCodeTable : tCodeTable;
      fGM : tGMState }.

(** The [put]* and [get]* functions define the accessors for the translator.
    %\bigskip%
*)

Definition putVC (newVC : nat) (xlator : tXlator) : tXlator :=
    match xlator with
    | {| fVC := _;
         fPC := pC;
         fRC := rC;
         fCode := code;
         fStack := stack;
         fRegStack := rStack;
         fCodeTable := codeTable;
         fGM := gm |} 
      => 
      {| fVC := newVC;
         fPC := pC;
         fRC := rC;
         fCode := code;
         fStack := stack;
         fRegStack := rStack;
         fCodeTable := codeTable;
         fGM := gm |}
    end.

Definition putPC (newPC : nat) (xlator : tXlator) : tXlator :=
    match xlator with
    | {| fVC := vC;
         fPC := _;
         fRC := rC;
         fCode := code;
         fStack := stack;
         fRegStack := rStack;
         fCodeTable := codeTable;
         fGM := gm |} 
      => 
      {| fVC := vC;
         fPC := newPC;
         fRC := rC;
         fCode := code;
         fStack := stack;
         fRegStack := rStack;
         fCodeTable := codeTable;
         fGM := gm |}
    end.

Definition putRC (newRC : nat) (xlator : tXlator) : tXlator :=
    match xlator with
    | {| fVC := vC;
         fPC := pC;
         fRC := _;
         fCode := code;
         fStack := stack;
         fRegStack := rStack;
         fCodeTable := codeTable;
         fGM := gm |} 
    => 
      {| fVC := vC;
         fPC := pC;
         fRC := newRC;
         fCode := code;
         fStack := stack;
         fRegStack := rStack;
         fCodeTable := codeTable;
         fGM := gm |}
    end.

Definition putCode (code : tRMCode) (xlator : tXlator) : tXlator :=
    match xlator with
    | {| fVC := vC;
         fPC := pC;
         fRC := rC;
         fCode := _;
         fStack := stack;
         fRegStack := rStack;
         fCodeTable := codeTable;
         fGM := gm |} 
    => 
      {| fVC := vC;
         fPC := pC;
         fRC := rC;
         fCode := code;
         fStack := stack;
         fRegStack := rStack;
         fCodeTable := codeTable;
         fGM := gm |}
    end.

Definition putStack (stack : tRMCode) (xlator : tXlator) : tXlator :=
    match xlator with
    | {| fVC := vC;
         fPC := pC;
         fRC := rC;
         fCode := code;
         fStack := _;
         fRegStack := rStack;
         fCodeTable := codeTable;
         fGM := gm |} 
    => 
      {| fVC := vC;
         fPC := pC;
         fRC := rC;
         fCode := code;
         fStack := stack;
         fRegStack := rStack;
         fCodeTable := codeTable;
         fGM := gm |}
    end.

Definition putRegStack (rStack : tRegs) (xlator : tXlator) : tXlator :=
    match xlator with
    | {| fVC := vC;
         fPC := pC;
         fRC := rC;
         fCode := code;
         fStack := stack;
         fRegStack := _;
         fCodeTable := codeTable;
         fGM := gm |} 
    => 
      {| fVC := vC;
         fPC := pC;
         fRC := rC;
         fCode := code;
         fStack := stack;
         fRegStack := rStack;
         fCodeTable := codeTable;
         fGM := gm |}
    end.

Definition putCodeTable (codeTable : tCodeTable) (xlator : tXlator) : tXlator :=
    match xlator with
    | {| fVC := vC;
         fPC := pC;
         fRC := rC;
         fCode := code;
         fStack := stack;
         fRegStack := rStack;
         fCodeTable := _;
         fGM := gm |} 
    => 
      {| fVC := vC;
         fPC := pC;
         fRC := rC;
         fCode := code;
         fStack := stack;
         fRegStack := rStack;
         fCodeTable := codeTable;
         fGM := gm |}
    end.

Definition putGM (gm : tGMState) (xlator : tXlator) : tXlator :=
    match xlator with
    | {| fVC := vC;
         fPC := pC;
         fRC := rC;
         fCode := code;
         fStack := stack;
         fRegStack := rStack;
         fCodeTable := codeTable;
         fGM := _ |} 
    => 
      {| fVC := vC;
         fPC := pC;
         fRC := rC;
         fCode := code;
         fStack := stack;
         fRegStack := rStack;
         fCodeTable := codeTable;
         fGM := gm |}
    end.

(** * Translator Implementation
    In this section we formalize the translation mechanism. We start by 
    defining the helper functions required by the translator.

    The [addCode] helper function adds a list of R-code instructions to the 
    code-segment. The zone where the code is inserted is determined by the 
    [zone] parameter. The [addInstr] function prefixes a single instruction to 
    the code-segment. [pushRMInstr] and [popRMInstr] manipulate the stack and 
    implement the push and pop operations. The [pushReg] and [popReg] functions 
    manipulate the register stack.
    %\bigskip%
*)

Definition addCode (code : tRMCode) (zone : tCodeSegmentZone) (xlator : tXlator) : tXlator :=
    match zone with
    | Prefix => putCode (app code xlator.(fCode)) xlator
    | Suffix => putCode (app xlator.(fCode) code) xlator
    end.

Definition addInstr (instr : tRMInstr) (xlator : tXlator) : tXlator :=
    putCode (instr :: xlator.(fCode)) xlator.
    
Definition pushRMInstr (instr : tRMInstr) (xlator : tXlator) : tXlator :=
    putStack (instr :: xlator.(fStack)) xlator.
    
Definition popRMInstr (xlator : tXlator) : option (tRMInstr * tXlator) :=
    match xlator.(fStack) with
    | instr :: instrs => Some (pair instr (putStack instrs xlator))
    | _ => None
    end.    

Definition pushReg (reg : tReg) (xlator : tXlator) : tXlator :=
    putRegStack (reg :: xlator.(fRegStack)) xlator.
    
Definition popReg (xlator : tXlator) : option (tReg * tXlator) :=
    match xlator.(fRegStack) with
    | reg :: regs => Some (pair reg (putRegStack regs xlator))
    | _ => None
    end.

(** The [allocateReg] function allocates a register of a given type. It does so 
    by incrementing the count of the last allocated register of that type. When 
    a register of a particular type is required by the translator, it reads the 
    value from appropriate field.
    %\bigskip%
*)

Definition allocateReg (regType : tRegType) (xlator : tXlator) : tXlator :=
    match regType with
    | V => putVC (S xlator.(fVC)) xlator
    | P => putPC (S xlator.(fPC)) xlator
    | R => putRC (S xlator.(fRC)) xlator
    end.

(** The [allocateRegAndLoadValue] helper function allocates a
    register and loads a value into it. The load instruction is
    recorded in the [fCodeStack], and the allocated register
    is recorded in the [fRegStack].
    
    The [allocateRegsAndLoadValues] helper function calls the
    [allocateRegAndLoadValue] function recursively to load a 
    set of values.
    %\bigskip%
*)

Definition allocateRegAndLoadValue
    (xlator : tXlator)
    (value : tRegVal)
    : tXlator :=
        let 
            reg := Reg V xlator.(fVC)
        in
            let
                instr := (Const reg value)
            in
                allocateReg V (pushReg reg (pushRMInstr instr xlator)).
    
Fixpoint allocateRegsAndLoadValues 
    (xlator : tXlator)
    (values : tRegVals)
    : tXlator :=
    match values with
    | nil         => xlator
    | v :: vs => allocateRegsAndLoadValues (allocateRegAndLoadValue xlator v) vs
    end.

(** The [addCodeEntry] function take a string label, indicating the name of a 
    supercombinator or a label indicating the address of an unconditional jump 
    and an address. It creates a pair of these two elements and adds this to the
    code-table.
    %\bigskip%
*)

Definition addCodeEntry 
    (name : tName) 
    (addr : tAddr) 
    (xlator : tXlator) : tXlator :=
    putCodeTable ((pair name addr)::xlator.(fCodeTable)) xlator. 



Open Local Scope nat_scope.

(** [getSCStream] takes as its input the name of a supercombinator and retrieves
    the G-code instruction sequence associated with the body of the 
    supercombinator by looking up the address of the supercombinator in the 
    globals section of the G-machine and then using that address to fetch the 
    instruction stream G-machine heap. The return type is the option monad, 
    which contains the [NGlobal] node in case of a successful lookup. If the
    lookup fails or if the node associated with the address is not a 
    supercombinator the [None] value is returned indicating an error condition.
    
    The [getNumArgs] function takes a supercombinator name and returns the 
    number of arguments that the supercombinator accepts. This is useful for 
    parameter register allocation during translating function applications.
    %\bigskip%
*)

Definition getSCStream (name : tName) (xlator : tXlator) : option GMi.tNode :=
    match assocLookup (GMi.getGlobals xlator.(fGM)) name stringComp with
    | Some addr =>
        match (hLookup (GMi.getHeap xlator.(fGM)) addr) with
        | Some node =>
            match node with
            | NGlobal numArgs innerCode => Some node
            | _ => None
            end
        | _ => None
        end
    | _ => None
    end.

Definition getNumArgs (name : tName) (xlator : tXlator) : nat :=
    match getSCStream name xlator with
    | Some (NGlobal numArgs innerCode) => numArgs
    | _ => 0
    end.

(** The [loadInstr] helper function compiles a list of instructions from 
    the intermediate instruction stack of the translator. It takes as an 
    argument the number of instructions to load. Once instructions are
    loaded into the list, those entries are popped off the stack. The 
    [loadRegs] function is similar, except that it works on registers 
    instead of instructions. The [getCodeAddress] function returns the 
    address of the input label by looking up the code-table.
    %\bigskip%
*)
    
Definition loadInstr (numArgs : nat) (xlator : tXlator) : (tRMCode * tXlator) :=
     let
         rmCode := take numArgs xlator.(fStack)
     in
         (pair rmCode (putStack (drop numArgs xlator.(fStack)) xlator)).

Definition loadRegs (numArgs : nat) (xlator : tXlator) : (tRegs * tXlator) :=
     let
         regs := take numArgs xlator.(fRegStack)
     in
         (pair regs (putRegStack (drop numArgs xlator.(fRegStack)) xlator)).

Definition getCodeAddress (name : tName) (xlator : tXlator) : tAddr :=
    match assocLookup xlator.(fCodeTable) name stringComp with
    | Some addr => addr
    | _ => NullAddr
    end.

Import ListNotations.

(** ** Translating Function Application 
    The [Invoke_static] instruction of Dalvik is used to generate a 
    function call in the R-machine. The number of arguments, [numArgs], required 
    by the supercombinator is looked up using the [getNumArgs] helper function. 
    [numArgs] registers are streamed from the register stack using the [loadRegs]
    helper function into the [regs] variable. In a similar manner, the 
    instructions for populating the parameter registers required by the function 
    call are streamed from the translator's [fStack] field using the helper 
    function [loadInstr] into the [instrs] variable. Finally, the instructions 
    for the function call are assembled in the following order:
    
    - instructions ([instrs]) required to populate the function call parameter 
      registers are laid out
    - the function call instruction with appropriate registers ([regs]) is laid 
      out
    - instruction required to move the result of the function call, using 
      [Move_result], is laid out
    
    As [Move_result] requires a register to store the return value of the 
    function call, a new value register is allocated through the [allocateReg] 
    call, resulting in a modified translator state. The laid out instructions 
    along with the modified translator state are returned back to the caller 
    as a pair of type [(tRMCode * tXlator)].
    %\bigskip%
*)

Definition generateCall 
    (numArgs : nat) 
    (name : tName) 
    (xlator : tXlator) 
    : (tRMCode * tXlator):=
    let
        (regs, xlator') := loadRegs numArgs xlator
    in
        let
            (instrs, xlator'') := (loadInstr numArgs xlator')
        in
            (pair 
                (app instrs [Invoke_static regs name; Move_result (Reg V xlator.(fVC))]) 
                (allocateReg V xlator'')).

(** ** Translating Dyadic and Monadic Operations
    The [generateDyadicCode] function is used to translate binary arithmetic and 
    logical G-code instructions in R-code. This generic function allocates a 
    register for holding the return value and used the [loadRegs] function to 
    retrieve the list of registers containing the operands. The R-code 
    instruction for the operator is laid out based on a match on the [op] 
    parameter followed by the second and the first parameter registers. The 
    instructions are then laid out at the prescribed [zone] in the translator's 
    code-segment. The [generateMonadicCode] function is similar, except that it
    requires a single operand, and hence uses a single register.    
    %\bigskip%
*)

Definition generateDyadicCode 
    (op : tGMInstr) 
    (zone : tCodeSegmentZone) 
    (xlator : tXlator) 
    : tXlator :=
    let 
        vReg := Reg V xlator.(fVC)
    in
        let
            (regs, xlator') := loadRegs 2 (allocateReg V xlator)
        in
            let
                code := 
                match op with
                | GMi.Add => (Add vReg (nth 1 regs (R, 0)) (nth 0 regs (R, 0)))::nil
                | GMi.Sub => (Sub vReg (nth 1 regs (R, 0)) (nth 0 regs (R, 0)))::nil
                | GMi.Mul => (Mul vReg (nth 1 regs (R, 0)) (nth 0 regs (R, 0)))::nil
                | GMi.Div => (Div vReg (nth 1 regs (R, 0)) (nth 0 regs (R, 0)))::nil
                | GMi.Eq => (CmpEq vReg (nth 1 regs (R, 0)) (nth 0 regs (R, 0)))::nil
                | GMi.Ne => (CmpNe vReg (nth 1 regs (R, 0)) (nth 0 regs (R, 0)))::nil
                | GMi.Lt => (CmpLt vReg (nth 1 regs (R, 0)) (nth 0 regs (R, 0)))::nil
                | GMi.Le => (CmpLe vReg (nth 1 regs (R, 0)) (nth 0 regs (R, 0)))::nil
                | GMi.Gt => (CmpGt vReg (nth 1 regs (R, 0)) (nth 0 regs (R, 0)))::nil
                | GMi.Ge => (CmpGe vReg (nth 1 regs (R, 0)) (nth 0 regs (R, 0)))::nil
                | _ => nil
                end
            in
                addCode code zone xlator'.

(**
    %\bigskip%
*)

Definition generateMonadicCode 
    (op : tGMInstr) 
    (zone : tCodeSegmentZone) 
    (xlator : tXlator) 
    : tXlator :=
    let 
        vReg := Reg V xlator.(fVC)
    in
        let
            (regs, xlator') := loadRegs 1 (allocateReg V xlator)
        in
            let
                code := 
                match op with
                | GMi.Neg=> (Neg vReg (nth 0 regs (R, 0)))::nil
                | _ => nil
                end
            in
                addCode code zone xlator'.

(** ** In-Built Functions
    As the G-code program that is being translated is designed to run on the 
    G-machine, it contains several graph and stack manipulation related 
    instructions, such as [Unwind], [Update], [Slide] to mention a few. 
    On the other hand a register machine does not have graph or stack 
    manipulation instructions in its set. To bridge this gap, a library of 
    in-built functions is defined and loaded as a part of the initial 
    configuration of every R-machine instance. The translator on encountering 
    such G-code instructions generates an appropriate [Invoke-static] call to 
    the corresponding in-built function. This is implemented in the 
    [generateBuiltInCall] function defined below.
    %\bigskip%
*)

Definition generateBuiltInCall
    (inbuilt : tName)
    (args : tRegVals)
    (zone : tCodeSegmentZone)
    (xlator : tXlator)
    : tXlator :=
    let 
        xlator' := allocateRegsAndLoadValues xlator args
    in
        let 
            (code, xlator'') := generateCall (List.length args) inbuilt xlator'
        in
            addCode code zone xlator''.
        
(*        
| GMi.Alloc num => addCode [Invoke_static [reg0] "__allocNode"; Move_result reg1] zone xlator 
| GMi.Unwind => addCode [Invoke_static [] "__unwind"] zone xlator
| GMi.Pop num => addCode [Invoke_static [] "__pop"] zone xlator
| GMi.Update num => addCode [Invoke_static [reg0] "__update"] zone xlator
| GMi.Slide num => addCode [Invoke_static [reg0] "__slide"] zone xlator
| GMi.MkAp => addCode [Invoke_static [] "__mkAp"] zone xlator
| GMi.Eval => addCode [Invoke_static [] "__eval"] zone xlator
| GMi.Pack tag arity => xlator
| GMi.Split num => addCode [Invoke_static [reg0] "__split"] zone xlator
| GMi.Print => addCode [Invoke_static [] "__print"] zone xlator
| GMi.Cond trueBranch falseBranch => addCode [Invoke_static [reg0; reg1] "__cond"] zone xlator
*)

(** ** Translator Dispatch Function 
    The recursive function [translateCode] performs the heavy lifting during a 
    translator run. It accepts a translator state, a G-code stream and the zone
    where the translated R-code instruction is appended to in the code-segment.
    The [{struct code}] directive tells Coq that [code] is the reducing argument
    to this [Fixpoint] definition.
    
    Each instruction from the code stream is examined, and dispatched for 
    translation based on the match. The [PushGlobal] instruction is translated 
    to a function call, the [PushInt] instruction results in a register
    allocation, followed by pushing a [Const] instruction in [fStack] and the 
    allocated register in the [fRegStack] fields of the translator. The [Push]
    instruction results in a parameter register allocation which is subsequently
    pushed onto the register stack.
    
    For all dyadic and monadic instructions, the appropriate helper function is 
    invoked to generate the required code. The [generateBuiltInCall] function
    translates the G-machine graph and stack manipulation instructions to 
    reserved built-in functions. The function names are prefixed with 
    a double underscore to indicate that they are machine internal.
    
    Translation proceeds till the [code] is exhausted, upon which the
    modified translator object is returned to the caller.
    
    %\bigskip%
*)

Open Local Scope string_scope.

Fixpoint translateCode
    (xlator : tXlator)
    (code : tGMCode)
    (zone : tCodeSegmentZone)
    {struct code} : tXlator :=
    match code with
    | nil => xlator
    | instr :: code' => 
        let xlator''' :=
            match instr with
            | GMi.PushGlobal name => 
                let 
                    (code, xlator'') := generateCall (getNumArgs name xlator) name xlator
                in
                    addCode code zone xlator''
            | GMi.PushInt num => allocateRegAndLoadValue xlator num 
            | GMi.Push num =>
                let
                    pReg := Reg P xlator.(fPC)
                in
                    allocateReg P (pushReg pReg xlator)
            | GMi.Add              => generateDyadicCode GMi.Add zone xlator
            | GMi.Sub              => generateDyadicCode GMi.Sub zone xlator
            | GMi.Mul              => generateDyadicCode GMi.Mul zone xlator
            | GMi.Div              => generateDyadicCode GMi.Div zone xlator
            | GMi.Eq               => generateDyadicCode GMi.Eq zone xlator 
            | GMi.Ne               => generateDyadicCode GMi.Ne zone xlator
            | GMi.Lt               => generateDyadicCode GMi.Lt zone xlator
            | GMi.Le               => generateDyadicCode GMi.Le zone xlator
            | GMi.Gt               => generateDyadicCode GMi.Gt zone xlator
            | GMi.Ge               => generateDyadicCode GMi.Ge zone xlator
            | GMi.Neg              => generateMonadicCode GMi.Neg zone xlator
            | GMi.Alloc num        => generateBuiltInCall "__alloc" [Z.of_nat num] zone xlator
            | GMi.Unwind           => generateBuiltInCall "__unwind" [] zone xlator
            | GMi.Pop num          => generateBuiltInCall "__pop" [] zone xlator
            | GMi.Update num       => generateBuiltInCall "__update" [Z.of_nat num] zone xlator
            | GMi.Slide num        => generateBuiltInCall "__slide" [Z.of_nat num] zone xlator
            | GMi.MkAp             => generateBuiltInCall "__mkAp" [] zone xlator
            | GMi.Eval             => generateBuiltInCall "__eval" [] zone xlator
            | GMi.Split num        => generateBuiltInCall "__split" [Z.of_nat num] zone xlator
            | GMi.Print            => generateBuiltInCall "__print" [] zone xlator
            | _                    => xlator
(*
            | GMi.Cond tb fb       => generateBranchCalls tb fb zone xlator
            | GMi.Pack tag arity   => xlator
*)
            end
        in
            translateCode xlator''' code' zone
    end.

Close Local Scope nat_scope.

(** ** Translation Kernel
    The translator retrieves the supercombinator definitions from the G-machine's
    global and heap sections and translates them into R-code using the 
    [translateAssocs] function. Finally, the [main] function is 
    translated to RM code.
*)

Definition translateGlobal 
    (xlator : tXlator)
    (code : tGMCode) : tXlator :=
    translateCode xlator code Suffix.

Definition translateAssoc 
    (xlator : tXlator)
    (name : tName)
    (value : tNode) : tXlator :=
    let
        codeAddr := S (S (S (List.length xlator.(fCode))))
    in
        match value with
        | NGlobal n code => 
            addCodeEntry 
                name
                codeAddr 
                (translateGlobal xlator code)
        | _ => xlator
        end.

Import ListNotations.

Definition getEndMarker : string :=
    "end".

Fixpoint translateAssocs
    (globals : tGMGlobals)
    (xlator : tXlator) : tXlator :=
    match globals with
    | assoc :: assocs => 
        let
            (name, addr) := assoc
        in
            let
                node := snd(nth (addr - 1) (getHeapAssocs (GMi.getHeap xlator.(fGM))) (pair NullAddr (NGlobal 0 [])))
            in
                translateAssocs assocs (translateAssoc xlator name node)
    | _ => xlator
    end.

Definition translate (xlator : tXlator) : tXlator :=
    let
        xlator' := translateAssocs (GMi.getGlobals xlator.(fGM)) xlator
    in
        let
            xlator'' := addCode [Goto "end"] Prefix xlator' 
        in
            let
                xlator''' := translateCode xlator'' (GMi.getCode xlator''.(fGM)) Prefix
            in    
                addCode [Halt] Suffix (addCodeEntry getEndMarker (List.length xlator'''.(fCode)) xlator''').

Close Local Scope string_scope.

End XlatorImpl.
