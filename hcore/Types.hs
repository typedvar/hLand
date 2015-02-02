module Types
    where
    
-----------------------------------------
-- Printer type    
-----------------------------------------
data Iseq = INil
            | IStr String
            | IAppend Iseq Iseq
            | IIndent Iseq
            | INewline
            | IComma
            | ISpace
            | ISemiColon

-----------------------------------------
-- Parser types
-----------------------------------------
data Expr a = EVar Name
    | ENum Int
    | EPack Int Int          -- tag, arity
    | EAp (Expr a) (Expr a)
    | ELet
        IsRec
        [(a, Expr a)]
        (Expr a)
    | ECase
        (Expr a)
        [Alter a]
    | ELam [a] (Expr a)
        deriving (Show)
        
type IsRec = Bool
type Alter a = (Int, [a], Expr a)
type CoreAlt = Alter Name
type CoreExpr = Expr Name
type ScDefn a = (Name, [a], Expr a)
type CoreScDefn = ScDefn Name
type Program a = [ScDefn a]
type CoreProgram = Program Name

data PartialExpr = NoOp | FoundOp Name CoreExpr

-- A token has the line number where it appears and
-- a string indicating the type of the token
type Token = (Int, String)

-- a parser of type 'a' takes a list of tokens
-- and extracts a token if it is of type 'a'
-- and returns a list of tuples 
-- It returns a list instead of a pair in order to 
-- accomodate the possibility of multiple parses
-- which arise in case of ambiguous grammars
type NParser a = [Token] -> [(a, [Token])]

type Name = String

type Addr = Int

data Instruction = 
    Add | Sub | Mul | Div | Neg
    | Alloc Int
    | Cond [Instruction] [Instruction]
    | Eq | Ne | Lt | Le | Gt | Ge
    | Eval
    | MkAp
    | Pop Int
    | Push Int
    | PushGlobal Name
    | PushInt Int
    | Slide Int
    | Unwind
    | Update Int
    | Pack Int Int
    | Casejump [(Int, GMCode)]
    | Split Int
    | Print    
instance Eq Instruction
    where
        Alloc a == Alloc b = a == b
        MkAp == MkAp = True
        Push a == Push b = a == b
        PushGlobal a == PushGlobal b = a == b
        PushInt a == PushInt b = a == b
        Slide a == Slide b = a == b
        Unwind == Unwind = True
        Update a == Update b = a == b
        _ == _ = False

data Node = NAp Addr Addr
    | NSuperComb Name [Name] CoreExpr
    | NNum Int
    | NInd Addr
    | NGlobal Int GMCode
    | NConstr Int [Addr]
instance Eq Node
    where
        NNum a == NNum b = a == b                
        NAp a b == NAp c d = False
        NGlobal a b == NGlobal c d = False
        NInd a == NInd b = False
        NSuperComb a b c == NSuperComb d e f = False
        NConstr a b == NConstr c d = False
        _ == _ = False
                
-- Heap is a triple of 
--      num objects in the heap
--      list of unused addresses
--      association list mapping addresses to objects
type Pair a b = (a, b)

-- Association list as a type
type Assoc a b = [Pair a b]

type Heap a = (Int, [Addr], Assoc Addr a)

type GMEnvironment = Assoc Name Int
type GMCompiler = CoreExpr -> GMEnvironment -> GMCode
type GMCompiledSC = (Name, Int, GMCode)
type GMHeap = Heap Node 
type GMStack = [Addr]
type GMCode = [Instruction]
type GMGlobals = Assoc Name Addr
type GMStats = Int
type GMDumpItem = (GMCode, GMStack)
type GMDump = [GMDumpItem]
type GMOutput = String

-- G-Machine state
type GMState = (GMOutput
    , GMCode
    , GMStack
    , GMDump
    , GMHeap
    , GMGlobals
    , GMStats)

-- end of file
