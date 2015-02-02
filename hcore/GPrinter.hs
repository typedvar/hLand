module GPrinter
    where

import Types
import Heap
import Iseq
import GMachine

showAll :: [GMState] -> Iseq
showAll states
    = iConcat [
        iStr "Compiled Supercombinators:"
        , iNewline
        , iStr "-----------------"
        , iNewline
        , iInterleave iNewline (map (showSC s) (getGlobals s))
        , iNewline
        , iStr "State transitions:"
        , iNewline
        , iStr "------------------"
        , iNewline
        , iLayn (map showState states)
        , iNewline
        , showStats (last states)
        , iNewline]
    where (s:_) = states

showResult :: [GMState] -> Iseq
showResult states = (iStr . getOutput . last) states

showCoqCompiledState :: GMState -> Iseq
showCoqCompiledState state 
    = iConcat [
        iStr "Require Import List."
        , iNewline
        , iStr "Require Import ZArith."
        , iNewline
        , iStr "Require Import VUtils."
        , iNewline
        , iStr "Require Import VHeap."
        , iNewline
        , iStr "Require Import GM."
        , iNewline
        , iNewline
        , iStr "Module Export FImplTesti."
        , iNewline
        , iStr "Import ListNotations."
        , iNewline
        , iNewline
        , iStr "Open Local Scope nat_scope."
        , iNewline
        , iStr "Open Local Scope string_scope."
        , iNewline
        , iNewline
        , iStr "Definition testGM : tGMState :="
        , iNewline
        , showCompiledState state
        , iStr "."
        , iNewline
        , iNewline
        , iStr "End FImplTesti."
        ]
        
showCompiledState :: GMState -> Iseq
showCompiledState state 
    = iConcat [
        iStr "("
        , iNewline
        , iStr "0%Z"
        , iComma
        , iNewline
        , showInstructions (getCode state)
        , iComma
        , iNewline
        , iStr "nil"
        , iComma
        , iNewline
        , iStr "nil"
        , iComma
        , iNewline
        , (showHeap . getHeap) state
        , iComma
        , iNewline
        , iStr "["
        , iInterleave iSemiColon (map (showGlobal) (getGlobals state))
        , iStr "]"
        , iComma
        , iNewline
        , iStr "0"
        , iNewline
        , iStr ")"
        ]
        
showGlobal :: (Name, Addr) -> Iseq
showGlobal (name, addr)
   = iConcat [ 
        iStr "("
        , iStr "\"" 
        , iStr name
        , iStr "\"" 
        , iComma
        , iNum addr
        , iStr ")"
        ]
    
showSC :: GMState -> (Name, Addr) -> Iseq
showSC s (name, addr)
   = iConcat [ iStr name
        , iStr " : "
        , showInstructions code]
   where (NGlobal _ code) = (hLookup (getHeap s) addr)

showInstructions :: GMCode -> Iseq
showInstructions is
   = iConcat [ iStr "[",
       iIndent (iInterleave iSemiColon (map showInstruction is)),
       iStr "]"]
   
showInstruction :: Instruction -> Iseq
showInstruction Unwind = iStr "Unwind"
showInstruction (PushGlobal f) = (iStr "PushGlobal ") `iAppend` (iConcat [iStr "\"", iStr f, iStr "\""])
showInstruction (Push n) = (iStr "Push ") `iAppend` (iNum n)
showInstruction (PushInt n) = (iStr "PushInt ") `iAppend` (iNum n)
showInstruction MkAp = iStr "MkAp"
showInstruction (Pop n) = (iStr "Pop ") `iAppend` (iNum n)
showInstruction (Update n) = (iStr "Update ") `iAppend` (iNum n)
showInstruction (Slide n) = (iStr "Slide ") `iAppend` (iNum n)
showInstruction (Alloc n) = (iStr "Alloc ") `iAppend` (iNum n)
showInstruction Eval = iStr "Eval"
showInstruction Add = iStr "Add "
showInstruction Sub = iStr "Sub "
showInstruction Mul = iStr "Mul "
showInstruction Div = iStr "Div "
showInstruction Neg = iStr "Neg "
showInstruction Eq = iStr "Eq "
showInstruction Ne = iStr "Ne "
showInstruction Lt = iStr "Lt "
showInstruction Le = iStr "Le "
showInstruction Gt = iStr "Gt "
showInstruction Ge = iStr "Ge "
showInstruction (Cond i1 i2) = iConcat [
                                    iStr "Cond "
                                    , showInstructions  i1
                                    , iSpace
                                    , showInstructions i2
                                    ]
                                    
showInstruction (Pack t a) = ((iStr "Pack ") `iAppend` (iNum t)) `iAppend` (iNum a)
showInstruction (Casejump nis) = (iStr "Casejump ") `iAppend` (showAlternatives nis)
showInstruction (Split n)      = (iStr "Split ") `iAppend` (iNum n)
showInstruction Print          = iStr "Print"

showAlternatives nis = 
    iConcat [iStr "[",
            iInterleave (iStr ", ") (map showLabelInstructions nis),
            iStr "]"]
    where showLabelInstructions (tag, code) = iConcat [iNum tag, iStr ": ", shortShowInstructions 2 code]

showState :: GMState -> Iseq
showState s
   = iConcat [
        iNewline
        , showOutput s
        , iNewline
        , showCode s
        , iNewline
        , showStack s
        , iNewline
        , showDump s
        , iNewline]

showOutput :: GMState -> Iseq
showOutput s 
    = iConcat [iStr "Output: {"
        , iStr (getOutput s)
        , iStr "}"]

showCode :: GMState -> Iseq
showCode state =
    iConcat [iStr "Code: "
        , showInstructions (getCode state)]
    
showDump :: GMState -> Iseq
showDump s
    = iConcat [iStr "Dump: {",
        iIndent (iInterleave iNewline
        (map showDumpItem (reverse (getDump s)))),
        iStr "}"]

showDumpItem :: GMDumpItem -> Iseq
showDumpItem (code, stack)
    = iConcat [iStr "<",
        shortShowInstructions 3 code, iStr ", ",
        shortShowStack stack, iStr ">"]       

showStack :: GMState -> Iseq
showStack s
   = iConcat [iStr "Stack: {"
        , iIndent (iInterleave iComma (map (showStackItem s) (reverse (getStack s))))
        , iStr "}"]

shortShowInstructions :: Int -> GMCode -> Iseq
shortShowInstructions number code
    = iConcat [iStr "{", iInterleave (iStr "; ") dotcodes, iStr "}"]
    where 
        codes = map showInstruction (take number code)
        dotcodes 
            | length code > number = codes ++ [iStr "..."]
            | otherwise = codes

shortShowStack :: GMStack -> Iseq
shortShowStack stack
    = iConcat [iStr "[",
        iInterleave (iStr ", ") (map showAddr stack),
        iStr "]"]

showAddr :: Addr -> Iseq
showAddr addr = iStr (show addr)
   
showStackItem :: GMState -> Addr -> Iseq
showStackItem s a
    = iConcat [showAddr a, iStr ": ", showNode s a (hLookup (getHeap s) a)]

showNode :: GMState -> Addr -> Node -> Iseq
showNode _ _ (NNum n) = iNum n
showNode s a (NGlobal _ _) = iConcat [iStr "Global ", iStr v]
    where 
    v = head [n | (n,b) <- getGlobals s, a==b]
    
showNode _ _ (NAp a1 a2) = iConcat [iStr "Ap ", showAddr a1, iStr " ", showAddr a2]
showNode _ _ (NInd a1) = iConcat [iStr "Ind ", showAddr a1]
showNode _ _ (NConstr t as) = iConcat [iStr "Ctor ", iNum t, iStr " [", iInterleave (iStr ", ") (map showAddr as), iStr "]"]
showNode _ _ (NSuperComb name args _) 
    = iConcat 
        [
            iStr "SC "
            , iStr name
            , iStr " ["
            , iInterleave (iStr ", ") (map iStr args)
            , iStr "]"
        ]

showNode' :: Node -> Iseq
showNode' (NNum n) = iNum n
showNode' (NGlobal n code) = iConcat [iStr "NGlobal ", iNum n, iSpace, showInstructions code]
showNode' (NAp a1 a2) = iConcat [iStr "Ap ", showAddr a1, iSpace, showAddr a2]
showNode' (NInd a1) = iConcat [iStr "Ind ", showAddr a1]
showNode' (NConstr t as) = iConcat [iStr "Ctor ", iNum t, iStr " [", iInterleave (iStr ", ") (map showAddr as), iStr "]"]
showNode' (NSuperComb name args _) 
    = iConcat 
        [
            iStr "SC "
            , iStr name
            , iStr " ["
            , iInterleave (iStr ", ") (map iStr args)
            , iStr "]"
        ]

showAssoc :: (Addr, Node) -> Iseq
showAssoc (addr, node)
    = iConcat 
        [
            iStr "("
            , showAddr addr
            , iStr ", ("
            , showNode' node
            , iStr "))"
        ]
    
showAssocs :: Assoc Addr Node -> Iseq
showAssocs assocs 
    = iInterleave (iConcat [iSemiColon, iNewline, iStr "    "]) (map showAssoc (reverse assocs))

showHeap :: GMHeap -> Iseq
showHeap heap 
    = iConcat
        [
            iStr "(Heap "
            , iNewline
            , iSpace
            , iNum (hSize heap)
            , iNewline
            , iSpace
            , iStr "(FreeStore [] "
            , iNum ((hSize heap) + 1)
            , iStr ")"
            , iNewline
            , iSpace
            , iStr "["            
            , iNewline
            , iStr "    "
            , (showAssocs . hAssocs) heap
            , iNewline
            , iSpace
            , iStr "]"            
            , iNewline
            , iStr ")"            
        ]

showStats :: GMState -> Iseq
showStats s = iConcat [iStr "Steps taken = ", 
                       iNum (statGetSteps (getStats s))]
                       