module GMachine
    where

import Types
import Heap

-- Getter and setter of the G-machine state
getOutput :: GMState -> GMOutput
getOutput (o, _, _, _, _, _, _) = o

putOutput :: GMOutput -> GMState -> GMState
putOutput o' (_, i, stack, dump, heap, globals, stats) 
    = (o', i, stack, dump, heap, globals, stats) 

getHeap :: GMState -> GMHeap
getHeap (_, _ , _, _, heap, _, _) =  heap

putHeap :: GMHeap -> GMState -> GMState
putHeap newHeap (output, code, stack, dump, _, globals, stats) 
    = (output, code, stack, dump, newHeap, globals, stats)
    
getStack :: GMState -> GMStack
getStack (_, _, stack, _, _, _, _) = stack

putStack :: GMStack -> GMState -> GMState
putStack newStack (output, code, _, dump, heap, globals, stats) 
    = (output, code, newStack, dump, heap, globals, stats)

getDump :: GMState -> GMDump
getDump (_, _, _, dump, _, _, _) 
    = dump

putDump :: GMDump -> GMState -> GMState
putDump dump' (output, i, stack, _, heap, globals, stats) 
    = (output, i, stack, dump', heap, globals, stats)

getCode :: GMState -> GMCode
getCode (_, code, _, _, _, _, _) = code 

putCode :: GMCode -> GMState -> GMState
putCode newCode (output, _, stack, dump, heap, globals, stats) 
    = (output, newCode, stack, dump, heap, globals, stats)

getGlobals :: GMState -> GMGlobals
getGlobals (_, _, _, _, _, globals, _) = globals

getStats :: GMState -> GMStats
getStats (_, _, _, _, _, _, stats) = stats

putStats :: GMStats -> GMState -> GMState
putStats newStats (ouptut, code, stack, dump, heap, globals, _) 
    = (ouptut, code, stack, dump, heap, globals, newStats)

statIncSteps :: GMStats -> GMStats
statIncSteps stats = stats + 1

statGetSteps :: GMStats -> Int
statGetSteps stats = stats

-- The eval function steps through each GM state until the final GM state is 
-- reached.
gmEval :: GMState -> [GMState]
gmEval state = state : restStates
    where
    restStates | gmFinal state = []
              | otherwise = gmEval nextState
    nextState = doAdmin (gmStep state)

gmFinal :: GMState -> Bool
gmFinal s = case getCode s of
    [] -> True
    _ -> False   
   
doAdmin :: GMState -> GMState
doAdmin s = putStats (statIncSteps (getStats s)) s

gmStep :: GMState -> GMState
gmStep state = gmDispatch i (putCode is state)
    where (i:is) = getCode state
    
gmDispatch :: Instruction -> GMState -> GMState
gmDispatch (PushGlobal f) = pushGlobal f
gmDispatch (PushInt n) = pushInt n
gmDispatch MkAp = mkAp
gmDispatch (Push n) = push n
gmDispatch (Update n) = update n
gmDispatch (Pop n) = pop n
gmDispatch Unwind = unwind
gmDispatch (Slide n) = slide n
gmDispatch (Alloc n) = alloc n

gmDispatch Eval = eval2WHNF
gmDispatch Add = arithmetic2 (+)
gmDispatch Sub = arithmetic2 (-)
gmDispatch Mul = arithmetic2 (*)
gmDispatch Div = arithmetic2 opDiv
gmDispatch Neg = arithmetic1 opNeg

gmDispatch (Cond i1 i2) = cond i1 i2
gmDispatch Eq = comparison (==)
gmDispatch Ne = comparison (/=)
gmDispatch Lt = comparison (<)
gmDispatch Le = comparison (<=)
gmDispatch Gt = comparison (>)
gmDispatch Ge = comparison (>=)

gmDispatch (Pack t arity) = pack t arity
gmDispatch (Casejump es) = caseJump es
gmDispatch (Split n) = split n
gmDispatch Print = printer

pack :: Int -> Int -> GMState -> GMState
pack t n state
    = putHeap heap' (putStack (addr: drop n s) state)
    where 
        s = getStack state
        (heap', addr) = hAlloc (getHeap state) (NConstr t (take n s))

caseJump :: [(Int, GMCode)] -> GMState -> GMState
caseJump es s 
    = putCode (i ++ getCode s) s
    where 
        (NConstr t _) = hLookup (getHeap s) (head (getStack s))
        i = aLookup es t (error ("No case for constructor" ++ show t)) 

split :: Int -> GMState -> GMState
split _ state
    = putStack (as ++ s) state
    where 
        (NConstr _ as) = hLookup (getHeap state) a
        (a:s)          = getStack state

printer :: GMState -> GMState
printer s = newState
    where
        (addr : _) = getStack s
        newState = printer' (hLookup (getHeap s) addr) s

printer' :: Node -> GMState -> GMState
printer' (NNum n) s = putOutput o s'
    where 
    o = (getOutput s) ++ show n
    s' = (putStack addrs s)
    (_ : addrs) = getStack s

printer' (NConstr t argAddrs) s = putCode (i' ++ (getCode s)) s'
    where
    s'' = putOutput ("Pack{" ++ show t ++ "," ++ show(length argAddrs) ++ "}") s'
    (_: addrs) = getStack s
    s' = putStack (argAddrs ++ addrs) s
    i' = printcode (length argAddrs)
    
printcode :: Int -> [Instruction]
printcode 0 = []
printcode n = Eval : Print : printcode (n - 1)

opNeg :: Int -> Int
opNeg n = -n

opDiv :: Int -> Int -> Int
opDiv n1 n2 = quot n1 n2

alloc :: Int -> GMState -> GMState
alloc n state = putStack stack' state'
    where
    state' = putHeap heap' state
    heap' = fst ret
    ret = allocNodes n (getHeap state)
    stack' = addrs ++ (getStack state)
    addrs = snd ret

allocNodes :: Int -> GMHeap -> (GMHeap, [Addr])
allocNodes 0 heap = (heap, [])
allocNodes n heap = (heap2, a:as)
    where 
    (heap1, as) = allocNodes (n - 1) heap
    (heap2, a) = hAlloc heap1 (NInd hNull)

slide :: Int -> GMState -> GMState
slide n state = putStack (a: drop n as) state
    where 
    (a:as) = getStack state

pushGlobal :: Name -> GMState -> GMState
pushGlobal f state
    = putStack (addr: getStack state) state
    where
    addr = aLookup (getGlobals state) f (error ("Symbol " ++ f ++ " is not defined"))

-- pushes an Integer Node into the heap
pushInt :: Int -> GMState -> GMState
pushInt n state
    = putHeap newHeap state'
    where 
    state' = putStack (addr: getStack state) state
    (newHeap, addr) = hAlloc (getHeap state) (NNum n) 

mkAp :: GMState -> GMState
mkAp state
    = putHeap heap' (putStack (a:as) state)
    where
    (heap', a) = hAlloc (getHeap state) (NAp a1 a2)
    (a1:a2:as) = getStack state 

push :: Int -> GMState -> GMState
push n state 
    = putStack (a:as) state
    where
    as = getStack state
    a = as !! n
    
pop :: Int -> GMState -> GMState
pop n state = putStack stack' state
    where
    stack' = drop n (getStack state)
      
update :: Int -> GMState -> GMState
update n state 
    = putHeap heap' (putStack as state)
    where
    heap' = hUpdate (getHeap state) (as !! n) (NInd a)
    (a:as) = getStack state
    

boxInteger :: Int -> GMState -> GMState
boxInteger n state
    = putStack (a: getStack state) (putHeap h' state)
    where (h', a) = hAlloc (getHeap state) (NNum n)

boxBoolean :: Bool -> GMState -> GMState
boxBoolean b state
    = putStack (a: getStack state) newState
    where 
        newState = (putHeap h' state)
        (h', a) = hAlloc (getHeap state) (NConstr b' []) 
        b' | b = 2         -- True
           | otherwise = 1 -- False

unboxInteger :: Addr -> GMState -> Int
unboxInteger a state
    = ub (hLookup (getHeap state) a)
    where 
    ub (NNum i) = i
    ub _ = error "Unboxing a non-integer"

primitive1 :: (b -> GMState -> GMState) -- boxing function
                -> (Addr -> GMState -> a) -- unboxing function
                -> (a -> b) -- operator
                -> (GMState -> GMState) -- state transition
primitive1 box unbox op state
    = box (op (unbox a state)) (putStack as state)
    where 
        (a:as) = getStack state

primitive2 :: (b -> GMState -> GMState) -- boxing function
                -> (Addr -> GMState -> a) -- unboxing function
                -> (a -> a -> b) -- operator
                -> (GMState -> GMState) -- state transition
primitive2 box unbox op state
    = box result state'
    where 
        result = (op (unbox a0 state) (unbox a1 state))
        (a0:a1:as) = getStack state
        state' = (putStack as state)

arithmetic1 :: (Int -> Int) -- arithmetic operator
                -> (GMState -> GMState) -- state transition
arithmetic1 = primitive1 boxInteger unboxInteger

arithmetic2 :: (Int -> Int -> Int) -- arithmetic operation
                -> (GMState -> GMState) -- state transition
arithmetic2 = primitive2 boxInteger unboxInteger

comparison :: (Int -> Int -> Bool) -> GMState -> GMState
comparison = primitive2 boxBoolean unboxInteger

doLt :: GMState -> GMState
doLt state = state'
    where
        state' = putStack as (boxBoolean True state)
        (a0:a1:as) = getStack state
        result = (<) (unboxInteger a0 state) (unboxInteger a1 state)

eval2WHNF :: GMState -> GMState
eval2WHNF state
    = putDump (frame : getDump state) (putStack [a] (putCode [Unwind] state))
    where
        frame = (getCode state, stack)
        (a : stack) = getStack state
        
cond :: GMCode -> GMCode -> GMState -> GMState
cond i1 i2 state 
    = putCode code' state'
    where
        state' = putStack stack state
        (a : stack) = getStack state
        is = getCode state
        code' = i ++ is
        i = getCodeStream i1 i2 (hLookup (getHeap state) a)

getCodeStream :: GMCode -> GMCode -> Node -> GMCode
getCodeStream i1 i2 (NConstr 2 _) = i1
getCodeStream i1 i2 _ = i2     

getArg :: Node -> Addr
getArg (NAp a1 a2) = a2    

rearrange :: Int -> GMHeap -> GMStack -> GMStack
rearrange n heap addrs
    = take n addrs' ++ drop n addrs 
    where addrs' = map (getArg . hLookup heap) (tail addrs) 

unwind :: GMState -> GMState
unwind state
    = newState (hLookup heap a)
    where
        (a:as) = getStack state
        heap = getHeap state
        ((i, stack):dump) = getDump state
        newState (NNum n) 
            = putCode i (putStack (a:stack) (putDump dump state))
        newState (NAp a1 a2) = putCode [Unwind] (putStack (a1:a:as) state) 
        newState (NGlobal n c)
            | length as >= n = putCode c (putStack as' state)
            | otherwise      = putCode i (putStack (last (a:as):stack) (putDump dump state))
            where as' = rearrange n heap (a:as)
        newState (NInd aInd) = putCode [Unwind] (putStack (aInd:as) state)
        newState (NConstr t as)
            = putCode i (putStack (a:stack) (putDump dump state))

builtInDyadic :: Assoc Name Instruction -- list of pairs - [(Name, Instruction)]
builtInDyadic = 
    [ ("+", Add), ("-", Sub), ("*", Mul), ("div", Div),
    ("==", Eq), ("~=", Ne), (">=", Ge),
    (">", Gt), ("<=", Le), ("<", Lt)]

-- end of file
