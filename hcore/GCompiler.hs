module GCompiler
    where

import Types
import Heap
import Utilities
import Language

gmCompile:: CoreProgram -> GMState
gmCompile program
    = ([], initialCode, [], [], heap, globals, statInitial)
    where 
    (heap, globals) = buildInitialHeap program
    initialCode = [PushGlobal "main", Eval, Print]

statInitial :: GMStats
statInitial = 0

buildInitialHeap :: CoreProgram -> (GMHeap, GMGlobals)
buildInitialHeap program
    = mapAccumLeft allocateCompiledSc hInitial compiled
    where 
     compiled = (map compileSc preludeDefs) 
                 ++  compiledPrimitives 
                 ++ (map compileSc program)
        
compiledPrimitives :: [GMCompiledSC]
compiledPrimitives
    = 
    [
      ("+", 2, [Push 1, Eval, Push 1, Eval, Add, Update 2, Pop 2, Unwind])
    , ("-", 2, [Push 1, Eval, Push 1, Eval, Sub, Update 2, Pop 2, Unwind])
    , ("*", 2, [Push 1, Eval, Push 1, Eval, Mul, Update 2, Pop 2, Unwind])
    , ("/", 2, [Push 1, Eval, Push 1, Eval, Div, Update 2, Pop 2, Unwind])
    , ("negate", 1, [Push 0, Eval, Neg, Update 1, Pop 1, Unwind])
    , ("==", 2, [Push 1, Eval, Push 1, Eval, Eq, Update 2, Pop 2, Unwind])
    , ("~=", 2, [Push 1, Eval, Push 1, Eval, Ne, Update 2, Pop 2, Unwind])
    , ("<", 2, [Push 1, Eval, Push 1, Eval, Lt, Update 2, Pop 2, Unwind])
    , ("<=", 2, [Push 1, Eval, Push 1, Eval, Le, Update 2, Pop 2, Unwind])
    , (">", 2, [Push 1, Eval, Push 1, Eval, Gt, Update 2, Pop 2, Unwind])
    , (">=", 2, [Push 1, Eval, Push 1, Eval, Ge, Update 2, Pop 2, Unwind])
    , ("if", 3, [Push 0, Eval, Cond [Push 1] [Push 2], Update 3, Pop 3, Unwind])
    ]

allocateCompiledSc :: GMHeap -> GMCompiledSC -> (GMHeap, (Name, Addr))
allocateCompiledSc heap (name, nargs, instns) 
    = (heap', (name, addr))
    where 
    (heap', addr) = hAlloc heap (NGlobal nargs instns)
   
-- SuperCombinator compiler    
compileSc :: (Name, [Name], CoreExpr) -> GMCompiledSC
compileSc (name, params, body) 
    = (name, length params, compileR body (zip params [0..]))

-- Compile RHS of SuperCombinator
--     1. uses the modified expression compiler compileE 
--     2. adds code to cleanup the stack (slide) 
--     3. unwind to find the next redex
compileR :: GMCompiler
compileR e env = compileE e env ++ [Update numArgs, Pop numArgs, Unwind]
    where
    numArgs = length env
    
builtInDyadic :: Assoc Name Instruction -- list of pairs - [(Name, Instruction)]
builtInDyadic = 
    [ ("+", Add), ("-", Sub), ("*", Mul), ("div", Div),
    ("==", Eq), ("~=", Ne), (">=", Ge),
    (">", Gt), ("<=", Le), ("<", Lt)]

-- Eta compiler
compileE :: GMCompiler
compileE (EAp (EAp (EVar op) e1) e2) env 
    | op `elem` binaryOps = compileE e2 env ++ compileE e1 env' ++ [value]
    where 
    binaryOps = map fst builtInDyadic
    value = aLookup builtInDyadic op (error "This can't happen")
    env' = argOffset 1 env

compileE (EAp (EVar "negate") e) env
    = compileE e env ++ [Neg]

compileE (EAp (EAp (EAp (EVar "if") e1) e2) e3) env
    = compileE e1 env ++ [Cond (compileE e2 env) (compileE e3 env)]

compileE (ENum n) _ = [PushInt n]

compileE (ELet rec defs e) env 
    | rec       = compileLetrec compileE defs e env
    | otherwise = compileLet    compileE defs e env

compileE (ECase e alts)  env = compileE e env ++
    [Casejump (compileAlts compileE' alts env)]
    
compileE (EPack tag arity) env = compilePack tag arity env ++ [Pack tag arity]

compileE e env = compileC e env ++ [Eval]

compilePack tag arity env = undefined

compileE' :: Int -> GMCompiler
compileE' offset expr env
    = [Split offset] ++ compileE expr env ++ [Slide offset]

compileAlts :: (Int -> GMCompiler) -- compiler for alternative bodies
               -> [CoreAlt] -- the list of alternatives
               -> GMEnvironment -- the current environment
               -> [(Int, GMCode)] -- list of alternative code sequences
compileAlts comp alts env
    = [(tag, comp (length names) body (zip names [0..] 
        ++ argOffset (length names) env))
        | (tag, names, body) <- alts]

-- Expression compiler
compileC :: GMCompiler
compileC (EPack t n) _ = [Pack t n]

compileC (EVar v) env
    | v `elem` aDomain env = [Push n]
    | otherwise = [PushGlobal v]
    where 
        n = aLookup env v (error "Can't happen")

compileC (ENum n) _ = [PushInt n]

compileC (EAp e1 e2) env
    | saturatedCons spine = compileCS (reverse spine) env
    | otherwise = compileC e2 env ++ compileC e1 (argOffset 1 env) ++ [MkAp]
        where 
            spine = makeSpine (EAp e1 e2)
            saturatedCons (EPack t a:es) = a == length es
            saturatedCons (e:es)           = False

compileC (ELet rec defs e) env
    | rec       = compileLetrec compileC defs e env
    | otherwise = compileLet compileC defs e env

compileC _ _ = []

makeSpine (EAp e1 e2) = makeSpine e1 ++ [e2]
makeSpine e           = [e]

compileCS [EPack t a] _ = [Pack t a]
compileCS (e:es)      env = compileC e env ++ compileCS es (argOffset 1 env)
    
compileLetrec :: GMCompiler -> [(Name, CoreExpr)] -> GMCompiler
compileLetrec comp defs expr env =
    [Alloc n] 
    ++ compileLetrec' defs env
    ++ comp expr env'
    ++ [Slide n]
    where
    n = length defs
    env' = compileArgs defs env

compileLetrec' :: [(Name, CoreExpr)] -> GMEnvironment -> GMCode
compileLetrec' [] _ = []
compileLetrec' ((_, expr):defs) env = 
    compileC expr env ++ [Update n] ++ compileLetrec' defs env
    where n = length defs

compileLet :: GMCompiler -> [(Name, CoreExpr)] -> GMCompiler
compileLet comp defs expr env = 
    compileLet' defs env 
    ++ comp expr env' 
    ++ [Slide (length defs)]
    where 
    env' = compileArgs defs env

compileLet' :: [(Name, CoreExpr)] -> GMEnvironment -> GMCode
compileLet' [] _ = []
compileLet' ((_, expr):defs) env = 
    compileC expr env ++ compileLet' defs (argOffset 1 env)

compileArgs :: [(Name, CoreExpr)] -> GMEnvironment -> GMEnvironment
compileArgs defs env = 
    zip (map fst defs) [n-1, n-2 .. 0] ++ argOffset n env
    where n = length defs

argOffset :: Int -> GMEnvironment -> GMEnvironment
argOffset n env = [(v, n+m) | (v,m) <- env]

-- end of file
