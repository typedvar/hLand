module PrettyPrinter 
    (pprDefns,
    pprExpr)
    where
    
import Language
import Iseq
import Types

pprDefns :: [(Name,CoreExpr)] -> Iseq
pprDefns defns = iInterleave sep (map pprDefn defns)
    where
        sep = iConcat [ iStr ";", iNewline ]

pprDefn :: (Name, CoreExpr) -> Iseq
pprDefn (name, expr) = iConcat [ iStr name, iStr " = ", iIndent (pprExpr expr) ]
       
pprExpr :: CoreExpr -> Iseq
pprExpr (EVar v) = iStr v
pprExpr (EAp (EAp (EVar "+") e1) e2) = iConcat [pprAExpr e1, iStr " + ", pprAExpr e2]
pprExpr (EAp e1 e2) = (pprExpr e1) `iAppend` (iStr " ") `iAppend` (pprAExpr e2)
pprExpr (ELet isRec defns expr) = 
    iConcat [iStr keyword, iNewline, iStr " ", iIndent (pprDefns defns), iNewline, iStr "in ", pprExpr expr]
    where
        keyword 
            | not isRec = "let"
            | isRec = "letrec"
                     
-- pprAExpr is pprExpr with parenthesis when required
pprAExpr :: CoreExpr -> Iseq
pprAExpr e 
    | isAtomicExpr e = pprExpr e
    | otherwise      = (iStr "(") `iAppend` pprExpr e `iAppend` (iStr ")")

-- end of file   
