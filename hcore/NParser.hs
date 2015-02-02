module NParser
    where
    
import Lexer
import Predicates
import Data.Char
import Types

-- the parser
parse :: String -> CoreProgram
parse = syntax . clex 0

-- syntax checker - takes a parse that is successful
syntax  :: [Token] -> CoreProgram
syntax = takeFirstParse . pProgram

takeFirstParse ((prog, []) : _) = prog
takeFirstParse (_ : others)     = takeFirstParse others
takeFirstParse _                = error "Syntax error" 

-- terminator parser
pSemiColon :: NParser String
pSemiColon = pLit ";"

-- the program parser
pProgram :: NParser CoreProgram
pProgram = pOneOrMoreWithSep pSC pSemiColon

-- the supercombinator parser
pSC :: NParser CoreScDefn
pSC = pThen4 mkSc pVar (pZeroOrMore pVar) (pLit "=") pExpr
    where 
    mkSc sc args _ coreExpr = (sc, args, coreExpr)

-- the expression parser

pExpr = pLet `pAlt` (pCase `pAlt` (pLambda `pAlt` pExpr1))

pExpr1 = pThen assembleOp pExpr2 pExpr1c

pExpr1c = (pThen FoundOp (pLit "|") pExpr1) `pAlt` (pEmpty NoOp)

pExpr2 = pThen assembleOp pExpr3 pExpr2c

pExpr2c = (pThen FoundOp (pLit "&") pExpr2) `pAlt` (pEmpty NoOp)

pExpr3 = pThen assembleOp pExpr4 pExpr3c

pExpr3c = (pThen FoundOp pRelop pExpr4) `pAlt` (pEmpty NoOp)

pExpr4 = pThen assembleOp pExpr5 pExpr4c

pExpr4c = (pThen FoundOp (pLit "+") pExpr4) `pAlt`
          ((pThen FoundOp (pLit "-") pExpr5) `pAlt`
           (pEmpty NoOp))

pExpr5 = pThen assembleOp pExpr6 pExpr5c

pExpr5c = (pThen FoundOp (pLit "*") pExpr5) `pAlt`
          ((pThen FoundOp (pLit "/") pExpr6) `pAlt`
           (pEmpty NoOp))

pExpr6 = (pOneOrMore pAtomic) `pApply` mkApChain
          where
          mkApChain (fn:args) = foldl EAp fn args

pRelop = pSat (`elem` relops)
          where
          relops = ["<=", "<", ">=", ">", "==", "~="]

pAtomic = pConstr `pAlt`
          (pBracExpr `pAlt`
          ((pVar `pApply` EVar) `pAlt`
          ((pNum `pApply` ENum))))

pBracExpr = pThen3 mkBrack (pLit "(") pExpr (pLit ")")
            where
            mkBrack open expr close = expr

pConstr = pThen4 pick_constr (pLit "Pack") (pLit "{") pTagArity (pLit "}")
          where
          pick_constr cons lbrack constr rbrack = constr
          pTagArity = pThen3 mkConstr pNum (pLit ",") pNum
          mkConstr tag comma arity = EPack tag arity

assembleOp e1 NoOp = e1

assembleOp e1 (FoundOp op e2) = EAp (EAp (EVar op) e1) e2

pLet = pThen4 mkLet ((pLit "let") `pAlt` (pLit "letrec")) pDefns (pLit "in") pExpr
    where 
        mkLet letStr defns inLiteral expr = ELet (letStr == "letrec") defns expr

pDefns :: NParser [(Name, Expr Name)]
pDefns = pOneOrMoreWithSep pDefn (pLit ";")

pDefn :: NParser (String, CoreExpr)
pDefn = pThen3 mkDefn pVar (pLit "=") pExpr 
    where mkDefn var equalsLiteral rhs = (var, rhs)

pCase :: NParser (Expr Name)
pCase = pThen4 mkCase (pLit "case") pExpr (pLit "of") pCaseAlts
    where mkCase caseLiteral expr ofLiteral alts = ECase expr alts

pCaseAlts :: NParser [Alter Name]
pCaseAlts = pOneOrMoreWithSep pCaseAlt (pLit ";")

pCaseAlt :: NParser (Int, [String], CoreExpr)
pCaseAlt = pThen4 mkAlt pTag (pZeroOrMore pVar) (pLit "->") pExpr
    where 
    mkAlt tag vars arrowLit expr = (tag, vars, expr)

pTag :: NParser Int
pTag = pThen3 getTag (pLit "<") pNum (pLit ">")
    where 
    getTag leftBracketLiteral tag rightBracketLiteral = tag

pLambda :: NParser (Expr String)
pLambda = pThen4 mkLambda (pLit "\\") (pOneOrMore pVar) (pLit ".") pExpr
    where 
    mkLambda lambdaLiteral boundVariables dotLiteral expr = ELam boundVariables expr
    
   
pTagArity :: NParser (Int, Int)
pTagArity = pThen3 mkTagArity pNum (pLit ",") pNum
    where 
    mkTagArity tag _ arity = (tag, arity)

pApply :: NParser a -> (a -> b) -> NParser b
pApply p f toks = [(f v, toks1) | (v, toks1) <- p toks]

-- A generic parser that parses a token if a predicate is satisfied
-- the predicate is an argument to this parser
-- unwraps the string value from the Token before applying the predicate
-- to it.
pSat :: (String -> Bool) -> NParser String
pSat pred (tok:toks) 
    | pred (snd tok) = [(snd tok, toks)]
    | otherwise = []
    
pSat _ [] = []    

-- parses a token if is matches
-- the literal
pLit :: String -> NParser String
pLit s = pSat (==s)

-- parses a variable
pVar :: NParser String
pVar = pSat isVar

---- parses a number
pNum :: NParser Int
pNum = pSat (isDigit.head) `pApply` ((+0).read)

pEmpty :: a -> NParser a
pEmpty v toks = [(v, toks)]

-- corresponds to the vertical bar in BNF
pAlt :: NParser a -> NParser a -> NParser a
pAlt p1 p2 toks = p1 toks ++ p2 toks

-- takes a combiner and two, or three, or four parsers p1, p2, [p3 [p4]]
-- 1. parses a value from the input using the first parser p1
-- 2. parses the second value from the input using the second parser p2
--    so on and so forth
-- 3. uses the combiner function to concatenate the output of the parsers

pThen :: (a -> b -> c) -> NParser a -> NParser b -> NParser c
pThen combiner p1 p2 toks =
    [ (combiner v1 v2, toks2) | (v1, toks1) <- p1 toks, (v2, toks2) <- p2 toks1 ]

pThen3 :: (a -> b -> c -> d) -> NParser a -> NParser b -> NParser c -> NParser d
pThen3 combiner p1 p2 p3 toks =
    [ (combiner v1 v2 v3, toks3) | (v1, toks1) <- p1 toks, 
                                   (v2, toks2) <- p2 toks1, 
                                   (v3, toks3) <- p3 toks2 ]

pThen4 :: (a -> b -> c -> d -> e) 
    -> NParser a 
    -> NParser b 
    -> NParser c 
    -> NParser d 
    -> NParser e
pThen4 combiner p1 p2 p3 p4 toks =
    [ (combiner v1 v2 v3 v4, toks4) | (v1, toks1) <- p1 toks, 
                                      (v2, toks2) <- p2 toks1, 
                                      (v3, toks3) <- p3 toks2, 
                                      (v4, toks4) <- p4 toks3 ]
    
pZeroOrMore :: NParser a -> NParser [a]
pZeroOrMore p = pOneOrMore p `pAlt` pEmpty []

pOneOrMore :: NParser a -> NParser [a]
pOneOrMore p = pThen (:) p (pZeroOrMore p)

pOneOrMoreWithSep :: NParser a -> NParser b -> NParser [a]
pOneOrMoreWithSep p pSep = pThen (:) p (pOneOrMoreWithSep' p pSep)

pOneOrMoreWithSep' p pSep = (pThen discardSep pSep (pOneOrMoreWithSep p pSep)) 
    `pAlt` pEmpty []
    where
        discardSep _ vs = vs

-- end of file