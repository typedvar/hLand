module Lexer
    where
    
import Predicates
import Data.Char
import Types

-- Takes a string of chars and tokenizes it
-- for reporting purposes it accepts 
-- a line number to indicate
-- the location of an error/warning
-- uses predicates defined in Predicates.hs
-- for classifying input

clex :: Int -> String -> [Token]

-- eat whitespaces
clex line (c:cs) | isWhiteSpace c = clex line cs

-- eat comments; comments span starts from the comment marker '//' till a newline
clex line (c0:c1:cs) | isCommentMarker c0 c1 = clex line restCs
    where
        restCs = dropWhile (not.isNewline) cs

-- increment line number on encountering a newline        
clex line (c:cs) | isNewline c = clex (line + 1) cs        

-- tokenize digits         
clex line (c:cs) | isDigit c = (line, numToken) : clex line restCs
    where
        numToken = c : takeWhile isDigit cs
        restCs = dropWhile isDigit cs

-- tokenize identifiers        
clex line (c:cs) | isAlpha c = (line, varTok) : clex line restCs
    where
        varTok = c : takeWhile isIdChar cs
        restCs = dropWhile isIdChar cs

-- tokenize twoCharOp        
clex line (c1:c2:cs) | isTwoCharOp c1 c2 = (line, [c1, c2]) : clex line cs        

-- failsafe tokenizer
clex line (c:cs) = (line, [c]) : clex line cs

-- lexer termination
clex _ [] = []

-- end of file
