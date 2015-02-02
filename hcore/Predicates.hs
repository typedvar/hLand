module Predicates
    where

import Data.Char

isNewline :: Char -> Bool
isNewline c = c == '\n' || c == '\r'

-- returns true on encountering //
isCommentMarker :: Char -> Char -> Bool
isCommentMarker c0 c1 = (c0 == '/') && (c1 == '/')

isWhiteSpace :: Char -> Bool
isWhiteSpace c = c `elem` whiteSpaceChars

isIdChar :: Char -> Bool
isIdChar c = isAlpha c || isDigit c || (c `elem` allowedVarChars)

isVar :: String -> Bool
isVar tok = (isAlpha.head) tok && (tok `notElem` keyWords)
    
isTwoCharOp :: Char -> Char -> Bool
isTwoCharOp c1 c2 = [c1, c2] `elem` twoCharOps

isKeyWord :: String -> Bool
isKeyWord s = s `elem` keyWords

twoCharOps :: [String]
twoCharOps = ["==", "~=", ">=", "<=", "->"]

keyWords :: [String]
keyWords = ["let", "letrec", "case", "in", "of", "Pack"]

allowedVarChars :: String
allowedVarChars = "\'_"

whiteSpaceChars :: String
whiteSpaceChars = " \t"
-- end of file
