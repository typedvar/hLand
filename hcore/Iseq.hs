module Iseq 
    where
        
import Types
            
iNil :: Iseq
iNil = INil

iStr :: String -> Iseq
iStr s = IStr s

iAppend :: Iseq -> Iseq -> Iseq
iAppend seq1 seq2 = IAppend seq1 seq2

iNewline :: Iseq
iNewline = INewline

iComma :: Iseq
iComma = IComma

iSemiColon :: Iseq
iSemiColon = ISemiColon

iSpace :: Iseq
iSpace = ISpace

iNum :: Int -> Iseq
iNum n = iStr (show n)

iFWNum :: Int -> Int -> Iseq
iFWNum width n 
    = iStr (space (width - length digits) ++ digits)
        where
            digits = show n

iIndent :: Iseq -> Iseq
iIndent seq' = IIndent seq'

iDisplay :: Iseq -> String
iDisplay seq' = flatten 0 [(seq',0)]

iConcat :: [Iseq] -> Iseq
iConcat = foldr iAppend iNil

iInterleave :: Iseq -> [Iseq] ->Iseq
iInterleave _ [] = iNil
iInterleave _ [seq'] = seq'
iInterleave sep (seq' : seqs) = seq' `iAppend` (sep `iAppend` iInterleave sep seqs)

flatten :: Int -> [(Iseq, Int)] -> String
flatten _ [] = ""
flatten _ ((INil, indent) : seqs) = flatten indent seqs
flatten _ ((IStr s, indent) : seqs) = s ++ (flatten indent seqs)
flatten col ((IAppend seq1 seq2, indent) : seqs) = flatten indent ((seq1, col) : (seq2, col) : seqs)
flatten _ ((INewline, indent) : seqs) = '\n' : (space indent) ++ (flatten indent seqs)
flatten _ ((IComma, indent) : seqs) = ',' : ' ' : (space indent) ++ (flatten indent seqs)
flatten _ ((ISemiColon, indent) : seqs) = ';' : ' ' : (space indent) ++ (flatten indent seqs)
flatten _ ((ISpace, indent) : seqs) = ' ' : (space indent) ++ (flatten indent seqs)
flatten col ((IIndent seq', _) : seqs) = flatten col ((seq', col) : seqs)

space :: Int -> String
space 0 = ""
space n = " " ++ (space (n - 1))

iLayn :: [Iseq] -> Iseq
iLayn seqs = iConcat (map layItem (zip [1..] seqs))
    where
    layItem (n, s)
        = iConcat [ iFWNum 4 n, iStr ") ", iIndent s, iNewline ]
        
-- end of file
