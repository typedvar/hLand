module DrvGM
    where

import NParser
import GCompiler
import GMachine
import GPrinter
import Repl
import Iseq

gmPrompt :: String
gmPrompt = "G Machine> "

gmEngine :: String -> IO ()
gmEngine str = putStr (runProg str) >> repl gmPrompt gmEngine

runProg :: String -> String
runProg = iDisplay . showResult . gmEval . gmCompile . parse

runProgDebug :: String -> String
runProgDebug = iDisplay . showAll . gmEval . gmCompile . parse

gm :: IO ()
gm = repl gmPrompt gmEngine

-- end of file
  