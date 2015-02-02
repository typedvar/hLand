module Main 
    where
    
import System.Environment
import DrvGM
import GCompiler
import GPrinter
import NParser
import Iseq

main :: IO ()
main = do
    args <- getArgs
    case (length args) of
        0 -> interp
        1 -> do
            stream <- readFile (args !! 0) 
            putStrLn(source stream)
        2 -> do
            stream <- readFile (args !! 1)
            putStr(invoke (args !! 0) stream)
        _ -> do
            putStr "usage: gm [-c|-d|-q] file"

invoke :: String -> String -> String
invoke opts stream 
    | opts == "-c" = compile stream
    | opts == "-d" = sourceDebug stream
    | opts == "-q" = coqCompile stream
    | otherwise = "reserved for future use"

interp :: IO ()
interp = gm

sourceDebug :: String -> String
sourceDebug stream = runProgDebug stream

source :: String -> String
source stream = runProg stream

coqCompile :: String -> String
coqCompile stream = (iDisplay . showCoqCompiledState. gmCompile . parse) stream

compile :: String -> String
compile stream = (iDisplay . showCompiledState. gmCompile . parse) stream

fImplPrompt :: String
fImplPrompt = "fImpl> "

getEngine :: String -> IO ()
getEngine name 
    | name == "gm" = gm
    | otherwise = interp
    
    