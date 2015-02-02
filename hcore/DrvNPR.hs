module DrvNPR
    where
    
import NParser
import Repl

npmPrompt :: String
npmPrompt = "Parser Machine> "

parserEngine :: String -> IO ()
parserEngine str = putStrLn (show (parse str)) >> repl npmPrompt parserEngine

npm :: IO ()
npm = repl npmPrompt parserEngine

-- end of file
