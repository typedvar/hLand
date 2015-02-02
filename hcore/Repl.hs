module Repl
    where

-- REPL
repl :: String -> (String -> IO()) -> IO ()
repl prompt f =
    do
        putStrLn ("Type " ++ exitCmd ++ " to quit ")
        putStr prompt
        expr <- getLine
        case (length expr) of
            0 -> repl prompt f
            _ -> execute expr
                    where
                        execute str 
                            | str == exitCmd = putStrLn "Machine exited"
                            | otherwise = f str

exitCmd :: String
exitCmd = ":x"

-- end of file
  