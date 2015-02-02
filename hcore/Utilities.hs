module Utilities
    where

-- mapAccumLeft
-- Accepts a function, an accumulator and a list. For each element of the 
-- list it applies the function to the current accumulator and that list 
-- element, which gives a new value of the accumulator and a new list element. 
-- The result of mapAccuml is the final value of the accumulator, and the list 
-- of all the results.
mapAccumLeft :: (a -> b -> (a, c)) -> a -> [b] -> (a, [c])    
mapAccumLeft _ acc [] = (acc, [])
mapAccumLeft f acc (el:els)
    = (acc'', el':els')
        where
            (acc', el') = f acc el
            (acc'', els') = mapAccumLeft f acc' els


