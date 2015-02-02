module MParser
    where
    
import Types

type Parser a = [Token] -> [(a, [Token])]

result :: a -> Parser a
result v = \inp -> [(v, inp)]

zero :: Parser a
zero = \_-> []

-- item :: Parser a
-- item [] = []
-- item (x:xs) = [(x, xs)]
    
bind :: Parser a -> (a -> Parser b) -> Parser b
bind p f = \inp -> concat [f v inp' | (v, inp') <- p inp]

    