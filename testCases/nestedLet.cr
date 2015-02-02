main = nestedLet;
nestedLet = oct I 4;
oct g x = let h = twice g
    in let k = twice h
    in k (k x) 
