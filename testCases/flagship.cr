main = nestedLet 4;

nestedLet x = oct add2 x;

add2 = sum lazyF;

sum x y = x + y;

lazyF = K' 2 (1/0);

K' c1 c2 = c1;

oct g x = let h = twice g
    in let k = twice h
    in k (k x) 
