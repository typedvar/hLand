main = fac 10; 
fac n = 
  if (n==0) 
    1 
    (n * fac (n-1))
