main = fib 10; 
fib n = if (n == 1) 1 (if (n == 2) 1 (compute n));
compute n = fib (n - 1) + fib (n - 2)
