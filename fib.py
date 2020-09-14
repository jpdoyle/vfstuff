def fib(n):
    a,b = 0,1
    for _ in xrange(n):
        a,b = b,(a+b)
    return a

print hex(fib(int(input("n? "))))

