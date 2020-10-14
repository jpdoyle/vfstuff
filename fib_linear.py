# def fib(n):
#     mask = 1
#     while mask < n:
#         mask <<= 1
#     f_n,f_n_1 = 0,1
#     while mask > 0:
#         f_2n = f_n*(2*f_n_1 - f_n)
#         f_2n_1 = f_n*f_n + f_n_1*f_n_1
#         if (n&mask) != 0:
#             f_n = f_2n_1
#             f_n_1 = f_2n+f_2n_1
#         else:
#             f_n = f_2n
#             f_n_1 = f_2n_1
#         mask >>= 1
#     return f_n

def fib(n):
    a,b = 0,1
    for _ in xrange(n):
        a,b = b,(a+b)
    return a*b

print hex(fib(int(input("n? "))))


