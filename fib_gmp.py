from gmpy2 import mpz

def fib(n):
    mask = 1
    while mask < n:
        mask <<= 1
    f_n,f_n_1 = mpz('0'),mpz('1')
    while mask > 0:
        f_2n = f_n*(2*f_n_1 - f_n)
        f_2n_1 = f_n*f_n + f_n_1*f_n_1
        if (n&mask) != 0:
            f_n = f_2n_1
            f_n_1 = f_2n+f_2n_1
        else:
            f_n = f_2n
            f_n_1 = f_2n_1
        mask >>= 1
    return f_n

print hex(fib(int(input("n? "))))

