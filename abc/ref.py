"""Reference model of the abc machine: the pairs in search order and their values."""
from math import gcd

def isprime(p): return p >= 2 and all(p % d for d in range(2, int(p ** 0.5) + 1))

def rad(n):
    r, p = 1, 2
    while n > 1:
        if n % p == 0:
            r *= p
            while n % p == 0: n //= p
        p += 1
    return r

def pairs():
    """(a, b) for c = 2, 3, ...; a = 1 .. c - 1."""
    c = 2
    while True:
        for a in range(1, c):
            yield a, c - a
        c += 1

def value(a, b):
    """None if the pair is skipped (not coprime, or c <= rad(abc)); else the least n >= 1
    with c^n > rad^(n+1) (the number of beeps before its boop)."""
    c = a + b
    if gcd(a, b) != 1: return None
    r = rad(a * b * c)
    if c <= r: return None
    n = 1
    while c ** n <= r ** (n + 1): n += 1
    return n

def events(npairs):
    """The event string (B = beep, O = boop) of the first npairs pairs."""
    out = []
    for i, (a, b) in enumerate(pairs()):
        if i >= npairs: break
        v = value(a, b)
        if v is not None: out.append('B' * v + 'O')
    return ''.join(out)

if __name__ == '__main__':
    for i, (a, b) in enumerate(pairs()):
        if i > 600: break
        v = value(a, b)
        if v is not None: print(a, b, a + b, rad(a * b * (a + b)), v)
