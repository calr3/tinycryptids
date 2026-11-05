"""Reference model of the search: the pairs (p, m) tested, in order."""
def rep(b, n): return sum(b**i for i in range(n))
def isprime(n): return n > 1 and all(n % d for d in range(2, n))
def pairs(mmax):
    for m in range(3, mmax + 1):
        if isprime(m):
            for p in reversed([q for q in range(2, m) if isprime(q)]):
                yield p, m
