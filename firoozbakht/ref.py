"""Reference model of the search: for each prime q >= 3, (p, q, n, B, A) with p the prime
before q, n = pi(p), B = p^(n+1), A = q^n."""
def isprime(n): return n > 1 and all(n % d for d in range(2, n))
def tests(qmax):
    ps = [2]
    for q in range(3, qmax + 1):
        if isprime(q):
            p, n = ps[-1], len(ps)
            yield p, q, n, p ** (n + 1), q ** n
            ps.append(q)
