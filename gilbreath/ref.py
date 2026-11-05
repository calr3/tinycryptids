"""Python reference for the tests: the stored diagonal S and the gap g."""
import re

def is_prime(n): return n >= 2 and all(n % d for d in range(2, int(n ** .5) + 1))

def ext(S, g):
    out = [g]
    for e in S:
        g = abs(g - e); out.append(g)
    return out

def reference(S, g, m, target, count):
    """states at the rebuild after each candidate m+1, m+2, ...; and the halting m"""
    S = list(S); out = []
    while len(out) < count:
        m += 1
        if is_prime(m):
            S = ext(S, g)
            if S[-1] != target: return out, m
            g = 1
        else:
            g += 1
        out.append((g, list(S), m))
    return out, None

def parse(tr):
    """G, S (math order) and m = d + r from a tape at c2"""
    tr = tr.strip('0')
    blocks = re.split('0000+', tr)
    q, trial = blocks[0], blocks[-1]
    parts = re.split('00+', q)
    G, M, S = parts[0], parts[1], parts[2:]
    assert G.startswith('10') and set(G[2:]) == {'1'} and M == '1', tr
    assert all(set(b) == {'1'} for b in S), tr
    return len(G) - 3, [len(b) - 2 for b in reversed(S)], len(trial.replace('0', '')) - 4

