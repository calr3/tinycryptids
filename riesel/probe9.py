"""End-to-end check of the Lean-style stream construction: CK k 1 v -> CK k 2 v."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm

BASE = os.path.dirname(os.path.abspath(__file__))
order, ST, _ = tm.parse(open(os.path.join(BASE, 'riesel.txt')).read())

def grp(u, s):
    return [1, u % 2, u // 2 % 2, u // 4 % 2, u // 8 % 2] + s

def cs(v):
    s = []
    for sh in (0, 4, 8, 12, 16):
        s = grp(v >> sh & 15, s)
    return s

def ck(k, n, v):
    """tape of MW (XK k v) 3 (k*2^n - 5) 3 0, head index 0"""
    d, h, j = 3, 3, 0
    r = k * 2 ** n - 5
    Y = [1] * (k + 4) + [0] + cs(v)
    left = [1] * h + [0] + Y
    right = [0] + [1] * (d - h) + [0, 0] + [1] * j + [0] + [1] * (r + 1 - j)
    tape = {}
    for i, c in enumerate(right):
        tape[i] = c
    for i, c in enumerate(left):
        tape[-1 - i] = c
    return tape, 0

def run(tape, h, q, maxsteps, stop):
    for n in range(maxsteps):
        if q in stop:
            return ('stop', q, h, dict(tape), n)
        b = tape.get(h, 0)
        t = ST[q][b]
        if t is None: return ('undef', q, h, tape, n)
        w, d, nq = t
        tape[h] = w
        h += 1 if d == 'R' else -1
        q = nq
        if q not in ST: return ('halt', q, h, tape, n)
    return ('limit', q, h, tape, maxsteps)

def runs(tape, h):
    lo = min([0] + list(tape) + [h]) - 1
    hi = max([0] + list(tape) + [h]) + 1
    s = ''.join('1' if tape.get(i, 0) else '0' for i in range(lo, hi + 1))
    out, i = [], 0
    while i < len(s):
        j = i
        while j < len(s) and s[j] == s[i]: j += 1
        tag = f'*[H{h}]' if i + lo <= h < j + lo else ''
        out.append(f'{s[i]}{j - i}@{i + lo}{tag}')
        i = j
    return ' '.join(out)

v = 254598
for (k, n, expect) in ((5, 1, 'composite then prime'),):
    tape, h = ck(k, n, v)
    st, q, h2, t2, steps = run(tape, h, 'ma1', 10**7, {'a6', 't1', 'e3'})
    print(f'k={k} n={n}: {st} {q} steps={steps} ({expect})')
    print('   ', runs(t2, h2))
