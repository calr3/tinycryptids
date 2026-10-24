"""Check CK k n v -> next CK (composite doubling) and -> t1 (prime), from built tapes."""
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
    d, h, j = 3, 3, 0
    r = k * 2 ** n - 5
    Y = [1] * (k + 4) + [0] + cs(v)
    left = [1] * h + [0] + Y
    right = [0] + [1] * (d - h) + [0, 0] + [1] * j + [0] + [1] * (r + 1 - j)
    tape = {}
    for i, c in enumerate(right): tape[i] = c
    for i, c in enumerate(left): tape[-1 - i] = c
    return tape, 0

def run(tape, h, q, maxsteps, stop):
    for n in range(maxsteps):
        if q in stop: return ('stop', q, h, dict(tape), n)
        b = tape.get(h, 0)
        t = ST[q][b]
        if t is None: return ('undef', q, h, tape, n)
        w, d, nq = t
        tape[h] = w
        h += 1 if d == 'R' else -1
        q = nq
        if q not in ST: return ('halt', q, h, tape, n)
    return ('limit', q, h, tape, maxsteps)

def shape(tape, h):
    """describe the tape as runs relative to the head"""
    out, i = [], 0
    lo = min([0] + list(tape) + [h]) - 1
    hi = max([0] + list(tape) + [h]) + 1
    s = ''.join('1' if tape.get(i, 0) else '0' for i in range(lo, hi + 1))
    while i < len(s):
        j = i
        while j < len(s) and s[j] == s[i]: j += 1
        out.append(f'{s[i]}{j - i}[{i + lo - h}]')
        i = j
    return ' '.join(out)

v = 254598
t, h = ck(5, 1, v)
st, q, h2, t2, n = run(t, h, 'ma1', 10**8, {'ma1', 't1'})
print('composite ->', st, q, n)
print('  ', shape(t2, h2))

t, h = ck(5, 2, v)
st, q, h2, t2, n = run(t, h, 'ma1', 10**8, {'ma1', 't1'})
print('prime ->', st, q, n)
print('  ', shape(t2, h2))
