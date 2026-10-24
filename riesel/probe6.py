"""Check dfin on the Riesel machine: from the t1 configuration of the loop on R,
find the resulting MW shape r as a function of m."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm

BASE = os.path.dirname(os.path.abspath(__file__))
order, ST, _ = tm.parse(open(os.path.join(BASE, 'riesel.txt')).read())

def put(tape, h, cells):
    """write the stream `cells` (list of 0/1) starting at h going right"""
    for i, c in enumerate(cells):
        tape[h + i] = c

def putL(tape, h, cells):
    """write the left stream with cells[0] AT h, going left: cell h-i = cells[i]"""
    for i, c in enumerate(cells):
        tape[h - i] = c

def run(tape, h, q, maxsteps):
    for n in range(maxsteps):
        b = tape.get(h, 0)
        t = ST[q][b]
        if t is None: return ('undef', q, h, tape)
        w, d, nq = t
        tape[h] = w
        h += 1 if d == 'R' else -1
        q = nq
        if q not in ST: return ('halt', q, h, tape)
    return ('limit', q, h, tape)

# Y = F ::: YR Y with Y = ones 7 (F ::: C) where C = Cs of anything; use C = 1
YR = lambda Y: [0, 0, 0, 1, 1, 1, 0] + Y

for m in range(0, 5):
    Y = [1] * 7 + [0] + [1] * 25   # a stand-in for XK 3 v (7 ones, sep, C)
    tape = {}
    h = 0
    put(tape, h, [0, 0] + [1] * m + [0] + [1] * m)
    putL(tape, h, YR(Y))
    st, q, h2, t2 = run(tape, h, 't1', 10**5)
    lo = min([0] + list(t2) + [h2]) - 1
    hi = max([0] + list(t2) + [h2]) + 1
    s = ''.join('1' if t2.get(i, 0) else '0' for i in range(lo, hi + 1))
    # find the head position relative to the D region: print runs with head
    out, i = [], 0
    while i < len(s):
        j = i
        while j < len(s) and s[j] == s[i]: j += 1
        tag = f'*[H{h2}]' if i + lo <= h2 < j + lo else ''
        out.append(f'{s[i]}{j - i}@{i + lo}{tag}')
        i = j
    print('m =', m, st, q, '|', ' '.join(out))
