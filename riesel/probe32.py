"""Dump the tape (runs relative to the head) at every t1 and a6 event of the
real Riesel machine, to pin the KT / a6 geometry."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm

BASE = os.path.dirname(os.path.abspath(__file__))
ORDER, ST, _ = tm.parse(open(os.path.join(BASE, 'riesel.txt')).read())
START = ORDER[0]

def runs(tape, h):
    cells = list(tape) + [h]
    lo, hi = min(cells), max(cells)
    s = ''.join('1' if tape.get(i, 0) else '0' for i in range(lo, hi + 1))
    out, i = [], 0
    while i < len(s):
        j = i
        while j < len(s) and s[j] == s[i]:
            j += 1
        out.append(f'{s[i]}^{j - i}@{i + lo - h}')
        i = j
    return ' '.join(out)

tape, h, q = {}, 0, START
ev = 0
for n in range(200000):
    if q in ('t1', 'a6') and ev < 12:
        print(f'{q:3s} step {n:6d} h={h}: {runs(tape, h)}')
        ev += 1
    t = ST[q][tape.get(h, 0)]
    if t is None:
        print('halt', q, 'at', n)
        break
    w, d, nq = t
    tape[h] = w
    h += 1 if d == 'R' else -1
    q = nq
