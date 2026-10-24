"""Dump the real machine's t1 checkpoints and the first candidate at ma1/a6."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm

BASE = os.path.dirname(os.path.abspath(__file__))
ORDER, ST, _ = tm.parse(open(os.path.join(BASE, 'riesel.txt')).read())

tape, h, q = {}, 0, ORDER[0]
t1s, mas = [], []
prev_t1 = None
for n in range(200000):
    if q == 't1':
        sig = tuple(sorted((i - h, c) for i, c in tape.items()))
        if sig != prev_t1:
            prev_t1 = sig
            t1s.append((n, h, dict(tape)))
    if q == 'ma1' and (not mas or mas[-1][0] != n - 1):
        mas.append((n, h, dict(tape)))
    t = ST[q][tape.get(h, 0)]
    if t is None:
        print('halt at', n, q); break
    w, d, nq = t
    tape[h] = w
    h += 1 if d == 'R' else -1
    q = nq
    if len(t1s) >= 6 and len(mas) >= 3: break

def runs(tape, h):
    lo = min(list(tape) + [h]) - 1
    hi = max(list(tape) + [h]) + 1
    s = ''.join('1' if tape.get(i, 0) else '0' for i in range(lo, hi + 1))
    out, i = [], 0
    while i < len(s):
        j = i
        while j < len(s) and s[j] == s[i]: j += 1
        out.append(f'{s[i]}^{j - i}@{i + lo - h}')
        i = j
    return ' '.join(out)

for n, h, t in t1s[:6]:
    print('t1 @', n, runs(t, h))
for n, h, t in mas[:3]:
    print('ma1 @', n, runs(t, h))
