"""Dump every checkpoint of small variants (c0 = 0, 1) with decoded runs."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

def runs(tape, h):
    cells = list(tape) + [h]
    lo, hi = min(cells), max(cells)
    s = ''.join('1' if tape.get(i, 0) else '0' for i in range(lo, hi + 1))
    out, i = [], 0
    while i < len(s):
        j = i
        while j < len(s) and s[j] == s[i]: j += 1
        out.append(f'{s[i]}^{j-i}@{i+lo-h}')
        i = j
    return ' '.join(out)

EVENTS = {'t1', 'a6', 'a4b', 'a4', 'a5', 'a5b', 'PM1', 'ma1', 'b2', 'Dm', 'w1'}

def go(c0):
    build.build(c0=c0, nf=1)
    ST, ORDER = build.ST, build.ORDER
    q, tape, h, step = ORDER[0], {}, 0, 0
    print(f'=== c0 = {c0} ===')
    while step < 2 * 10 ** 6:
        t = ST[q][tape.get(h, 0)]
        if t is None:
            print(f'  step {step}: HALT in {q}')
            return
        w, d, q2 = t
        tape[h] = w
        h += 1 if d == 'R' else -1
        q = q2
        step += 1
        if q in EVENTS:
            print(f'  step {step}: {q}  {runs(tape, h)}')
    print('  no halt')

go(0)
go(1)
