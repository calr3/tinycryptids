import sys
from build import build
from ref import first_barker
def run(n0, maxsteps=10**8):
    order, st = build(n0)
    tape = {}; h = 0; q = order[0]; steps = 0
    while steps < maxsteps:
        if q not in st: break
        t = st[q][tape.get(h, 0)]
        if t is None: break
        w, d, n = t
        tape[h] = w; h += 1 if d == 'R' else -1; q = n; steps += 1
    lo, hi = min(tape), max(tape)
    s = ''.join(str(tape.get(i, 0)) for i in range(lo, hi + 1))
    return q, steps, s
if __name__ == '__main__':
    for n0 in range(2, 14):
        q, steps, s = run(n0)
        exp = first_barker(n0)
        x = s.strip('0')
        print(n0, q, steps, s, exp)
