"""KT configs in the Sierpinski machine (for comparison)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build

build.build(c0=3)
order, ST = build.ORDER, build.ST
tape, h, q = {}, 0, order[0]

def cval(cell0, ng):
    bits = [tape.get(cell0 - i, 0) for i in range(5 * ng)]
    v = 0
    for g in range(ng):
        assert bits[5 * g] == 1, (g, bits)
        v += sum(bits[5 * g + 1 + b] << b for b in range(4)) << (4 * g)
    return v

seen = 0
for n in range(2 * 10**6):
    if q == 't1' and tape.get(h, 0) == 1:
        c = cval(h, 4)
        a = 0
        while tape.get(h + 3 + a, 0) == 1: a += 1
        b = 0
        while tape.get(h + 4 + a + b, 0) == 1: b += 1
        print('step', n, 'c =', c, 'blocks', a, b)
        seen += 1
        if seen >= 4: break
    t = ST[q][tape.get(h, 0)]
    if t is None: break
    w, d, nq = t
    tape[h] = w
    h += 1 if d == 'R' else -1
    q = nq
