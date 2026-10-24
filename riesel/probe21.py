"""KT configs: t1 with the C marker under the head.  Decode blocks and c."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build

build.build()
order, ST = build.ORDER, build.ST
tape, h, q = {}, 0, order[0]

def cval(cell0):
    # C occupies 25 cells ending at the head (the lowest marker); read leftwards
    bits = []
    for i in range(25):
        bits.append(tape.get(cell0 - i, 0))
    # groups: bit0..3, marker, bit4..7, marker, ...
    v = 0
    for g in range(5):
        m = bits[5 * g]
        assert m == 1, (g, m, bits)
        u = sum(bits[5 * g + 1 + b] << b for b in range(4))
        v += u << (4 * g)
    return v

seen = 0
for n in range(2 * 10**6):
    if q == 't1' and tape.get(h, 0) == 1:
        c = cval(h)
        a = 0
        while tape.get(h + 3 + a, 0) == 1: a += 1
        b = 0
        while tape.get(h + 4 + a + b, 0) == 1: b += 1
        print('step', n, 'c =', c, 'blocks', a, b, 'k(guess)', build.C0 - c, 'k+5', 3 + 2 * (build.C0 - c) + 5)
        seen += 1
        if seen >= 4: break
    t = ST[q][tape.get(h, 0)]
    if t is None: break
    w, d, nq = t
    tape[h] = w
    h += 1 if d == 'R' else -1
    q = nq
