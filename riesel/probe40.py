"""At each ma1 event with the R hole at cell 0 and the D hole home, decode
(d, r) and the K length and the counter value, and print the implied P."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build

c0 = int(sys.argv[1]) if len(sys.argv) > 1 else 3
build.build(c0=c0, nf=1)
ST, ORDER = build.ST, build.ORDER

def get(t, i):
    return t.get(i, 0)

def counter_value(t, h):
    # head on C's lowest marker
    v = 0
    for g in range(5):
        base = h - 1 - 5 * g
        u = sum((1 << b) for b in range(4) if get(t, base - b))
        v += u * (16 ** g)
    return v

def walk_start(t, h):
    # head on D's hole, h = d, j = 0: right = 0,0,0 then r+1 ones then blank
    i = h + 1
    z = 0
    while not get(t, i):
        z += 1; i += 1
    if z != 3:
        return None
    r1 = 0
    while get(t, i):
        r1 += 1; i += 1
    if get(t, i + 1) or get(t, i + 2) or get(t, i + 3):
        return None
    # left: h ones, then a 0, then K ones, then 0, then C
    l = 0
    while get(t, h - 1 - l):
        l += 1
    if get(t, h - 1 - l) or l != z + r1 - 3:   # d = h and d = r1? no; d from context
        pass
    kk = 0
    j = h - 1 - l - 1
    while get(t, j - kk):
        kk += 1
    base = j - kk - 1
    v = counter_value(t, base)
    return z, r1, l, kk, v

tape, h, q = {}, 0, ORDER[0]
step = 0
while step < 200000:
    t = ST[q][tape.get(h, 0)]
    if t is None:
        print(f'step {step}: HALT in {q}')
        break
    if q == 'ma1':
        w = walk_start(tape, h)
        if w is not None:
            z, r1, l, kk, v = w
            print(f'step {step}: d={l} r={r1 - 1} P={l + r1} K={kk} v={v}')
    w, d, nq = t
    tape[h] = w
    h += 1 if d == 'R' else -1
    q = nq
    step += 1
