"""At each t1 event, check whether the config is a KT checkpoint (right of the
head: 0,0, b ones, 0, b ones, blank) and decode b and the counter v."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build

c0 = int(sys.argv[1]) if len(sys.argv) > 1 else 0
build.build(c0=c0, nf=1)
ST, ORDER = build.ST, build.ORDER

def get(t, i):
    return t.get(i, 0)

def isone(t, i):
    return get(t, i) == 1

def counter_value(t, h):
    # head on C's lowest marker; left: bit0..bit3, then marker of the next group, ...
    v = 0
    for g in range(5):
        base = h - 1 - 5 * g
        # base = bit0 of group g
        u = 0
        for b in range(4):
            if isone(t, base - b):
                u += 1 << b
        v += u * (16 ** g)
        # marker at base - 4 should be 1
        assert isone(t, base - 4) or g == 4, (g, base)
    return v

def kt(t, h):
    if get(t, h) != 1:
        return None
    if get(t, h + 1) or get(t, h + 2):
        return None
    b = 0
    while isone(t, h + 3 + b):
        b += 1
    if get(t, h + 3 + b):
        return None
    b2 = 0
    while isone(t, h + 4 + b + b2):
        b2 += 1
    if get(t, h + 4 + b + b2) or get(t, h + 5 + b + b2):
        return None
    if b != b2:
        return None
    return b

tape, h, q = {}, 0, ORDER[0]
step = 0
while step < 3000:
    t = ST[q][tape.get(h, 0)]
    if t is None:
        print(f'step {step}: HALT in {q}')
        break
    if q == 't1':
        b = kt(tape, h)
        if b is not None:
            print(f'step {step}: KT b={b} v={counter_value(tape, h)}')
    w, d, nq = t
    tape[h] = w
    h += 1 if d == 'R' else -1
    q = nq
    step += 1
