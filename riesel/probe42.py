"""Dump the head neighbourhood at every t1 (and ma1) event of the standard
machine (small c0) so the block geometry can be read off directly."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build

c0 = int(sys.argv[1]) if len(sys.argv) > 1 else 3
build.build(c0=c0, nf=1)
ST, ORDER = build.ST, build.ORDER

def get(t, i):
    return t.get(i, 0)

def dump(t, h, lo=-8, hi=26):
    idx = ''.join(str(abs(i) // 10 % 10) if i < 0 else str(i // 10 % 10) for i in range(lo, hi + 1))
    one = ''.join(str(abs(i) % 10) for i in range(lo, hi + 1))
    s = ''.join(('[' + ('1' if get(t, i) else '.') + ']') if i == h else ('1' if get(t, i) else '.')
                for i in range(lo, hi + 1))
    return f'{idx}\n{one}\n{s}'

tape, h, q = {}, 0, ORDER[0]
step = 0
ev = 0
while step < 100000:
    t = ST[q][tape.get(h, 0)]
    if t is None:
        print(f'step {step}: HALT in {q}')
        break
    if q in ('t1', 'ma1'):
        print(f'--- step {step} state {q} event {ev}')
        print(dump(tape, h))
        ev += 1
        if ev > 26:
            break
    w, d, nq = t
    tape[h] = w
    h += 1 if d == 'R' else -1
    q = nq
    step += 1
