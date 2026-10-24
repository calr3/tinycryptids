"""Dump the tape around the head at every ma1 event of a small variant."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build

build.build(c0=0, nf=1)
ST, ORDER = build.ST, build.ORDER

def get(t, i):
    return t.get(i, 0)

def dump(tape, h, lo, hi):
    return ''.join('[.]' if i == h and not get(tape, i) else
                   '[1]' if i == h else
                   ('1' if get(tape, i) else '.') for i in range(lo, hi + 1))

tape, h, q = {}, 0, ORDER[0]
step = 0
seen = 0
while step < 4000:
    t = ST[q][tape.get(h, 0)]
    if t is None:
        print(f'step {step}: HALT in {q}')
        break
    w, d, nq = t
    if q == 'ma1' and seen < 8:
        print(f'step {step}: ma1 h={h}')
        print('   ', dump(tape, h, h - 14, h + 14))
        print('    idx  ', ''.join(str(abs((i - h) // 10) % 10) for i in range(h - 14, h + 15)))
        print('    idx  ', ''.join(str(abs(i - h) % 10) for i in range(h - 14, h + 15)))
        seen += 1
    tape[h] = w
    h += 1 if d == 'R' else -1
    q = nq
    step += 1
