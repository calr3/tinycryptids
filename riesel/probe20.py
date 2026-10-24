import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build

build.build(c0=0)
order, ST = build.ORDER, build.ST
tape, h, q = {}, 0, order[0]
want = {134: 't1', 155: 't1', 160: 'a6', 147: 'g1', 138: 'b2'}
for n in range(170):
    if n in want:
        lo = min(list(tape) + [h]) - 1
        hi = max(list(tape) + [h]) + 1
        s = ''.join('1' if tape.get(i, 0) else '0' for i in range(lo, hi + 1))
        print(n, q, 'h=', h)
        print('  ', ''.join(str((i + lo) % 10) for i in range(len(s))))
        print('  ', s)
    t = ST[q][tape.get(h, 0)]
    if t is None: break
    w, d, nq = t
    tape[h] = w
    h += 1 if d == 'R' else -1
    q = nq
