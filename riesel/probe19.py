import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

build.build(c0=0)
order, ST = build.ORDER, build.ST
tape, h, q = {}, 0, order[0]
prev = None
for n in range(1200):
    if q in ('t1', 'a6', 'ma1', 'b2', 'g1', 's4', 's1'):
        if (q, n) != prev:
            lo = min(list(tape) + [h]) - 1
            hi = max(list(tape) + [h]) + 1
            s = ''.join('1' if tape.get(i, 0) else '0' for i in range(lo, hi + 1))
            print(n, q, 'h=', h, s.strip('0'), '| str=', s)
        prev = (q, n)
    t = ST[q][tape.get(h, 0)]
    if t is None:
        print('HALT', n, q); break
    w, d, nq = t
    tape[h] = w
    h += 1 if d == 'R' else -1
    q = nq
