"""Absolute dump of the first checkpoint configurations (t1, a6, ma1)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm

BASE = os.path.dirname(os.path.abspath(__file__))
order, ST, _ = tm.parse(open(os.path.join(BASE, 'riesel.txt')).read())

def run(maxsteps, watch):
    tape, h, q = {}, 0, order[0]
    ev = {k: [] for k in watch}
    for n in range(maxsteps):
        if q in watch and len(ev[q]) < 8:
            lo = min([0] + list(tape) + [h]) - 2
            hi = max([0] + list(tape) + [h]) + 2
            s = ''.join('1' if tape.get(i, 0) else '0' for i in range(lo, hi + 1))
            ev[q].append((h, s, h - lo, n))
        b = tape.get(h, 0)
        t = ST[q][b]
        if t is None: return ev, ('undefined', n, q)
        w, d, nq = t
        tape[h] = w
        h += 1 if d == 'R' else -1
        q = nq
        if q not in ST: return ev, ('halt', n, q)
    return ev, ('limit', maxsteps, q)

ev, st = run(3 * 10**5, ('t1', 'a6', 'ma1'))
print(st)
for k, v in ev.items():
    print('===', k)
    for h, s, hh, n in v:
        print(f'  n={n} h={h}  {s}')
        print('          ' + ' ' * hh + '^')
