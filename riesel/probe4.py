"""Dump checkpoint configurations as runs with absolute positions."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm

BASE = os.path.dirname(os.path.abspath(__file__))
order, ST, _ = tm.parse(open(os.path.join(BASE, 'riesel.txt')).read())

def cfg_runs(tape, h):
    lo = min([0] + list(tape) + [h]) - 1
    hi = max([0] + list(tape) + [h]) + 1
    s = ''.join('1' if tape.get(i, 0) else '0' for i in range(lo, hi + 1))
    out, i = [], 0
    while i < len(s):
        j = i
        while j < len(s) and s[j] == s[i]: j += 1
        tag = ''
        if i + lo <= h < j + lo: tag = f'*H{h}' if False else f'*[H{h}]'
        out.append(f'{s[i]}{j - i}@{i + lo}{tag}')
        i = j
    return ' '.join(out)

def run(maxsteps, watch, limit=5):
    tape, h, q = {}, 0, order[0]
    ev = {k: [] for k in watch}
    for n in range(maxsteps):
        if q in watch and len(ev[q]) < limit:
            ev[q].append((n, q, h, cfg_runs(tape, h)))
        b = tape.get(h, 0)
        t = ST[q][b]
        if t is None: return ev, ('undefined', n, q)
        w, d, nq = t
        tape[h] = w
        h += 1 if d == 'R' else -1
        q = nq
        if q not in ST: return ev, ('halt', n, q)
    return ev, ('limit', maxsteps, q)

ev, st = run(3 * 10**5, ('t1', 'a6', 'ma1'), limit=6)
print(st)
for k, v in ev.items():
    print('===', k)
    for n, q, h, s in v:
        print(f'  n={n} {s}')
