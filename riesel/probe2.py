"""Direct interpreter probes: checkpoints at t1 / a6 / ma1 for the first few k."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm

BASE = os.path.dirname(os.path.abspath(__file__))
order, ST, _ = tm.parse(open(os.path.join(BASE, 'riesel.txt')).read())

def run_steps(maxsteps, watch):
    """watch: state -> callback(cfg) on entry, returning False to stop"""
    tape = {}
    h = 0
    q = order[0]
    for n in range(maxsteps):
        b = tape.get(h, 0)
        t = ST[q][b]
        if t is None:
            return ('undefined', n, q, h, tape)
        if q in watch and not watch[q]((q, h, dict(tape))):
            return ('stopped', n, q, h, tape)
        w, d, nq = t
        tape[h] = w
        h += 1 if d == 'R' else -1
        q = nq
        if q not in ST:
            return ('halt', n, q, h, tape)
    return ('limit', maxsteps, q, h, tape)

def fmt(h, tape):
    lo = min([0] + list(tape)); hi = max([0] + list(tape))
    lo = min(lo, h - 4); hi = max(hi, h + 4)
    return ''.join('1' if tape.get(i, 0) else '0' for i in range(lo, hi + 1)), h - lo

def rle(s, h):
    out, i = [], 0
    while i < len(s):
        j = i
        while j < len(s) and s[j] == s[i]: j += 1
        mark = 'H' if i <= h < j else ('L' if j <= h else 'R')
        out.append(f'{s[i]}^{j - i}{mark}')
        i = j
    return ' '.join(out)

count = [0]
def at(qname):
    def cb(cfg):
        q, h, tape = cfg
        s, hh = fmt(h, tape)
        print(f'{qname} @{h}: {rle(s, hh)}')
        count[0] += 1
        return count[0] < 120
    return cb

run_steps(10**5, {'t1': at('t1'), 'a6': at('a6'), 'ma1': at('ma1')})
