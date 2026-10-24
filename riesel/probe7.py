"""From the s1 config of the composite path (X = R, m cells), check the a6/ma1 shape."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm

BASE = os.path.dirname(os.path.abspath(__file__))
order, ST, _ = tm.parse(open(os.path.join(BASE, 'riesel.txt')).read())

def run(tape, h, q, maxsteps, stop):
    for n in range(maxsteps):
        if q in stop:
            return ('stop', q, h, dict(tape), n)
        b = tape.get(h, 0)
        t = ST[q][b]
        if t is None: return ('undef', q, h, tape, n)
        w, d, nq = t
        tape[h] = w
        h += 1 if d == 'R' else -1
        q = nq
        if q not in ST: return ('halt', q, h, tape, n)
    return ('limit', q, h, tape, maxsteps)

def runs(tape, h):
    lo = min([0] + list(tape) + [h]) - 1
    hi = max([0] + list(tape) + [h]) + 1
    s = ''.join('1' if tape.get(i, 0) else '0' for i in range(lo, hi + 1))
    out, i = [], 0
    while i < len(s):
        j = i
        while j < len(s) and s[j] == s[i]: j += 1
        tag = f'*[H{h}]' if i + lo <= h < j + lo else ''
        out.append(f'{s[i]}{j - i}@{i + lo}{tag}')
        i = j
    return ' '.join(out)

YR = lambda Y: [0, 0, 0, 1, 1, 1, 0] + Y
for m in (0, 1, 2, 3, 6):
    Y = [1] * 7 + [0] + [1] * 25       # XK 3 with a fake C
    tape, h = {}, 0
    # left stream at s1: ones m, then the 0 that s1 will read, then YR Y
    left = [1] * m + [0] + YR(Y)
    for i, c in enumerate(left):
        tape[h - 1 - i] = c
    st, q, h2, t2, n = run(tape, h, 's1', 10**6, {'ma1', 'a6'})
    print(f'm={m} -> {st} {q} steps={n} | {runs(t2, h2)}')
