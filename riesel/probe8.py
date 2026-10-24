"""dfin check with a valid counter stream."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm

BASE = os.path.dirname(os.path.abspath(__file__))
order, ST, _ = tm.parse(open(os.path.join(BASE, 'riesel.txt')).read())

def grp(u, s):
    return [1, u % 2, u // 2 % 2, u // 4 % 2, u // 8 % 2] + s

def cs(v):
    s = []
    for sh in (0, 4, 8, 12, 16):
        s = grp(v >> sh & 15, s)
    return s

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

def mw_shape(tape, h):
    """given head at ma1 on D's hole home: count zeros after head etc."""
    return runs(tape, h)

# 1) the t1 config of dfin, for k = 5, v = 254598 (valid C), m = k - 4 = 1
for (k, v, m) in ((5, 254598, 1), (7, 254596, 3), (5, 254598, 0)):
    Y = [1] * (k + 4) + [0] + cs(v)
    tape, h = {}, 0
    right = [0, 0] + [1] * m + [0] + [1] * m
    for i, c in enumerate(right):
        tape[h + i] = c
    left = YR(Y)
    for i, c in enumerate(left):
        tape[h - 1 - i] = c
    st, q, h2, t2, n = run(tape, h, 't1', 10**6, {'ma1'})
    print(f't1 k={k} m={m}: {st} {q} steps={n}')
    print('   ', runs(t2, h2))

# 2) the s1 config of the composite path: X = R = m cells, then 0, then YR Y
for (k, v, m) in ((5, 254598, 6),):
    Y = [1] * (k + 4) + [0] + cs(v)
    tape, h = {}, 0
    left = [1] * m + [0] + YR(Y)
    for i, c in enumerate(left):
        tape[h - 1 - i] = c
    st, q, h2, t2, n = run(tape, h, 's1', 10**6, {'ma1'})
    print(f's1 k={k} m={m}: {st} {q} steps={n}')
    print('   ', runs(t2, h2))
