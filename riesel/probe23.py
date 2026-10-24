import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build

build.build()
order, ST = build.ORDER, build.ST

def grp(u, s):
    return [1, u % 2, u // 2 % 2, u // 4 % 2, u // 8 % 2] + s
def cs(v):
    s = []
    for sh in (0, 4, 8, 12, 16):
        s = grp(v >> sh & 15, s)
    return s

Y = [1] * 4 + [0] + cs(254598)   # XK 3-ish (K = 4 for readability)
m = 1
s = [0, 0, 0, 1, 1, 1, 0] + Y
R = [0, 0] + [1] * m + [0] + [1] * m
tape = {}
for i, c in enumerate(R): tape[i] = c
for i, c in enumerate(s[1:]): tape[-1 - i] = c
h, q = 0, 't1'
print('start right:', ''.join(str(tape.get(i, 0)) for i in range(0, 16)))
for n in range(60):
    if q == 'ma1':
        print('reached ma1 at step', n, 'h =', h); break
    t = ST[q][tape.get(h, 0)]
    if t is None:
        print('undef at', q, 'step', n, 'cell', tape.get(h, 0), 'h', h); break
    print(n, q, 'reads', tape.get(h, 0), 'h', h, '->', t)
    w, d, nq = t
    tape[h] = w
    h += 1 if d == 'R' else -1
    q = nq
