import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))  # tm.py
import build, tm
from itertools import product
build.build()
st = {k: list(v) for k, v in build.ST.items()}
st['su0'] = [(0, 'R', 'en2'), None]          # skip the power computation
order = build.ORDER
r = tm.run(order, st, maxsteps=3*10**8, trace='su0', maxtrace=40000)
seen = []
for t in r[5]:
    blocks = [len(b) for b in t.strip('0').split('00') if b]
    assert len(blocks) == 6 and blocks[4:] == [1, 2], (t, blocks)
    seen.append(tuple([blocks[0]-2] + [b-2 for b in blocks[1:4]]))
print(r[:3], len(seen), seen[:12])
s = set(seen)
for N in range(8, 40):
    want = {c for c in product(range(1, N), repeat=4) if sum(c) == N and c[0] >= 3}
    if not want <= s:
        print('first incomplete total', N, len(want - s)); break
else: print('complete')
