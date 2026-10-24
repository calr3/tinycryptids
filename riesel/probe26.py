"""Step-by-step dump (state, head, tape runs) of the Riesel design around the
composite rounds; absolute cell numbers."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build

build.build(c0=2)
order, ST = build.ORDER, build.ST

class C:
    def __init__(self):
        self.q = order[0]; self.t = {}; self.h = 0
    def step(self):
        tr = ST[self.q][self.t.get(self.h, 0)]
        if tr is None: return False
        w, d, q = tr
        self.t[self.h] = w
        self.h += 1 if d == 'R' else -1
        self.q = q
        return True
    def runs(self):
        lo = min(list(self.t) + [self.h]) - 1
        hi = max(list(self.t) + [self.h]) + 1
        s = ''.join('1' if self.t.get(i, 0) else '0' for i in range(lo, hi + 1))
        out, i = [], 0
        while i < len(s):
            j = i
            while j < len(s) and s[j] == s[i]: j += 1
            out.append(f'{s[i]}^{j - i}@{i + lo}')
            i = j
        return ' '.join(out)

c = C()
lo, hi = 380, 445
for n in range(hi):
    if n >= lo:
        print(f'{n:5d} {c.q:5s} h={c.h:4d} {c.runs()}')
    if not c.step(): break
