"""At each ma1 checkpoint of the real machine: runs relative to the head."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm

BASE = os.path.dirname(os.path.abspath(__file__))
ORDER, ST, _ = tm.parse(open(os.path.join(BASE, 'riesel.txt')).read())


class C:
    def __init__(self, q):
        self.q, self.t, self.h = q, {}, 0

    def step(self):
        tr = ST[self.q][self.t.get(self.h, 0)]
        if tr is None:
            return False
        w, d, q = tr
        self.t[self.h] = w
        self.h += 1 if d == 'R' else -1
        self.q = q
        return True

    def runs(self):
        cells = list(self.t) + [self.h]
        lo, hi = min(cells), max(cells)
        s = ''.join('1' if self.t.get(i, 0) else '0' for i in range(lo, hi + 1))
        out, i = [], 0
        while i < len(s):
            j = i
            while j < len(s) and s[j] == s[i]:
                j += 1
            out.append(f'{s[i]}^{j - i}@{i + lo - self.h}')
            i = j
        return ' '.join(out)


c = C('seed0')
seen = 0
for n in range(300000):
    if c.q == 'ma1':
        print(f'--- ma1 #{seen} at step {n}')
        print('   ', c.runs())
        seen += 1
        if seen >= 12:
            break
    if not c.step():
        print('halted at', n, c.q)
        break
