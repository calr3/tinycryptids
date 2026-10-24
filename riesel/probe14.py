import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm
BASE = os.path.dirname(os.path.abspath(__file__))
ORDER, ST, _ = tm.parse(open(os.path.join(BASE, 'riesel.txt')).read())
class C:
    def __init__(self, q, left, right):
        self.q = q; self.t = {i: c for i, c in enumerate(right)}
        for i, c in enumerate(left): self.t[-1 - i] = c
        self.h = 0
    def step(self):
        t = ST[self.q][self.t.get(self.h, 0)]
        if t is None: return False
        w, d, q = t
        self.t[self.h] = w
        self.h += 1 if d == 'R' else -1
        self.q = q
        return True
    def cfg(self):
        return (self.q, ''.join(str(self.t.get(-1 - i, 0)) for i in range(8)),
                ''.join(str(self.t.get(i, 0)) for i in range(8)), self.h)
def cfgL(q, s, R):
    return C(q, s[1:], [s[0]] + R)
c = cfgL('PM1', [0, 0, 0, 1, 1, 1, 0, 0], [1, 1])
for i in range(4):
    print(i, c.cfg())
    c.step()
