"""Step-by-step cell-level simulation of a machine from an abstract config."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build

build.build()
ST = build.ST

# streams: tuples of bools, all-false tail supplied lazily by `at`
def at(s, i):
    return s[i] if i < len(s) else False

def ones(n, s=()):
    return (True,) * n + tuple(s)

def grp(u, s):
    return (True, u % 2 == 1, u // 2 % 2 == 1, u // 4 % 2 == 1, u // 8 % 2 == 1) + tuple(s)

def Cs(v):
    return (grp(v % 16, ()) + grp(v // 16 % 16, ()) + grp(v // 256 % 16, ()) +
            grp(v // 4096 % 16, ()) + grp(v // 65536 % 16, ()))

def YR(Y):
    return (False, False, False, True, True, True, False) + tuple(Y)

def run(L, R, q, n=30):
    L, R = tuple(L), tuple(R)
    for k in range(n):
        print(f'{k:2d} {q:4s} L={"".join("1" if x else "." for x in L[:22])!r:26s} '
              f'head={"1" if at(R,0) else "."} R={"".join("1" if at(R, i) else "." for i in range(1, 16))}')
        t = ST[q][at(R, 0)]
        if t is None:
            print('   HALT'); return
        w, d, q = t
        if d == 'R':
            L, R = (w,) + L, R[1:]
        else:
            L, R = L[1:], (at(L, 0), w) + R[1:]
    return q

Y = ones(7, (False,) + Cs(0))
# cfgL t1 (YR Y) R has left = tl (YR Y) and head cell = (YR Y) 0
print('=== Riesel dfin, m = 0 ===')
s = tuple(YR(Y))
run(s[1:], (s[0],) + (False, False, False), 't1', 16)
print()
print('=== Riesel dfin, m = 1 ===')
run(s[1:], (s[0],) + (False, False, True, False, True, False), 't1', 24)
