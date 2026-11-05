"""One round from a hand-placed tape, for every x < N: the tape at the start of a
round (as in the Lean `RD x G`): D with its hole at d10 (p = 9), 00, X (x + 3 cells,
hole at cell 1), G zeros, A (one cell); the head on D's hole in state fA.
The round must halt iff rev10 x = x, and otherwise reach the next round (state ix3
traced) with X = x + rev10 x cells + 3."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

def rev10(n): return int(str(n)[::-1])

N = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
build.build()
ok = True
for x in range(N):
    for G in (2, 5):
        tape = '1' * 10 + '0' + '1' + '00' + '1' + '0' + '1' * (x + 1) + '0' * G + '1'
        r = tm.run(build.ORDER, build.ST, start='fA', tape=tape, head=10, maxsteps=10**8,
                   trace='ix3', maxtrace=1)
        if rev10(x) == x:
            good = r[0] == 'halt' and not r[5]
        else:
            tr = r[5][0].lstrip('0') if r[5] else ''
            good = bool(tr) and tr[:14] == '1' * 10 + '0' + '100' and \
                tr[14:].split('0')[0] == '1' * (x + rev10(x) + 3)
        if not good:
            print('FAIL', x, G, r[:3]); ok = False
print(f'rounds for x < {N}:', 'ALL OK' if ok else 'FAILURES')
