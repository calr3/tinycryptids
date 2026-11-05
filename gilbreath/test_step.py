"""One step of the update on hand-placed tapes (the configuration CA of Queue.lean):
    Z = H(z) 00 L = H(x) (cursor at cell 1) 00 mid B (y + 2 cells) 0000 1
started in a1 on L's hole; at the end of the step (state s2) B must be erased and
Z = H(z') with z' = |x - y|, L = 1^(x+1) 0 1 (its cursor at the last position)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

def H(v): return '10' + '1' * (v + 1)

ok = True
n = 0
build.build()
mids = ['100', '11100' + '0100', '111000' + '100' + '1111000']   # [M], P(1) M, ...
for x in range(0, 9):
    for y in range(0, 9):
        for mid in mids:
            tape = H(0) + '00' + H(x) + '00' + mid + '1' * (y + 2) + '0000' + '1'
            head = len(H(0)) + 2 + 1
            r = tm.run(build.ORDER, build.ST, start='a1', tape=tape, head=head, maxsteps=10**6,
                       trace='s2', maxtrace=1)
            want = H(abs(x - y)) + '00' + '1' * (x + 1) + '01' + '00' + mid.rstrip('0')
            t = r[4]
            good = r[0] == 'traced' and t.startswith(want) and t[len(want):].strip('0') == '1'
            n += 1
            if not good:
                print('FAIL', x, y, mid, r[0], r[4], want); ok = False
print(n, 'tapes:', 'ALL OK' if ok else 'FAILURES')
