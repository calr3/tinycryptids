"""Routines of the design on hand-placed tapes.
 * counter: from Dm on the low marker of C = v (then 00, the gap 00 and a K copy), the
   machine halts if v = 0, else reaches b2 on K's first cell with C = v - 1;
 * loop on R: from s1 on the last cell of R (hole at cell 1, m more cells) the
   machine reaches the mod walk (ma1) with R = 2|R| + 2 cells, hole at cell 1;
 * loop on K: from s1 on the last cell of K (no hole), K gets 2 cells and the copy T
   gets |K| cells (checked at the counter, Dm)."""
import os, sys, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

build.build()
O, S = build.ORDER, build.ST
ok = True

def decode_c(s):
    assert len(s) == 25 and all(s[5 * g + 4] == '1' for g in range(5)), s
    return sum(int(s[5 * g:5 * g + 4], 2) << (4 * (4 - g)) for g in range(5))

vals = list(range(0, 300)) + [16 * i for i in range(1, 300)] + [256 * i for i in range(1, 256)] \
    + [4096 * i for i in range(1, 256)] + [65536 * i for i in range(1, 16)] + [254599, 2**20 - 1] \
    + random.Random(1).sample(range(2**20), 300)
bad = 0
for v in vals:
    pad = '0' * 8
    tape = pad + build.counter_cells(v) + '00' + '00' + '1' * 9 + '00' + '1' * 9
    r = tm.run(O, S, start='Dm', tape=tape, head=len(pad) + 24, maxsteps=10**5, trace='b2', maxtrace=1)
    if v == 0:
        good = r[0] == 'halt'
    else:
        st, _, q, h, t, _ = r
        c = t[:h - 2].rjust(25, '0')[-25:]      # C ends 3 cells left of the head
        good = st == 'traced' and decode_c(c) == v - 1
    if not good: bad += 1; print('counter FAIL', v, r[:5])
print('counter:', len(vals), 'values', 'OK' if not bad else 'FAIL'); ok &= not bad

bad = 0
for m in range(0, 40):
    X = '1' * 5 + '00' + '10111' + '00'            # K, separator, D = 3 (hole at cell 1)
    R = '10' + '1' * m
    tape = X + R
    r = tm.run(O, S, start='s1', tape=tape, head=len(tape) - 1 if m else len(X) + 1,
               maxsteps=10**6, trace='ma1', maxtrace=1)
    st, _, q, h, t, _ = r
    Rn = t.split('00')[-1]
    good = st == 'traced' and Rn == '10' + '1' * (2 * len(R)) and t.startswith(X)
    if not good: bad += 1; print('loop R FAIL', m, r[:5])
print('loop on R: m = 0 .. 39', 'OK' if not bad else 'FAIL'); ok &= not bad

bad = 0
for K in range(1, 40):
    C = build.counter_cells(5)
    tape = C + '00' + '1' * K
    r = tm.run(O, S, start='s1', tape=tape, head=len(tape) - 1, maxsteps=10**6, trace='Dm', maxtrace=1)
    st, _, q, h, t, _ = r
    Ct = C.lstrip('0')                             # the printed tape drops leading 0s
    good = st == 'traced' and t == Ct + '0000' + '1' * K + '00' + '1' * K and h == len(Ct) - 1
    if not good: bad += 1; print('loop K FAIL', K, r[:5])
print('loop on K: |K| = 1 .. 39', 'OK' if not bad else 'FAIL'); ok &= not bad
print('ALL OK' if ok else 'FAILURES')
