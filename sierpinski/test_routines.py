"""Routines of the design on hand-placed tapes.
 * counter: from t1 on the low marker of C = v (then 0, the gap 0, K' and T), the
   machine halts if v = 0, else reaches b2 on the gap with C = v - 1;
 * loop on R: from s1 on the last cell of R (hole at cell 0, m more cells) the
   machine reaches the mod walk (ma1) with R = 2|R| + 1 cells, hole at cell 0;
 * loop on K: from s1 on the last cell of K (no hole), K moves one cell right
   and the copy T gets |K| cells (checked at D0);
 * trial division: from the start of a mod walk (D = 3, hole home) on P, the
   machine reaches the loop on R with P' = 2P - 1 if P is composite, and the
   wipe (w1) with r = 0 if P is prime."""
import os, sys, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

build.build()
O, S = build.ORDER, build.ST
ok = True

def decode_c(s):
    assert len(s) == 20 and all(s[5 * g + 4] == '1' for g in range(4)), s
    return sum(int(s[5 * g:5 * g + 4], 2) << (4 * (3 - g)) for g in range(4))

vals = list(range(0, 300)) + [16 * i for i in range(1, 300)] + [256 * i for i in range(1, 256)] \
    + [4096 * i for i in range(1, 16)] + [39277, 39278, 65535] + random.Random(1).sample(range(65536), 300)
bad = 0
for v in vals:
    pad = '0' * 8
    tape = pad + build.counter_cells(v) + '0' + '0' + '1' * 9 + '0' + '1' * 9
    r = tm.run(O, S, start='t1', tape=tape, head=len(pad) + 19, maxsteps=10**5, trace='b2', maxtrace=1)
    if v == 0:
        good = r[0] == 'halt'
    else:
        st, _, q, h, t, _ = r
        c = t[:h - 1].rjust(20, '0')[-20:]      # C ends 2 cells left of the head
        good = st == 'traced' and decode_c(c) == v - 1 and t[h - 1:h + 1] == '00'
    if not good: bad += 1; print('counter FAIL', v, r[:5])
print('counter:', len(vals), 'values', 'OK' if not bad else 'FAIL'); ok &= not bad

bad = 0
for m in range(0, 40):
    X = '1' * 5 + '0' + '1110' + '00'               # K, separator, D = 3 (hole home)
    R = '0' + '1' * m
    tape = X + R
    r = tm.run(O, S, start='s1', tape=tape, head=len(tape) - 1, maxsteps=10**6, trace='ma1', maxtrace=1)
    st, _, q, h, t, _ = r
    good = st == 'traced' and t == X + '0' + '1' * (2 * len(R))
    if not good: bad += 1; print('loop R FAIL', m, r[:5])
print('loop on R: m = 0 .. 39', 'OK' if not bad else 'FAIL'); ok &= not bad

bad = 0
for K in range(1, 40):
    C = build.counter_cells(5)
    tape = C + '0' + '1' * K
    r = tm.run(O, S, start='s1', tape=tape, head=len(tape) - 1, maxsteps=10**6, trace='D0', maxtrace=1)
    st, _, q, h, t, _ = r
    Ct = C.lstrip('0')                             # the printed tape drops leading 0s
    good = st == 'traced' and t == Ct + '00' + '1' * K + '0' + '1' * K and h == len(Ct) - 2
    if not good: bad += 1; print('loop K FAIL', K, r[:5])
print('loop on K: |K| = 1 .. 39', 'OK' if not bad else 'FAIL'); ok &= not bad

def is_prime(m): return m >= 2 and all(m % d for d in range(2, int(m ** 0.5) + 1))
bad = 0
for P in range(5, 400, 2):
    X = '1' * 5 + '0'
    tape = X + '1110' + '00' + '0' + '1' * (P - 3)    # D = 3, R = P - 3 + 1 cells, hole at 0
    # start as the doubling leaves it: on the gap-filled R, about to look for the D hole
    r = tm.run(O, S, start='PM1', tape=tape, head=len(X) + 5, maxsteps=10**8, trace='s1' if not is_prime(P) else 'w1', maxtrace=1)
    st, _, q, h, t, _ = r
    if is_prime(P):
        good = st == 'traced'
    else:
        good = st == 'traced' and t.startswith(X + '1110000') and t[len(X) + 7:].rstrip('0') == '1' * (P - 3)
    if not good: bad += 1; print('trial FAIL', P, r[:5])
print('trial division: P = 5 .. 399', 'OK' if not bad else 'FAIL'); ok &= not bad
print('ALL OK' if ok else 'FAILURES')
