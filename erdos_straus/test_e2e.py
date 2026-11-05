"""End-to-end checks of the design.
 * every mod walk (state ms4: D's last cell, before its home hole is written) is checked against
   the reference search: the tape is A 00 R 00 N 00 M 00 K 00 D 00 P with the values of the
   next pair (n, x, y) with m < ay <= 2m, in order;
 * the variant n0 = 1 halts at n = 1 (4/1 has no solution);
 * the real machine runs 10^8 steps."""
import os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

def reference(n0, rate=4, nohit=False):
    """The tests (n, a, m, W, d, p) in the order of the machine, and the halting n."""
    n = n0
    while True:
        solved = False
        x = 0
        while not solved:
            x += 1
            U = rate * x
            if U <= n: continue
            if U > 3 * n: return n
            a, m = U - n, n * x
            y = 0
            while True:
                y += 1
                W = a * y
                if W > 2 * m + 2: break
                if W > m:
                    d, p = W - m, m * y
                    yield (n, x, y, a, m, W, d, p)
                    if p % d == 0 and not nohit: solved = True; break
        n += 1

def decode(t):
    blocks = t.strip('0').split('00')
    assert len(blocks) == 7, blocks
    Ab, Rb, Nb, Mb, Kb, Db, Pb = blocks
    for b in (Ab, Rb, Nb, Mb, Db, Pb): assert '0' not in b, blocks
    a, n, m, d, p = len(Ab) - 1, len(Nb) - 1, len(Mb) - 1, len(Db) - 1, len(Pb) - 1
    assert len(Rb) == 2 * n + build.SLACK - a and len(Kb) == m + 5 - d, blocks
    assert Kb[:3] == '101' and Kb.count('0') == 1, Kb
    return (n, a, m, d, p)

def check(rate, n0, steps, maxtrace, nohit=False):
    """The mod walks of the variant against the reference; returns (ok, run result)."""
    build.build(n0=n0, rate=rate, nohit=nohit)
    r = tm.run(build.ORDER, build.ST, maxsteps=steps, trace='ms4', maxtrace=maxtrace)
    ref = reference(n0, rate, nohit)
    cnt, want, ok = 0, None, True
    for tr in r[5]:
        try:
            want = next(ref)
        except StopIteration:
            print('  extra walk', decode(tr)); return False, r
        got = decode(tr)
        if got != (want[0], want[3], want[4], want[6], want[7]):
            print('  FAIL at', cnt, got, want); return False, r
        cnt += 1
    print(f'  rate {rate}, n0 = {n0}: {cnt} mod walks as in the reference, last (n, x, y) =',
          want[:3] if want else None, r[0], r[1])
    return True, r

def main():
    ok = True
    for rate, n0 in [(4, 2), (5, 2), (6, 2), (7, 3)]:
        good, r = check(rate, n0, 10**9, 3000)
        ok &= good
    for rate, n0, nh, nohit in [(4, 1, 1, False), (8, 2, 2, False), (8, 3, 3, False),
                                (9, 3, 5, False), (4, 5, 5, True), (4, 7, 7, True), (4, 12, 12, True),
                                (5, 9, 9, True)]:
        good, r = check(rate, n0, 10**9, 3000, nohit)
        Nb = re.split('0+', r[4].strip('0'))[-3]   # (K has no hole here)
        h = good and r[0] == 'halt' and len(Nb) == nh + 1
        print(f'  rate {rate}, n0 = {n0}{" (no hits)" if nohit else ""} halts at n = {nh}:', r[0],
              'OK' if h else 'FAIL'); ok &= h
    build.build()
    r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
    print('10^8 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
    print('ALL OK' if ok else 'FAILURES')

if __name__ == '__main__':
    main()
