"""Tests for the beeping Wall-Sun-Sun machine.
 * Design, blank start: at every check (entry to q2, after the odometer's last string) for
   m = 2 .. 24, B is clean (m + 1 cells), E and D (m + 2 cells) have their holes at
   1 + v mod m and 1 + (v div m) mod m, v = m - 1 + N, N = F(m - 1) if m = 1, 4 mod 5 else
   F(m + 1).  Every round start (entry to e2) for m = 2 .. 26 is build.canon(m); with m0 = 1
   (round 1 written by the seed) the round starts are canon(1), canon(2), ...
 * Design variants beep (q9 reading 0) exactly in the rounds a model predicts: `extra` cells
   in B (N = F(m - 1 + extra) or F(m + 1 + extra)), all residues `holes` (N = F(m - 1 + extra)),
   and the low digit only (q7 reading 0: m | N).  The m of a beep is read off B's length.
 * The merged machine (default machines/wallsunsuninf_48.txt), blank start, follows the
   design with m0 = 1 (the round m = 1 written by a plain seed) up to a fixed step offset:
   the same tape and head at 10^3 .. 10^8 steps after round 1 starts, and the same beeps.
   Its beeps in 2 * 10^8 steps are at most the check of m = 1.
Usage: python3 test_e2e.py [merged.txt]"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [HERE, os.path.join(HERE, '..', 'tools')]
import tm, build

def fib(n):
    a, b = 0, 1
    for _ in range(n): a, b = b, a + b
    return a

def blocks(t):
    out, cur, z = [], '', 0
    for ch in t.strip('0'):
        if ch == '0':
            z += 1
        else:
            if z >= 2: out.append(cur); cur = ''
            elif z == 1: cur += '0'
            cur += '1'; z = 0
    out.append(cur)
    return out

def hole(b, size):
    assert len(b) == size and b.count('0') == 1, (b, size)
    return b.index('0')

def count(m, extra=0, holes=(1, 4)):
    L = m - 1 + extra
    return fib(L) if m % 5 in holes else fib(L + 2)

def model_beeps(ms, extra=0, holes=(1, 4), low=False):
    return [m for m in ms if count(m, extra, holes) % (m if low else m * m) == 0]

def beep_ms(order, states, beep, maxsteps, extra=0):
    r = tm.run(order, states, maxsteps=maxsteps, beep=beep, maxtrace=10 ** 6)
    return [len(blocks(t)[0]) - 1 - extra for _, t in r[5]], r

def offset_to_round1(order, states):
    """Steps until the first exact round start canon(1) at e1's class, head on D's cell 0."""
    T, head, q = {}, 0, order[0]
    for step in range(10 ** 5):
        if q == 'e1':
            ones = [k for k, v in T.items() if v] or [0]
            lo, hi = min(ones), max(ones)
            tp = ''.join(str(T.get(i, 0)) for i in range(lo, hi + 1))
            if tp == build.canon(1) and head == hi - 2: return step
        w, d, q = states[q][T.get(head, 0)]; T[head] = w; head += 1 if d == 'R' else -1
    raise AssertionError('no round start')

def norm(r):
    t = r[4]; lo = t.index('1'); return r[2:3] and (t.strip('0'), r[3] - lo)

if __name__ == '__main__':
    bad = 0
    order, states = build.build()
    n = 23
    r = tm.run(order, states, maxsteps=10 ** 10, trace='q2', maxtrace=n)
    assert len(r[5]) == n
    for m, t in zip(range(2, 2 + n), r[5]):
        B, E, D = blocks(t)
        v = m - 1 + count(m)
        ok = B == '1' * (m + 1) and (hole(E, m + 2), hole(D, m + 2)) == (1 + v % m, 1 + (v // m) % m)
        if not ok: print('check of m =', m, 'wrong:', t); bad += 1
    print('design: checks m = 2 ..', n + 1, 'OK' if not bad else 'FAIL')
    n = 25
    r = tm.run(order, states, maxsteps=10 ** 10, trace='e2', maxtrace=n)
    wrong = [m for m, t in zip(range(2, 2 + n), r[5]) if t.strip('0') != build.canon(m)]
    print('design: round starts m = 2 ..', n + 1, 'OK' if not wrong and len(r[5]) == n else f'FAIL {wrong}')
    bad += bool(wrong) or len(r[5]) != n
    # variants against the model
    for kw, low, steps in [(dict(), True, 3 * 10 ** 8), (dict(extra=3), False, 10 ** 9),
                           (dict(extra=8), False, 10 ** 9), (dict(extra=5, holes=range(5)), False, 10 ** 9),
                           (dict(extra=1), False, 10 ** 9), (dict(extra=11), False, 2 * 10 ** 9)]:
        o, s = build.build(**kw)
        got, r = beep_ms(o, s, ('q7', 0) if low else build.BEEP, steps, kw.get('extra', 0))
        last = len(blocks(r[4])[0]) - 1 - kw.get('extra', 0)   # the round reached
        want = model_beeps(range(2, last), kw.get('extra', 0), kw.get('holes', (1, 4)), low)
        ok = got[:len(want)] == want and all(m >= last for m in got[len(want):])
        print('variant', kw, 'low digit' if low else '', 'rounds to', last, 'beeps at', want[:12],
              '...' if len(want) > 12 else '', 'OK' if ok else f'FAIL {got[:12]}')
        bad += not ok
    # the merged machine against the design with m0 = 1
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'machines', 'wallsunsuninf_48.txt')
    mo, ms, _ = tm.parse(open(path).read())
    do, ds = build.build(m0=1)
    r = tm.run(do, ds, maxsteps=10 ** 9, trace='e2', maxtrace=8)
    ok = [t.strip('0') for t in r[5]] == [build.canon(m) for m in range(1, 9)]
    print('design, m0 = 1: round starts m = 1 .. 8', 'OK' if ok else 'FAIL'); bad += not ok
    a, b = offset_to_round1(mo, ms), offset_to_round1(do, ds)
    print('round 1 starts at step', a, '(merged),', b, '(design, m0 = 1)')
    for k in range(3, 9):
        rm = tm.run(mo, ms, maxsteps=a + 10 ** k); rd = tm.run(do, ds, maxsteps=b + 10 ** k)
        same = norm(rm) == norm(rd)
        print(f'  10^{k} steps later: same tape and head' if same else f'  10^{k}: DIFFERENT'); bad += not same
    N = 2 * 10 ** 8
    gm, rm = beep_ms(mo, ms, ('q9', 0), a + N); gd, rd = beep_ms(do, ds, build.BEEP, b + N)
    sm = [st - a for st, _ in rm[5]]; sd = [st - b for st, _ in rd[5]]
    ok = sm == sd and set(gm) <= {1}
    print('merged: beeps at m =', gm, 'steps after round 1', sm, '(design:', sd, ')', 'OK' if ok else 'FAIL')
    bad += not ok
    print('FAIL' if bad else 'all OK')
