"""Routine tests on hand-placed tapes: the trial pass, the prime path (copy, H_B, H_A), and
the comparison B <= A."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm, ref

def run_until(stops, start, tape, head, maxsteps=10**9):
    """Run from `start`; stop on entering any state in `stops` (returns its name)."""
    st = {k: ([None, None] if k in stops else v) for k, v in build.ST.items()}
    r = tm.run(build.ORDER, st, start=start, tape=tape, head=head, maxsteps=maxsteps)
    return r[0], r[1], r[2], r[3], r[4]

def D(v, hole=None):
    """Block holding v (v + 2 cells), with a hole at cell `hole`."""
    c = ['1'] * (v + 2)
    if hole is not None: c[hole] = '0'
    return ''.join(c)

def blocks(t): return [b for b in t.strip('0').split('00') if b]
def val(b): return len(b) - 2

build.build()
ok = True
# trial pass for m: tape N 00 P1 .. Pk 00 M, start at kn6 on P1's cell 1
for m in range(3, 80):
    pr = [q for q in range(2, m) if ref.isprime(q)]
    e = len(pr) + 2
    tape = '000' + D(e, 1) + '00' + '00'.join(D(q) for q in pr) + '00' + D(m, 1) + '0' * 40
    head = 3 + e + 2 + 2 + 1
    s, n, st, h, t = run_until({'rt1', 'PX1'}, 'kn6', tape, head)
    want = 'rt1' if ref.isprime(m) else 'PX1'
    good = st == want
    if want == 'PX1':      # composite: M += 1, the list unchanged and without holes
        good &= blocks(t) == blocks(tape)[:-1] + [D(m + 1, 1)]
    if not good: print('trial', m, st); ok = False
print('trial pass ok' if ok else 'trial FAIL')

# prime path: from rt1 (prime m found) to the two dk4 checkpoints and the comparison
for (p, q, n, B, A) in list(ref.tests(11)):
    pr = [x for x in range(2, q) if ref.isprime(x)]
    e = n + 2
    tape = '000' + D(e, 1) + '00' + '00'.join(D(x) for x in pr) + '00' + D(q, 1) + '0' * (B + A + 60)
    head = tape.rindex(D(q, 1)) + 1                 # M's cell 1 (the hole), state rt1 next
    s, k1, st, h, t = run_until({'dk4'}, 'rt1', tape, head - 1)
    bs = blocks(t)
    good = st == 'dk4' and [val(b) for b in bs] == [e] + pr + [q, q, B] and bs[-2] == D(q, 1) \
        and bs[0] == D(e, 1)
    s, k2, st, h, t = run_until({'z0', 'QA1'}, 'dk4', t, h)
    good &= st == 'QA1'
    s, k3, st, h, t = run_until({'dk4'}, 'QA1', t, h)
    bs = blocks(t)
    good &= st == 'dk4' and [val(b) for b in bs] == [e + 1] + pr + [q, q, B, A] and bs[0] == D(e + 1, 1)
    if not good: print('prime', p, q, st, [val(b) for b in bs]); ok = False
    else: print('prime', q, 'B =', B, 'A =', A, k1 + k2 + k3, 'steps')
print('prime path ok' if ok else 'prime FAIL')

# compare: ... 00 M' 00 B 00 A from z0 (B's cell 2): halt iff b <= a, else the M' end (ms)
for b in range(1, 12):
    for a in range(1, 12):
        tape = '000' + D(5, 1) + '00' + D(b, 1) + '00' + D(a, 1) + '0' * 20
        head = 3 + 7 + 2 + 2
        s, k, st, h, t = run_until({'ms'}, 'z0', tape, head)
        if b <= a: good = s == 'halt'
        else: good = st == 'ms' and t.strip('0') == D(5, 1) and t[h] == '0' and t[h - 1] == '1'
        if not good: print('compare', b, a, s, st); ok = False
print('compare ok' if ok else 'compare FAIL')
print('OK' if ok else 'FAIL')
