"""Routine tests on hand-placed tapes: the trial pass, Horner, the pair step."""
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
# trial pass for m: tape L 00 P0 00 primes 00 M, start at u5 (P1's cell 0)
for m in range(3, 60):
    pr = [q for q in range(2, m) if ref.isprime(q)]
    if not pr: continue
    L = D(m, 1); M = D(m, 1)
    tape = '000' + L + '00' + '111' + '00' + '00'.join(D(q) for q in pr) + '00' + M + '000'
    head = 3 + len(L) + 2 + 3 + 2
    s, n, st, h, t = run_until({'rt1', 'PM1'}, 'kn5', tape, head)
    want = 'rt1' if ref.isprime(m) else 'PM1'
    good = st == want
    # tape unchanged (all list holes filled)
    good &= blocks(t) == blocks(tape)
    if not good: print('trial', m, s, st); ok = False
print('trial pass ok' if ok else 'trial FAIL')

# Horner H1 / H2 on a pair (p, m): from rt5 at p's cell 1 to hd1 (exponent done)
def pair_tape(m, pr, i):
    L = D(m, 1); M = D(m, 1)
    bl = [D(q) for q in pr]
    return '000' + L + '00' + '111' + '00' + '00'.join(bl) + '00' + M + '000' * 10
for m in [3, 5, 7]:
    pr = [q for q in range(2, m) if ref.isprime(q)]
    for i, p in enumerate(pr):
        if ref.rep(p, m) > 3000: continue
        tape = pair_tape(m, pr, i)
        head = 3 + m + 2 + 2 + 3 + 2 + sum(q + 2 + 2 for q in pr[:i]) + 1   # p's cell 1
        s, n, st, h, t = run_until({'hd1'}, 'rt5', tape, head)
        bs = blocks(t)
        good = st == 'hd1' and val(bs[-1]) == ref.rep(p, m)
        # continue: H2
        s2, n2, st2, h2, t2 = run_until({'tw1', 'pz1'}, 'hd1', t, h)
        bs2 = blocks(t2)
        good &= st2 == 'tw1' and val(bs2[-1]) == ref.rep(m, p) and val(bs2[-2]) == ref.rep(p, m)
        if not good: print('horner', p, m, st, [val(b) for b in bs], st2, [val(b) for b in bs2]); ok = False
        else: print('pair', p, m, 'A =', val(bs2[-2]), 'B =', val(bs2[-1]), n + n2, 'steps')
print('OK' if ok else 'FAIL')

# composite and prime transitions, per-prime step
def cand_tape(m, pr, marker=None, mark_m=True):
    L = D(m, 1); M = D(m, 1 if mark_m else None)
    bl = [D(q, 1 if q == marker else None) for q in pr]
    return '000' + L + '00' + '111' + '00' + '00'.join(bl) + '00' + M + '0' * 40
def vals(t): return [val(b) for b in blocks(t)]
for m in range(4, 40):
    pr = [q for q in range(2, m) if ref.isprime(q)]
    if ref.isprime(m):
        # prime: from kn6 at M's cell 1 to the pair entry pw1 (marker at Pk)
        tape = cand_tape(m, pr)
        head = tape.rindex('00' + D(m, 1) + '0') + 3
        s, n, st, h, t = run_until({'pw1'}, 'kn6', tape, head)
        bs = blocks(t)
        good = st == 'pw1' and vals(t) == [m, 1] + pr + [m] and bs[-2] == D(pr[-1], 1)
        # the pair pass ends at P0: H1 for P0, then the next candidate (ca2: trial step for P1)
        tape = '000' + D(m, 1) + '00' + '111' + '00' + '00'.join(D(q) for q in pr) + '00' + D(m, 1) + '0' * 40
        s, n, st, h, t = run_until({'ca2'}, 'rt5', tape, 3 + m + 2 + 2 + 1)   # P0's cell 1
        good &= st == 'ca2' and vals(t) == [m + 1, 1] + pr + [m, m + 1] and blocks(t)[0] == D(m + 1, 1) \
            and blocks(t)[-1] == D(m + 1, 1)
        if not good: print('prime', m, st, vals(t)); ok = False
    else:
        # composite: Pi | m with the counter's hole filled; from kd5 (next block's cell 0) to ca2
        p = min(q for q in pr if m % q == 0)
        tape = cand_tape(m, pr)
        i = pr.index(p)
        head = 3 + m + 2 + 2 + 3 + 2 + sum(q + 4 for q in pr[:i + 1])     # next block's cell 0
        s, n, st, h, t = run_until({'ca2'}, 'kd5', tape, head)
        good = st == 'ca2' and vals(t) == [m + 1, 1] + pr + [m + 1] and blocks(t)[0] == D(m + 1, 1)
        if not good: print('composite', m, st, vals(t)); ok = False
print('transitions ok' if ok else 'transitions FAIL')
