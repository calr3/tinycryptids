"""Tests of the weak Collatz machine (pure Python stepping, plus the C simulator).
* Every macro step: from C(M, v) (head on cell 0 in `disp`), for all
  2 <= M <= 60 and 1 <= v <= M, the machine reaches the next C(M', v') or halts,
  as the reference says.  This includes the halting case T(v) = M, which the
  real run never meets.
* From the blank tape, the tape at every visit of `disp` on cell 0 follows the
  reference (M, v) sequence for rounds 2 .. 300.
* The real machine runs past 10^8 steps (C simulator)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'tools'))
import tm, build

def T(v): return v // 2 if v % 2 == 0 else (3 * v + 1) // 2

def macro(M, v):
    """the reference macro step from C(M, v): ('C', M', v') or ('halt',)"""
    if v == 1: return ('C', M + 1, M + 1)
    y = T(v)
    if y < M: return ('C', M, y)
    if y == M: return ('halt',)
    return ('C', M + 1, M + 1)

def tape_C(M, v):
    return {i: 1 for i in range(M) if i != v - 1}

def run_macro(ST, tape, maxsteps=10**6):
    """from `disp` on cell 0: run to the next `disp` on cell 0, or to the halt"""
    h, q, steps = 0, 'disp', 0
    while steps < maxsteps:
        w, d, q = ST[q][tape.get(h, 0)]
        tape[h] = w; h += 1 if d == 'R' else -1; steps += 1
        if q not in ST: return ('halt', h, steps)
        if q == 'disp' and h == 0: return ('disp', steps)
    raise AssertionError('no macro end')

def ones(tape): return {i for i, b in tape.items() if b}

def test_macros(Mmax=60):
    _, ST, _ = tm.parse(build.build())
    n = 0
    for M in range(2, Mmax + 1):
        for v in range(1, M + 1):
            tape = tape_C(M, v)
            r, exp = run_macro(ST, tape), macro(M, v)
            if exp == ('halt',):
                assert r[0] == 'halt', (M, v, r)
                assert ones(tape) == set(tape_C(M, M)), (M, v)   # the tape of C(M, M)
                assert r[1] == M + 1, (M, v, r)
            else:
                assert r[0] == 'disp', (M, v, r)
                assert ones(tape) == set(tape_C(exp[1], exp[2])), (M, v, exp, sorted(ones(tape)))
            n += 1
    return n

def test_run(rounds=300):
    _, ST, _ = tm.parse(build.build())
    tape, h, q = {}, 0, 'fill'
    M, v, k = 2, 2, 0
    while M <= rounds:
        w, d, q = ST[q][tape.get(h, 0)]
        tape[h] = w; h += 1 if d == 'R' else -1
        assert q in ST
        if q == 'disp' and h == 0:
            assert ones(tape) == set(tape_C(M, v)), (M, v)
            k += 1
            r = macro(M, v)
            assert r[0] == 'C'
            M, v = r[1], r[2]
    return k

if __name__ == '__main__':
    print('macro steps checked:', test_macros())
    print('run from the blank tape: %d macro steps, rounds 2 .. 300' % test_run())
    order, ST, _ = tm.parse(build.build())
    r = tm.run(order, ST, maxsteps=10**8)
    assert r[0] == 'limit', r[:3]
    print('10^8 steps: limit OK')
