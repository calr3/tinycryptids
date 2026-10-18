"""End-to-end tests of the weak Collatz machine (pure Python stepping).
* At every step (the parity branch at H) the tape must be the block
  1^(n+2) with one hole at x, for the (n, x) sequence of the reference.
* The variant without the x = 1 abort must halt in round 4 (4 -> 2 -> 1 -> 4).
* The real machine runs past 10^8 steps (C simulator)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm, build

def C(x): return x // 2 if x % 2 == 0 else 3 * x + 1

def reference(trivial=False, rounds=60):
    """(n, x) at each step start, in order; ('halt', n) at the end if it halts."""
    out = []
    for n in range(1, rounds + 1):
        x = n
        while True:
            out.append((n, x))
            x = C(x)
            if x == n: return out + [('halt', n)]
            if x > n or (x == 1 and not trivial): break
    return out

def simulate(text, maxsteps):
    order, ST, _ = tm.parse(text)
    tape, h, q, seen, steps = {}, 0, order[0], [], 0
    while steps < maxsteps:
        b = tape.get(h, 0)
        t = ST[q][b] if q in ST else None
        if t is None: return seen + [('halt', q)], steps
        w, d, nq = t
        if b == 0 and (q in ('p0', 'p1') or (q == 'c1' and nq == 'os')):   # step: the parity branch at H
            i = h
            while not (tape.get(i - 1, 0) == 0 and tape.get(i - 2, 0) == 0): i -= 1
            cells = []
            while not (tape.get(i, 0) == 0 and tape.get(i + 1, 0) == 0): cells.append(tape.get(i, 0)); i += 1
            cells.append(tape.get(i, 0))      # hole at the last value cell
            seen.append(cells)
        tape[h] = w; h += 1 if d == 'R' else -1; q = nq; steps += 1
    return seen, steps

def check(trivial, rounds, maxsteps):
    ref = reference(trivial, rounds)
    seen, steps = simulate(build.build(trivial=trivial), maxsteps)
    k = 0
    for item in seen:
        if isinstance(item, tuple):
            assert ref[k] == ('halt', ref[k][1]), (item, ref[k])
            return 'halt in round %d after %d steps' % (ref[k][1], steps)
        n, x = ref[k]
        exp = [1] * (n + 2); exp[x] = 0
        assert item[:n + 2] == exp, (k, n, x, got)
        k += 1
    return '%d step starts checked (rounds 1..%d)' % (k, ref[k - 1][0] if k else 0)

if __name__ == '__main__':
    print('variant:', check(True, 10, 10**6))
    print('real:', check(False, 400, 3 * 10**6))
    order, ST, _ = tm.parse(build.build())
    r = tm.run(order, ST, maxsteps=10**8)
    assert r[0] == 'limit', r[:3]
    print('10^8 steps: limit OK')
