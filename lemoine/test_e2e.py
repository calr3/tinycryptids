"""End-to-end tests of the Lemoine machine (build.py's design, or a given file for the last test).
* Every normalization (traced at c5, the pair's separator about to be rewritten), from a blank
  tape: the pair normalized (P before its test, Q before its test), its value and the gap
  G = 2(q - q0) + 4 follow the reference order of (n, q) below; the other pair holds what it should.
* Variants q0 (the search q >= q0, from n = 3 + 2 q0): q0 = 3 follows the reference for 300
  normalizations; q0 = 4, 6, 7 halt at the first odd n with no p + 2q, q >= q0 prime
  (11, 15, 23), after the reference sequence.
* The real machine runs past 10^8 steps (C simulator).
Usage: python3 test_e2e.py [file]"""
import os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm, build

def prime(m): return m >= 2 and all(m % d for d in range(2, m))

def events(q0=2):
    """(which, n, q, value) for each normalization, in order; ends with ('P', n, q, 1)."""
    n = 3 + 2 * q0
    while True:
        q = q0
        while True:
            p = n - 2 * q
            yield 'P', n, q, p
            if p == 1: return
            if prime(p):
                yield 'Q', n, q, q
                if prime(q): break
            q += 1
        n += 2

def decode(t):
    """the tape at c5: (which, value, gap, other pair's string)"""
    t = t.strip('0')
    m = re.fullmatch(r'10(1[01]*?)(0{3,})(1[01]*)01', t)
    assert m, t
    P, gap, Q = m.groups()
    if '00' not in P:
        assert re.fullmatch(r'101+', P), t
        return 'P', len(P) - 6, len(gap), Q
    assert re.fullmatch(r'101+', Q), t
    return 'Q', len(Q) - 6, len(gap), P

def decode_halt(t):
    """the tape at the halt: P normalized with one cell in R (p = 1)"""
    m = re.fullmatch(r'10(1011001)0{3,}1[01]*01', t.strip('0'))
    assert m, t
    return len(m.group(1)) - 6

def check(q0=2, n_events=300, halt=False):
    build.build(q0=q0)
    ev = list(zip(range(n_events), events(q0)))
    r = tm.run(build.ORDER, build.ST, maxsteps=10 ** 10, trace='c5', maxtrace=len(ev))
    assert len(r[5]) == len(ev), (len(r[5]), len(ev))
    for (_, (which, n, q, v)), t in zip(ev, r[5]):
        w, val, gap, other = decode(t)
        assert (w, val, gap) == (which, v, 2 * (q - q0) + 4), (t, which, n, q, v)
        if which == 'P':      # Q at rest: D hole at cell 1, R without hole, q = d + r
            D, R = other.split('00')
            assert D[:2] == '10' and '0' not in D[2:] + R and len(D) + len(R) - 4 == q, t
        else:                 # P after a prime test: d = p, r = 0
            assert other == '10' + '1' * (n - 2 * q) + '0011', t
    if halt:
        r = tm.run(build.ORDER, build.ST, maxsteps=10 ** 10)
        assert r[0] == 'halt' and decode_halt(r[4]) == ev[-1][1][1] - 2 * ev[-1][1][2], r[:4]
        print(f'variant q0={q0}: halts after {len(ev)} normalizations, {r[1]} steps, at n = {ev[-1][1][1]}')
    else:
        print(f'first {len(ev)} normalizations as expected (up to n = {ev[-1][1][1]})')

if __name__ == '__main__':
    check(2, 400)
    check(3, 300)
    for q0 in (4, 6, 7):
        k = len(list(events(q0)))
        check(q0, k, halt=True)
    text = open(sys.argv[1]).read() if len(sys.argv) > 1 else build.build()
    order, states, _ = tm.parse(text)
    res = tm.run(order, states, maxsteps=10 ** 8)
    print('C simulator, 10^8 steps:', res[0]); assert res[0] != 'halt'
    print('ALL OK')
