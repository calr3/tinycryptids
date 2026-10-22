"""End-to-end tests of the Fermat machine (build.py's design, or a given file for the last test).
* Variants: emin = 1 halts on 1 + 1 = 2; A restored with d cells (a_init) halts on the first
  tuple of the search order with x^E + y^E + d = z^E, for several d (the tuple is read off the
  tape at the halt).
* The real machine runs 10^8 steps without halting (C simulator).
Usage: python3 test_e2e.py [file]"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm, build

def nxt(t):
    E, a, b, c = t
    if E >= 4: return (E - 1, a + 1, b, c)
    if a >= 2: return (a + 1, 1, b + 1, c)
    if b >= 2: return (b + 1, 1, 1, c + 1)
    if c >= 2: return (c + 3, 1, 1, 1)
    return (4, 1, 1, 1)

def first_halt(d, emin=3, limit=20000):
    t = (emin + 1, 1, 1, 1)
    for _ in range(limit):
        t = nxt(t) if emin == 3 else t
        E, a, b, c = t
        if a ** E + b ** E + d == c ** E: return t
    return None

def tuple_of(tape):
    """(E, x, y, z) from the tape at the halt (blocks split at 00; the anchor is the single 0)"""
    blocks = [b for b in tape.strip('0').split('00') if b]
    return tuple(len(b) - 2 for b in blocks[:4])

if __name__ == '__main__':
    build.build(emin=1)
    r = tm.run(build.ORDER, build.ST, maxsteps=10 ** 8)
    assert r[0] == 'halt' and tuple_of(r[4]) == (1, 1, 1, 2), (r[:2], r[4].strip('0'))
    print('emin = 1: halts on 1 + 1 = 2 after', r[1], 'steps')
    for d in (6, 11, 14, 18, 25, 29, 36, 55, 62, 64):
        want = first_halt(d)
        build.build(a_init='1' * d)
        r = tm.run(build.ORDER, build.ST, maxsteps=10 ** 10)
        got = tuple_of(r[4]) if r[0] == 'halt' else None
        assert got == want, (d, want, r[:2], got)
        print(f'A + {d}: halts on {want} after {r[1]} steps')
    if len(sys.argv) > 1:
        o, S, _ = tm.parse(open(sys.argv[1]).read())
    else:
        build.build(); o, S = build.ORDER, build.ST
    r = tm.run(o, S, maxsteps=10 ** 8)
    assert r[0] == 'limit', r[:2]
    print('real machine: no halt in', r[1], 'steps')
