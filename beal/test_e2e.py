"""End-to-end tests of the Beal machine.
* test_tuple.py: tuples placed on the tape (solutions with and without gcd(a, b) = 1, near
  misses), with the real machine and with the 'nogcd' variant.
* test_enum.py: from a blank tape the first 500 tuples tested are the NEXCOM successors of
  the seed, in order.
* Variants from a blank tape: 'nogcd' (no coprimality test) halts on 2^3 + 2^3 = 2^4;
  'swap' (halt on a pair that is not coprime) halts on a = b = 2.
* The real machine runs past 10^8 steps (C simulator).
Usage: python3 test_e2e.py [file]   (default: build.py's design; the tests that need
variants or start states of the design always use build.py)"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm, build, test_tuple, test_enum

if __name__ == '__main__':
    test_tuple.main()
    n = 500
    build.build()
    r = tm.run(build.ORDER, build.ST, maxsteps=10 ** 10, trace='gA0', maxtrace=n)
    seen = [tuple(L - 4 for L in test_enum.decode(t)) for t in r[5]]
    cur, want = [1, 0, 0, 0, 0, 0], []
    for _ in range(n):
        cur = test_enum.nexcom(cur); want.append(tuple(cur))
    assert seen == want; print('first', n, 'tuples in NEXCOM order')
    for var, want in (('nogcd', [0, 0, 1, 1, 1, 1]), ('swap', [0, 0, 0, 1, 1, 0])):
        build.build(variant=var)
        r = tm.run(build.ORDER, build.ST, maxsteps=10 ** 9)
        got = [L - 4 for L in test_enum.decode(r[4])]
        print(f'variant {var}:', r[0], r[1], 'steps, tuple', got)
        assert r[0] == 'halt' and got == want
    text = open(sys.argv[1]).read() if len(sys.argv) > 1 else build.build()
    order, states, _ = tm.parse(text)
    res = tm.run(order, states, maxsteps=10 ** 8)
    print('C simulator, 10^8 steps:', res[0]); assert res[0] != 'halt'
    print('ALL OK')
