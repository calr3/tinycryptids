"""End to end: variants that must halt do, and the real machine (design and merged) runs
10^8 steps without halting."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))  # tm.py
import build, tm

for kw, at in (({'t': 5}, 9), ({'t': 6, 'c0': 3}, 25), ({'t': 7, 'c0': 4}, 25)):
    build.build(**kw)
    r = tm.run(build.ORDER, build.ST, maxsteps=10**8, trace='hg5', maxtrace=10**6)
    print(kw, r[0], r[1], 'steps, at m =', len(r[5]) + 2)
    assert r[0] == 'halt' and len(r[5]) + 2 == at
for f in ('brocard_primes.txt', 'machines/brocard_primes_72.txt'):
    o, S, _ = tm.parse(open(f).read())
    r = tm.run(o, S, maxsteps=10**8)
    print(f, r[0], r[1], 'steps')
    assert r[0] != 'halt'
