"""End-to-end checks of the design.
 * at each rebuild (state c2) the tape is G 00 M 00 S(n-1) 000 ... S1 gap D 00 R with
   the values of a Python reference (G the gap to the last prime, S the stored diagonal);
 * test variants (another seed list or target) halt exactly at the first prime whose
   new bottom entry is not the target;
 * the real machine must run past 10^8 steps."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

from ref import is_prime, ext, reference, parse

ok = True
build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**10, trace='c2', maxtrace=1000)
got = [parse(t) for t in r[5]]
ref, _ = reference([1], 1, 3, 1, len(got))
# at c2 the D/R region still holds m (the rebuild makes m + 1)
ref = [(g, S, m) for (g, S, m) in ref]
good = got == ref
print(f'{len(got)} candidates up to m = {got[-1][2]}, |S| = {len(got[-1][1])}:', 'OK' if good else 'FAIL')
if not good:
    for a, b in zip(got, ref):
        if a != b: print(' got', a, '\n ref', b); break
ok &= good

def true_S(p):
    """the stored diagonal after the prime p"""
    S, g, m = [1], 1, 3
    while m < p:
        m += 1
        if is_prime(m): S, g = ext(S, g), 1
        else: g += 1
    return S

S53 = true_S(53); S53[7] += 2       # a wrong entry deep in the diagonal: fails at 59
S47 = true_S(47); S47[13] += 2      # the deepest entry: fails at 53
for seed_s, seed_g, seed_m, target in (([2], 1, 3, 1), ([0], 1, 3, 1), ([1], 2, 3, 1), ([1, 2, 0], 1, 3, 1),
                                       ([1], 1, 3, 2), ([3, 1], 1, 3, 1), ([1, 1, 1, 1], 1, 3, 1),
                                       (S53, 1, 53, 1), (S47, 1, 47, 1), (true_S(23), 1, 23, 3)):
    build.build(seed_s=seed_s, seed_g=seed_g, seed_m=seed_m, target=target)
    h = tm.run(build.ORDER, build.ST, maxsteps=10**10, trace='c2', maxtrace=10**6)
    got = [parse(t) for t in h[5]]
    ref, hm = reference(seed_s, seed_g, seed_m, target, 10**6)
    good = h[0] == 'halt' and got == ref and hm is not None
    print(f'variant S={seed_s} g={seed_g} m={seed_m} target={target}: {h[0]} after {h[1]} steps,'
          f' {len(got)} candidates, halting prime {hm}', 'OK' if good else 'FAIL')
    ok &= good

build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
print('10^8 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
print('ALL OK' if ok else 'FAILURES')
