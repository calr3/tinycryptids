"""End-to-end checks of the design (and of a merged machine, if given as argv[1]).
 * At every scan start (each entry into C1) the whole tape is compared with a model of the
   algorithm (README.md), for every x up to 120: pass 1 has P = 1^(x+1), its hole and the
   separator (three 0s), then N = 1^(x+4) (C1 on N's cell 1); pass 2, run iff s(x) > x
   (s = sum of proper divisors), has 1^(m+4), 00, N = 1^x, with m = s(x).
 * The beep transition (H5 reading 0) is taken first at x = 220, the smaller number of the
   first amicable pair, with N = 1^220 on the tape, and at no x before it.
 * The design never halts in 10^8 steps; a merged machine has the same beeps."""
import os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))  # tm.py
import build, tm

def s(n): return sum(d for d in range(1, n) if n % d == 0)

def model(xmax):
    out = []
    for x in range(1, xmax + 1):
        out.append('1' * (x + 1) + '000' + '1' * (x + 4))
        if s(x) > x: out.append('1' * (s(x) + 4) + '00' + '1' * x)
    return out

ok = True
build.build()
want = model(120)
r = tm.run(build.ORDER, build.ST, maxsteps=10**9, trace='C1', maxtrace=len(want))
got = [t.strip('0') for t in r[5]]
bad = [i for i, (g, w) in enumerate(zip(got, want)) if g != w]
good = len(got) == len(want) and not bad
print(len(want), 'scan starts (x <= 120) match the model:', 'OK' if good else f'FAIL at {bad[:3]}')
ok &= good

machines = [('design', build.ORDER, build.ST)]
if len(sys.argv) > 1:
    o, S, _ = tm.parse(open(sys.argv[1]).read()); machines.append((sys.argv[1], o, S))
for name, o, S in machines:
    r = tm.run(o, S, maxsteps=10**9, beep=('H5', 0), maxtrace=2)
    beeps = [(st, t.strip('0')) for st, t in r[5]]
    good = len(beeps) == 1 and beeps[0][1].endswith('00' + '1' * 220) and r[0] == 'limit'
    print(name, 'beeps in 10^9 steps:', [(st, len(t.split('00')[-1])) for st, t in beeps],
          'OK (x = 220 only)' if good else 'FAIL')
    ok &= good
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
print('10^8 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
print('ALL OK' if ok else 'FAILURES')
