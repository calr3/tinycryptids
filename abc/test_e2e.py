"""End-to-end checks of the design (and of a merged machine given as argument).
 * The events (B = beep, `xe3` reading 0; O = boop, `xq6` reading 0) of the first 2·10^10
   steps are, in order, those of the reference model `ref.py`: for each pair (a, b),
   c = a + b, in the order c = 2, 3, ..., a = 1 .. c - 1, nothing if gcd(a, b) > 1 or
   c <= rad(abc), else `val` beeps (the least n with c^n > rad^(n+1)) and one boop. That
   covers 1 + 8 = 9 and 8 + 1 = 9 (5 beeps each; the first boop is at step 9.45·10^9: the
   powers are unary, 9^5 against 6^6), and the run is then inside 5 + 27 = 32.
 * Variant 'halt' (the boop replaced by a halt) halts at the first boop, after the 5 beeps of
   1 + 8 = 9 (9^5 > 6^6, 9^4 <= 6^5).
 * The machine runs 10^8 steps without halting.
Usage: test_e2e.py [machines/merged.txt]  (the merged machine: the same events)"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))  # tm.py
import build, tm, ref

def events(order, st, beep, boop, steps):
    r = tm.run(order, st, maxsteps=steps, maxtrace=10**7, beep=beep, boop=boop, notape=True)
    return r[0], ''.join(e[0] for e in r[5])

ok = True
build.build()
STEPS = 2 * 10**10
status, ev = events(build.ORDER, build.ST, build.BEEP, build.BOOP, STEPS)
# the reference events of enough pairs; the run stops inside some pair
want = ref.events(5000)
done = ev[:ev.rfind('O') + 1]
good = status == 'limit' and done == 'BBBBBOBBBBBO' and want.startswith(ev)
print(f'events of 2*10^10 steps: {ev.count("B")} beeps, {ev.count("O")} boops, as ref.py:', 'OK' if good else 'FAIL')
print('  values:', [len(s) for s in done.split('O')[:-1]][:20], '...')
ok &= good

if len(sys.argv) > 1:
    o2, s2, _ = tm.parse(open(sys.argv[1]).read())
    st2, ev2 = events(o2, s2, ('xe3', 0), ('xq6', 0), STEPS)
    good = ev2 == ev
    print(f'{sys.argv[1]}: the same events in 2*10^10 steps:', 'OK' if good else 'FAIL'); ok &= good

build.build(variant='halt')
h = tm.run(build.ORDER, build.ST, maxsteps=STEPS, maxtrace=100, beep=build.BEEP)
good = h[0] == 'halt' and len(h[5]) == 5
print("variant 'halt' halts at the first boop, after", len(h[5]), 'beeps:', h[0], h[1], 'OK' if good else 'FAIL')
ok &= good

build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
print('10^8 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
print('ALL OK' if ok else 'FAILURES')
