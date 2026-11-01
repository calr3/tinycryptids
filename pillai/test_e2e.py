"""End-to-end checks of the design (and of a merged machine given as argument).
 * The events (B = beep, `zX3` reading 1; O = boop, `zX3` reading 0) of the first 10^9 steps are
   those of the reference model `ref.py`: for each tuple (x, y, a, b) in the search order, nothing
   if a^x <= b^y, else a^x - b^y - 1 beeps and one boop.
 * Variant 'halt' (the boop replaced by a halt) halts at the first boop, after the 4 beeps of
   (x, y, a, b) = (2, 2, 3, 2): 3^2 - 2^2 = 5.
 * The machine runs 10^8 steps without halting.
Usage: test_e2e.py [machines/merged.txt]  (the merged machine: the same events)"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))  # tm.py
import build, tm, ref

STEPS = 10 ** 9

def events(order, st, beep, boop, steps=STEPS):
    r = tm.run(order, st, maxsteps=steps, maxtrace=10 ** 8, beep=beep, boop=boop, notape=True)
    return r[0], ''.join(e[0] for e in r[5])

def ref_prefix(ev):
    """the reference events, as long as they can be a prefix of `ev` (values are huge later)"""
    out, g = '', ref.tuples()
    while len(out) <= len(ev):
        out += ref.ev(next(g))
    return out

ok = True
build.build()
status, ev = events(build.ORDER, build.ST, build.BEEP, build.BOOP)
good = status == 'limit' and ref_prefix(ev).startswith(ev) and ev.count('O') >= 100
vals = [len(s) for s in ev.split('O')[:-1]]
print(f'events of 10^9 steps: {ev.count("B")} beeps, {ev.count("O")} boops, as ref.py:', 'OK' if good else 'FAIL')
print('  values:', vals[:20], '...')
ok &= good

if len(sys.argv) > 1:
    import leangen
    o2, s2, _ = tm.parse(open(sys.argv[1]).read())
    phi = leangen.state_map(build.ORDER, build.ST, o2, s2)
    st2, ev2 = events(o2, s2, (phi['zX3'], 1), (phi['zX3'], 0))
    good = ev2 == ev
    print(f'{sys.argv[1]}: the same events in 10^9 steps:', 'OK' if good else 'FAIL'); ok &= good

build.build(variant='halt')
h = tm.run(build.ORDER, build.ST, maxsteps=STEPS, maxtrace=100, beep=build.BEEP)
good = h[0] in ('halt', 'undefined') and len(h[5]) == 4
print("variant 'halt' halts at the first boop, after", len(h[5]), 'beeps:', h[0], h[1], 'OK' if good else 'FAIL')
ok &= good

build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
print('10^8 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
print('ALL OK' if ok else 'FAILURES')
