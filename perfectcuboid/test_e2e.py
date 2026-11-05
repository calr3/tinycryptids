"""End-to-end checks.

* The design and the merged machine, from a blank tape, run 10^8 steps without halting
  (no perfect cuboid is known; none exists with edges below 10^10 or so).
* Every square check of the design's first tuples agrees with the abstract model
  (test_model.py) and the search order is NEXCOM's.
* Hand-placed tuples (test_windows.py): the Euler brick (44, 117, 240), started in the
  second, third or fourth window, halts; started in the first it goes on to the next tuple
  (44^2 + 117^2 + 240^2 is not a square), as do tuples with one wrong edge.
Usage: python3 test_e2e.py [merged.txt]"""
import os, sys, subprocess
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm

here = os.path.dirname(os.path.abspath(__file__))
for f in ['perfectcuboid.txt'] + sys.argv[1:] or ['machines/perfectcuboid_88.txt']:
    o, S, _ = tm.parse(open(os.path.join(here, f)).read())
    r = tm.run(o, S, maxsteps=10**8)
    assert r[0] == 'limit', (f, r[:3])
    print(f, len(o), 'states: no halt in 10^8 steps')
f2 = sys.argv[1] if len(sys.argv) > 1 else 'machines/perfectcuboid_88.txt'
o, S, _ = tm.parse(open(os.path.join(here, f2)).read())
assert tm.run(o, S, maxsteps=10**8)[0] == 'limit'
print(f2, len(o), 'states: no halt in 10^8 steps')
subprocess.run([sys.executable, os.path.join(here, 'test_model.py'), '3000000'], check=True, cwd=here)
subprocess.run([sys.executable, os.path.join(here, 'test_windows.py')], check=True, cwd=here)
