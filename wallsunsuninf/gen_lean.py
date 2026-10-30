"""Emit lean/TinyCryptids/WallSunSunInf/Machine.lean from wallsunsuninf_seeded.txt (the Lean
design, see unroll_seed.py): `delta` and `deltaNB` (without the beep, q9 reading 0)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
print(leangen.machine_lean('wallsunsuninf_seeded.txt', 'WallSunSunInf', beep=('q9', 0)), 'states written')
