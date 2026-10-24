"""Emit lean/TinyCryptids/TwinPrimes/Machine.lean from twinprimes.txt (the design machine):
`delta`, and `deltaNB`, the design without its beep transition (G2 reading 0)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
os.makedirs(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'lean', 'TinyCryptids', 'TwinPrimes'), exist_ok=True)
print(leangen.machine_lean('twinprimes.txt', 'TwinPrimes', beep=('G2', 0)), 'states written')
