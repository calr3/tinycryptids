"""Emit lean/TinyCryptids/Amicable/Machine.lean from amicable.txt (the design machine):
`delta`, and `deltaNB`, the design without its beep transition (H5 reading 0)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
os.makedirs(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'lean', 'TinyCryptids', 'Amicable'), exist_ok=True)
print(leangen.machine_lean('amicable.txt', 'Amicable', beep=('H5', 0)), 'states written')
