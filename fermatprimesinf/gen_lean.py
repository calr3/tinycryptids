"""Emit lean/TinyCryptids/FermatPrimesInf/Machine.lean from fermatprimesinf.txt (the design
machine): `delta`, and `deltaNB`, the design without its beep transition (G0 reading 0)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
os.makedirs(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'lean', 'TinyCryptids', 'FermatPrimesInf'), exist_ok=True)
print(leangen.machine_lean('fermatprimesinf.txt', 'FermatPrimesInf', beep=('G0', 0)), 'states written')
