"""Emit lean/TinyCryptids/Riesel/Machine.lean from riesel.txt (the design machine)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
print(leangen.machine_lean('riesel.txt', 'Riesel'), 'states written')
