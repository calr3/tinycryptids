"""Emit lean/TinyCryptids/Andrica/Machine.lean from andrica.txt (the design machine)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
print(leangen.machine_lean('andrica.txt', 'Andrica'), 'states written')
