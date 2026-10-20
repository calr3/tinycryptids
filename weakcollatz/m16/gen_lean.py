"""Emit lean/TinyCryptids/WeakCollatz16/Machine.lean from weakcollatz.txt (the design machine)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'tools'))
import leangen
print(leangen.machine_lean('weakcollatz.txt', 'WeakCollatz16'), 'states written')
