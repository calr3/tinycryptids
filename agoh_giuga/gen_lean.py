"""Emit lean/TinyCryptids/AgohGiuga/Machine.lean from agoh_giuga.txt (the design machine)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
print(leangen.machine_lean('agoh_giuga.txt', 'AgohGiuga'), 'states written')
