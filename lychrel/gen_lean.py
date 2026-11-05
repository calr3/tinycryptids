"""Emit lean/TinyCryptids/Lychrel/Machine.lean from lychrel.txt (the design machine)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
print(leangen.machine_lean('lychrel.txt', 'Lychrel'), 'states written')
