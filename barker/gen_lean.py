"""Emit lean/TinyCryptids/Barker/Machine.lean from barker.txt (the design machine)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
os.makedirs(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'lean', 'TinyCryptids', 'Barker'), exist_ok=True)
print(leangen.machine_lean('barker.txt', 'Barker'), 'states written')
