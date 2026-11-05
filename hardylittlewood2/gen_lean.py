"""Emit lean/TinyCryptids/HardyLittlewood2/Machine.lean from hardylittlewood2.txt (the design machine)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
print(leangen.machine_lean('hardylittlewood2.txt', 'HardyLittlewood2'), 'states written')
