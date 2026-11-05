"""Emit lean/TinyCryptids/Erdos/Machine.lean from machines/erdos_15.txt."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
print(leangen.machine_lean('machines/erdos_15.txt', 'Erdos'), 'states written')
