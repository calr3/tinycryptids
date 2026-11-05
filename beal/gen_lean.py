"""Emit lean/TinyCryptids/Beal/Machine.lean (the design) from beal.txt."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
print(leangen.machine_lean('beal.txt', 'Beal'), 'states written')
