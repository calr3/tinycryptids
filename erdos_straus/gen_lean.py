"""Emit lean/TinyCryptids/ErdosStraus/Machine.lean (the design) from erdos_straus.txt."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
print(leangen.machine_lean('erdos_straus.txt', 'ErdosStraus'), 'states written')
