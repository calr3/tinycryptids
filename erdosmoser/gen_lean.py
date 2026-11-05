"""Emit lean/TinyCryptids/ErdosMoser/Machine.lean (the design) from erdosmoser.txt."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
print(leangen.machine_lean('erdosmoser.txt', 'ErdosMoser'), 'states written')
