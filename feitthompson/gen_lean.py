"""Emit lean/TinyCryptids/FeitThompson/Machine.lean from feitthompson.txt (the design machine)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
print(leangen.machine_lean('feitthompson.txt', 'FeitThompson'), 'states written')
