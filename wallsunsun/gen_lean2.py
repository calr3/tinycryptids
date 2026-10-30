"""Emit lean/TinyCryptids/WallSunSun2/Machine.lean from wallsunsun2.txt (build2.py's design)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
print(leangen.machine_lean('wallsunsun2.txt', 'WallSunSun2'), 'states written')
