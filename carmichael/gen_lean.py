"""Emit lean/TinyCryptids/Carmichael/Machine.lean (the design) from carmichael.txt."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
print(leangen.machine_lean('carmichael.txt', 'Carmichael'), 'states written')
