"""Emit lean/TinyCryptids/SophieGermain/Machine.lean from sophiegermain.txt (the design machine):
`delta`, and `deltaNB`, the design without its beep transition (G0 reading 0)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
os.makedirs(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'lean', 'TinyCryptids', 'SophieGermain'), exist_ok=True)
print(leangen.machine_lean('sophiegermain.txt', 'SophieGermain', beep=('G0', 0)), 'states written')
