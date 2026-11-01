"""Emit lean/TinyCryptids/Pillai/Machine.lean from pillai.txt (the design machine): `delta`, and
`deltaQ`, the design without its beep (zX3 reading 1) and its boop (zX3 reading 0)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
os.makedirs(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'lean', 'TinyCryptids', 'Pillai'), exist_ok=True)
print(leangen.machine_lean('pillai.txt', 'Pillai', beep=('zX3', 1), boop=('zX3', 0)), 'states written')
