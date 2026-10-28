"""Emit lean/TinyCryptids/ABC/Machine.lean from abc.txt (the design machine): `delta`, and
`deltaQ`, the design without its beep (xe3 reading 0) and its boop (xq6 reading 0)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
os.makedirs(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'lean', 'TinyCryptids', 'ABC'), exist_ok=True)
print(leangen.machine_lean('abc.txt', 'ABC', beep=('xe3', 0), boop=('xq6', 0)), 'states written')
