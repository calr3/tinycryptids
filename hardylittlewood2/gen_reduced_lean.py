"""Emit lean/TinyCryptids/HardyLittlewood2/<Name>.lean for a merged machine: its transition
function, the state map from hardylittlewood2.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('hardylittlewood2.txt', sys.argv[1], 'HardyLittlewood2', sys.argv[2],
    '∃ x y, 2 ≤ x ∧ 2 ≤ y ∧ primeCount x + primeCount y < primeCount (x + y)',
    'haltAt_of h', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
