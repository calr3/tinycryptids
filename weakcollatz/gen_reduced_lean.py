"""Emit lean/TinyCryptids/WeakCollatz/<Name>.lean for a merged machine: its transition
function, the state map from weakcollatz.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('weakcollatz.txt', sys.argv[1], 'WeakCollatz', sys.argv[2],
    '∃ n k, 0 < n ∧ 0 < k ∧ iterate collatz k n = n ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4',
    'haltAt_of_cycle h', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
