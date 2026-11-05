"""Emit lean/TinyCryptids/ErdosStraus/<Name>.lean for a merged machine: its transition
function, the state map from erdos_straus.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('erdos_straus.txt', sys.argv[1], 'ErdosStraus', sys.argv[2],
    '∃ n, 2 ≤ n ∧ ∀ x y z, 1 ≤ x → 1 ≤ y → 1 ≤ z → 4 * x * y * z ≠ n * (x * y + y * z + z * x)',
    'haltAt_of h')
print('written', sys.argv[2], n, 'states')
