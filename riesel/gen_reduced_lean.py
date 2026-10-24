"""Emit lean/TinyCryptids/Riesel/<Name>.lean for a merged machine: its transition
function, the state map from riesel.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('riesel.txt', sys.argv[1], 'Riesel', sys.argv[2],
    '∀ k, k % 2 = 1 → k < 509203 → ∃ n, 1 ≤ n ∧ Prime (k * 2 ^ n - 1)',
    'haltAt_of h', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
