"""Emit lean/TinyCryptids/Oppermann/<Name>.lean for a merged machine: its transition
function, the state map from oppermann.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('oppermann.txt', sys.argv[1], 'Oppermann', sys.argv[2],
    '∃ n, 2 ≤ n ∧ ((∀ p, n * n - n < p → p < n * n → ¬ Prime p) ∨ '
    '(∀ p, n * n < p → p < n * n + n → ¬ Prime p))',
    'haltAt_of h', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
