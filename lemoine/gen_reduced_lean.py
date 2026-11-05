"""Emit lean/TinyCryptids/Lemoine/<Name>.lean for a merged machine: its transition
function, the state map from lemoine.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('lemoine.txt', sys.argv[1], 'Lemoine', sys.argv[2],
    '∃ n, 7 ≤ n ∧ n % 2 = 1 ∧ ∀ p q, Prime p → Prime q → p + 2 * q ≠ n',
    'haltAt_of h', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
