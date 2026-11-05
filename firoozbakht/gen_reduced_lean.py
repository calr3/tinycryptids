"""Emit lean/TinyCryptids/Firoozbakht/<Name>.lean for a merged machine: its transition
function, the state map from firoozbakht.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('firoozbakht.txt', sys.argv[1], 'Firoozbakht', sys.argv[2],
    '∃ p q, Prime p ∧ Prime q ∧ p < q ∧ (∀ r, p < r → r < q → ¬ Prime r) ∧ '
    'p ^ (primeCount p + 1) ≤ q ^ primeCount p',
    'haltAt_of h', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
