"""Emit lean/TinyCryptids/BrocardPrimes/<Name>.lean for a merged machine: its transition
function, the state map from brocard_primes.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('brocard_primes.txt', sys.argv[1], 'BrocardPrimes', sys.argv[2],
    '∃ p q, 3 ≤ p ∧ TinyCryptids.Prime p ∧ TinyCryptids.Prime q ∧ p < q ∧ '
    '(∀ r, p < r → r < q → ¬ TinyCryptids.Prime r) ∧ '
    'TinyCryptids.primeCount (q ^ 2) - TinyCryptids.primeCount (p ^ 2) < 4',
    'haltAt_of h', opens=[])
print('written', sys.argv[2], n, 'states')
