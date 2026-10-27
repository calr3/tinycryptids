"""Emit lean/TinyCryptids/FermatPrimes/<Name>.lean for a merged machine: its transition
function, the state map from fermatprimes.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('fermatprimes.txt', sys.argv[1], 'FermatPrimes', sys.argv[2],
    '∃ n, 5 ≤ n ∧ Prime (2 ^ 2 ^ n + 1)',
    'haltAt_of (fp_big_iff.mp h)', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
