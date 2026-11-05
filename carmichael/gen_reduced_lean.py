"""Emit lean/TinyCryptids/Carmichael/<Name>.lean for a merged machine: its transition
function, the state map from carmichael.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('carmichael.txt', sys.argv[1], 'Carmichael', sys.argv[2],
    '∃ m, 1 ≤ m ∧ ∀ n, n ≠ m → totient n ≠ totient m',
    'haltAt_of h', opens=('TinyCryptids',))
print('written', sys.argv[2], n, 'states')
