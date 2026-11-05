"""Emit lean/TinyCryptids/Brocard/<Name>.lean for a merged machine: its transition
function, the state map from brocard.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('brocard.txt', sys.argv[1], 'Brocard', sys.argv[2],
    '∃ n m, 8 ≤ n ∧ fact n + 1 = m * m',
    'haltAt_of_sol h', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
