"""Emit lean/TinyCryptids/AgohGiuga/<Name>.lean for a merged machine: its transition
function, the state map from agoh_giuga.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('agoh_giuga.txt', sys.argv[1], 'AgohGiuga', sys.argv[2],
    '∃ n, 2 ≤ n ∧ ¬ Prime n ∧ n ∣ powSum n (n - 1) + 1',
    'haltAt_of h', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
