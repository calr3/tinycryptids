"""Emit lean/TinyCryptids/Goormaghtigh/<Name>.lean for a merged machine: its transition
function, the state map from goormaghtigh.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('goormaghtigh.txt', sys.argv[1], 'Goormaghtigh', sys.argv[2],
    '∃ x y m n, 1 < y ∧ y < x ∧ 2 < m ∧ 2 < n ∧ rep x m = rep y n ∧ rep x m ≠ 31 ∧ rep x m ≠ 8191',
    'haltAt_of_conj h', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
