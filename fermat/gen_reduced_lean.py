"""Emit lean/TinyCryptids/Fermat/<Name>.lean for a merged machine: its transition
function, the state map from fermat.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('fermat.txt', sys.argv[1], 'Fermat', sys.argv[2],
    '∃ E x y z : Nat, 3 ≤ E ∧ 1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧ x ^ E + y ^ E = z ^ E',
    'haltAt_of_sol h', opens=[])
print('written', sys.argv[2], n, 'states')
