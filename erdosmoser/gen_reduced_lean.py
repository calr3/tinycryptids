"""Emit lean/TinyCryptids/ErdosMoser/<Name>.lean for a merged machine: its transition
function, the state map from erdosmoser.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('erdosmoser.txt', sys.argv[1], 'ErdosMoser', sys.argv[2],
    '∃ k m, 2 ≤ k ∧ 1 ≤ m ∧ powSum m k = m ^ k', 'haltAt_of h', opens=('TinyCryptids',))
print('written', sys.argv[2], n, 'states')
