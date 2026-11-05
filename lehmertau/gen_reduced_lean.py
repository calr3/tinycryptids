"""Emit lean/TinyCryptids/LehmerTau/<Name>.lean for a merged machine: its transition
function, the state map from lehmertau.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('lehmertau.txt', sys.argv[1], 'LehmerTau', sys.argv[2],
    '∃ n, 1 ≤ n ∧ tau756 n = 0', 'haltAt_of h', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
