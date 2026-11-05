"""Emit lean/TinyCryptids/Gilbreath/<Name>.lean for a merged machine: its transition
function, the state map from gilbreath.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('gilbreath.txt', sys.argv[1], 'Gilbreath', sys.argv[2],
    '∃ N k, 1 ≤ k ∧ k < (primesBelow N).length ∧ (gilbreathRow (primesBelow N) k).head? ≠ some 1',
    'haltAt_of (fail_iff.1 h)', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
