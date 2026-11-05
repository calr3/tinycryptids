"""Emit lean/TinyCryptids/ZeroFree/<Name>.lean for a merged machine: its transition
function, the state map from zerofree.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('zerofree.txt', sys.argv[1], 'ZeroFree', sys.argv[2],
    '∃ n, 86 < n ∧ ∀ k, 2 ^ n / 10 ^ k ≠ 0 → (2 ^ n / 10 ^ k) % 10 ≠ 0',
    'haltAt_of h')
print('written', sys.argv[2], n, 'states')
