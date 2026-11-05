"""Emit lean/TinyCryptids/Beal/<Name>.lean for a merged machine: its transition
function, the state map from beal.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('beal.txt', sys.argv[1], 'Beal', sys.argv[2],
    '∃ a b c x y z, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ 3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧ Nat.gcd a b = 1 ∧ a ^ x + b ^ y = c ^ z',
    'haltAt_of h')
print('written', sys.argv[2], n, 'states')
