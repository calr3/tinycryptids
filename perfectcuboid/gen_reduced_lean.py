"""Emit lean/TinyCryptids/PerfectCuboid/<Name>.lean for a merged machine: its transition
function, the state map from perfectcuboid.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('perfectcuboid.txt', sys.argv[1], 'PerfectCuboid', sys.argv[2],
    '∃ a b c d e f g : Nat, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ a * a + b * b = d * d ∧ '
    'a * a + c * c = e * e ∧ b * b + c * c = f * f ∧ a * a + b * b + c * c = g * g',
    'haltAt_of h')
print('written', sys.argv[2], n, 'states')
