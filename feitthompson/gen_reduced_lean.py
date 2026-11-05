"""Emit lean/TinyCryptids/FeitThompson/<Name>.lean for a merged machine: its transition
function, the state map from feitthompson.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('feitthompson.txt', sys.argv[1], 'FeitThompson', sys.argv[2],
    '∃ p q, Prime p ∧ Prime q ∧ p ≠ q ∧ rep p q ∣ rep q p',
    'haltAt_of (ft_iff.mp h)', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
