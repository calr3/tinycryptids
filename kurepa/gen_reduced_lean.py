"""Emit lean/TinyCryptids/Kurepa/<Name>.lean for a merged machine: its transition
function, the state map from kurepa.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('kurepa.txt', sys.argv[1], 'Kurepa', sys.argv[2],
    '∃ p, Prime p ∧ 2 < p ∧ p ∣ leftFact p',
    'haltAt_of (kurepa_iff.mpr h)', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
