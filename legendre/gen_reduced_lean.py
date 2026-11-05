"""Emit lean/TinyCryptids/Legendre/<Name>.lean for a merged machine: its transition
function, the state map from legendre.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('legendre.txt', sys.argv[1], 'Legendre', sys.argv[2],
    '∃ n, 1 ≤ n ∧ ∀ p, n ^ 2 < p → p < (n + 1) ^ 2 → ¬ Prime p',
    'haltAt_of_fails (let ⟨n, h1, h2⟩ := h; ⟨n, h1, h2⟩)', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
