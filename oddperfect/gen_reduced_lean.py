"""Emit lean/TinyCryptids/OddPerfect/<Name>.lean for a merged machine: its transition
function, the state map from oddperfect.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('oddperfect.txt', sys.argv[1], 'OddPerfect', sys.argv[2],
    '∃ n, n % 2 = 1 ∧ properDivSum n = n',
    'haltAt_of_opn h', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
