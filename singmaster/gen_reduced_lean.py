"""Emit lean/TinyCryptids/Singmaster/<Name>.lean for a merged machine: its transition
function, the state map from singmaster.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('singmaster.txt', sys.argv[1], 'Singmaster', sys.argv[2],
    '∃ N, 2 ≤ N ∧ ∃ l : List (Nat × Nat), l.Nodup ∧ 9 ≤ l.length ∧ ∀ x ∈ l, choose x.1 x.2 = N',
    'haltAt_of h', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
