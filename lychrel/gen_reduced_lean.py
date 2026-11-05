"""Emit lean/TinyCryptids/Lychrel/<Name>.lean for a merged machine: its transition
function, the state map from lychrel.txt, and the transferred main theorem.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('lychrel.txt', sys.argv[1], 'Lychrel', sys.argv[2],
    '∃ k, rev10 (iterate (fun x => x + rev10 x) k 196) = iterate (fun x => x + rev10 x) k 196',
    'haltAt_of h', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
