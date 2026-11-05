"""Emit lean/TinyCryptids/Barker/<Name>.lean for a merged machine and transfer `halts_iff`.
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('barker.txt', sys.argv[1], 'Barker', sys.argv[2],
    '∃ a : List Int, 13 < a.length ∧ IsBarker a',
    'haltAt_of h', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
