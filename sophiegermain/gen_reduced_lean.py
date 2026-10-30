"""Emit lean/TinyCryptids/SophieGermain/<Name>.lean for a merged machine: its transition
function, the state map from sophiegermain.txt, the beep's exclusivity, and the transferred
main theorems (`quasihalts_iff`, `never_halts`).
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_beep_lean('sophiegermain.txt', sys.argv[1], 'SophieGermain', sys.argv[2], ('G0', 0),
    'FinitelyManySophieGermainPrimes', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
