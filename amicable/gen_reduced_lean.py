"""Emit lean/TinyCryptids/Amicable/<Name>.lean for a merged machine: its transition
function, the state map from amicable.txt, the beep's exclusivity, and the transferred
main theorems (`quasihalts_iff`, `never_halts`).
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_beep_lean('amicable.txt', sys.argv[1], 'Amicable', sys.argv[2], ("H5", 0),
    '¬ InfinitelyManyAmicable', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
