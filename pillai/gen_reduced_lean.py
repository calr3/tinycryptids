"""Emit lean/TinyCryptids/Pillai/<Name>.lean for a merged machine: its transition function, the
state map from pillai.txt, the exclusivity of the beep and the boop, and the transferred main
theorems (`repeats_iff`, `never_halts`).
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_beepboop_lean('pillai.txt', sys.argv[1], 'Pillai', sys.argv[2], ('zX3', 1), ('zX3', 0),
    '¬ PillaiConjecture', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
