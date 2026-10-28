"""Emit lean/TinyCryptids/ABC/<Name>.lean for a merged machine: its transition function, the
state map from abc.txt, the exclusivity of the beep and the boop, and the transferred main
theorems (`repeats_iff`, `never_halts`).
Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_beepboop_lean('abc.txt', sys.argv[1], 'ABC', sys.argv[2], ('xe3', 0), ('xq6', 0),
    '¬ ABCConjecture', opens=['TinyCryptids'])
print('written', sys.argv[2], n, 'states')
