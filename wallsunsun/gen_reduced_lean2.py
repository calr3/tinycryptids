"""Emit lean/TinyCryptids/WallSunSun2/<Name>.lean for a merged machine of wallsunsun2.txt: its
transition function, the state map, and the transferred main theorem.
Usage: gen_reduced_lean2.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_lean('wallsunsun2.txt', sys.argv[1], 'WallSunSun2', sys.argv[2],
    '∃ p, Prime p ∧ p * p ∣ fib (wssIndex p)', 'haltAt_of h', opens=('TinyCryptids',))
print('written', sys.argv[2], n, 'states')
