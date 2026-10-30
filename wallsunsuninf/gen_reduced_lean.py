"""Emit lean/TinyCryptids/WallSunSunInf/<Name>.lean for a merged machine of
wallsunsuninf_seeded.txt: its transition function, the state map, and the transferred
theorems.  Usage: gen_reduced_lean.py machines/merged.txt Name"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
n = leangen.reduced_beep_lean('wallsunsuninf_seeded.txt', sys.argv[1], 'WallSunSunInf', sys.argv[2],
    ('q9', 0), '¬ InfinitelyManyWallSunSunPrimes', opens=('TinyCryptids',))
print('written', sys.argv[2], n, 'states')
