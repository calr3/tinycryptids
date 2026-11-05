"""Emit lean/TinyCryptids/BrocardPrimes/Machine.lean from brocard_primes.txt (the design machine)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import leangen
print(leangen.machine_lean('brocard_primes.txt', 'BrocardPrimes'), 'states written')
