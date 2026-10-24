"""Trace dfin from its input: tape with absolute cells, head marked, for m = 0."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build

build.build()

def show(tape, h, lo=-12, hi=16):
    return ''.join(('.' if i == h else ('1' if tape.get(i, 0) else '.')) if i != h
                   else '[' + ('1' if tape.get(i, 0) else '.') + ']'
                   for i in range(lo, hi + 1))

# YR Y = 0 0 0 1 1 1 0 Y  (left of head: F F 1 1 1 F Y); head F; right F F blank
# absolute: cell -7..-1 = 0 0 1 1 1 0 Y(blank), cell 0 = 0, cell 1 = 0, cell 2 = 0 (blank)
tape = {}
for i, v in enumerate([0, 0, 1, 1, 1, 0]):   # i = 0..5 -> cells -6..-1
    tape[-6 + i] = v
h = 0
state = 't1'
for k in range(14):
    print(f'{k:3d} {state:4s} {show(tape, h)}')
    t = build.ST[state][tape.get(h, 0)]
    if t is None:
        print('HALT')
        break
    w, d, q = t
    tape[h] = w
    h += 1 if d == 'R' else -1
    state = q
