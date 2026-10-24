"""Print the cell tape of abstract configurations, same format as probe37, so
they can be compared with the real machine's checkpoints.

Cell model: a Cfg is (head content, left stream, right stream) where the head
cell is the right stream's first element and the left stream holds the cells to
the left, nearest first.
"""
import sys

F = 0
T = 1

def ones(n, s):
    return (True,) * n + tuple(s)

def grp(u, s):
    return (True, u % 2 == 1, u // 2 % 2 == 1, u // 4 % 2 == 1, u // 8 % 2 == 1) + tuple(s)

def Cs(v):
    return (grp(v % 16, b'') + grp(v // 16 % 16, b'') + grp(v // 256 % 16, b'') +
            grp(v // 4096 % 16, b'') + grp(v // 65536 % 16, b''))

CONS = lambda a, s: (a,) + tuple(s)
TL = lambda s: s[1:]
BLANK = ()

def YR(Y):
    return CONS(False, CONS(False, CONS(False, CONS(True, CONS(True, CONS(True, CONS(False, Y)))))))

def MW(Y, d, r, h, j):
    L = ones(h, CONS(False, Y))
    R = CONS(False, ones(d - h, CONS(False, CONS(False, ones(j, CONS(False, ones(r + 1 - j, BLANK)))))))
    return L, R

def dump(L, R, lo=-16, hi=16):
    # L nearest-first to the left; R[0] is the head cell
    tape = {}
    for i, v in enumerate(L):
        tape[-1 - i] = v
    for i, v in enumerate(R):
        tape[i] = v
    return ''.join('[1]' if i == 0 and tape.get(0) else '[.]' if i == 0 else
                   ('1' if tape.get(i) else '.') for i in range(lo, hi + 1))

Y = ones(7, CONS(False, Cs(0)))
for (d, r, h, j) in [(3, 1, 3, 0), (3, 2, 3, 0), (3, 0, 3, 0)]:
    L, R = MW(Y, d, r, h, j)
    print(f'MW Y 3 {r} {h} {j}:')
    print('   ', dump(L, R))
