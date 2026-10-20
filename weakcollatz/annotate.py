"""Write a commented version of the machine: a header (tape, algorithm), a
description of every state, and a comment on every transition.
Usage: python3 annotate.py weakcollatz.txt machines/weakcollatz_14_annotated.txt"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm

HEADER = """\
; ============================================================================
; A {n}-state, 2-symbol Turing machine that HALTS IFF THE COLLATZ MAP HAS A
; CYCLE OTHER THAN 1 -> 4 -> 2 -> 1 (the weak Collatz conjecture is false).
; Start on a blank tape in the first state. A transition to `halt` halts.
; Lean proof: lean/TinyCryptids/WeakCollatz/Main.lean, theorem TM.WeakCollatz.halts_iff.
; Standard text: {std}
; ============================================================================
;
; SHORTCUT MAP: T(v) = v/2 (v even), (3v+1)/2 (v odd).  T has a cycle through
;   some n >= 3 iff the Collatz map has a cycle other than 1 -> 4 -> 2 -> 1.
;
; ALGORITHM: rounds M = 2, 3, ...: v := M, then v := T(v) until v = 1 or
;   v >= M; HALT iff v = M.
;
; TAPE C(M, v): cells 0 .. M-1 hold 1 except the HOLE at cell v-1; the rest
;   is blank.  Head on cell 0 in `disp`.  (v = M: M-1 ones, the hole is the
;   first blank.)  The blank tape is C(1, 1).
;
; STEP:
;   v = 1    fill the hole (cell 0), go home: the first blank is the next
;            round's hole.
;   halving  `disp` writes a MARKER on cell 0; per round trip the hole moves
;            left one cell and the marker right one.  Neighbours (v = 2k): the
;            marker (cell k-1) is the result hole.  Same cell (v = 2k+1): the
;            hole is on cell k.
;   odd      the hole moves to k+1, the marker to k-1; per round trip the
;            marker moves left one cell and the hole right two.  When the
;            marker passes cell 0 the hole is at 3k+1 = T(v)-1; a blank after it
;            means T(v) = M: HALT.  The hole running off the block (T(v) > M):
;            fill the marker, go home.
;   home     run left to cell -1, step right.
; ============================================================================

blank_symbol: 0
"""

DESC = {
    'disp': 'dispatch on cell 0: 0 = the hole (v = 1); 1 = write the marker, start halving',
    'toH': 'halving: run right to the hole, fill it',
    'stepH': 'halving: the hole moves left; 0: the marker is there (v even); also restores a hole',
    'back': 'halving: run left to the marker, fill it',
    'mark': 'halving: the marker moves right; 0: it meets the hole (v odd)',
    'hop2': 'odd: second cell of the hole\'s jump, the new hole; 0: off the block',
    'backO': 'odd: run left to the marker, fill it',
    'markO': 'odd: the marker moves left; 0: it passed cell 0',
    'toHO': 'odd: run right to the hole, fill it',
    'hop1': 'odd: first cell of the hole\'s jump; 0: off the block',
    'toHN': 'end of the odd step: run right to the hole',
    'peek': 'the cell after the hole: 0 = T(v) = M, halt; 1 = go home',
    'home': 'run left over 1s; at cell -1 step right: the next macro step',
    'fill': 'after the hole ran off the block: run left, fill the marker, go home',
}

TRANS = {
    ('disp', 0): 'v = 1: next round', ('disp', 1): 'the marker',
    ('toH', 0): 'fill the hole', ('toH', 1): '',
    ('stepH', 0): 'the marker (v even) or a hole: go home', ('stepH', 1): 'the new hole',
    ('back', 0): 'fill the marker', ('back', 1): '',
    ('mark', 0): 'met the hole: v odd', ('mark', 1): 'the marker',
    ('hop2', 0): 'off the block: T(v) > M', ('hop2', 1): 'the new hole',
    ('backO', 0): 'fill the marker', ('backO', 1): '',
    ('markO', 0): 'passed cell 0', ('markO', 1): 'the marker',
    ('toHO', 0): 'fill the hole', ('toHO', 1): '',
    ('hop1', 0): 'off the block: T(v) > M', ('hop1', 1): '',
    ('toHN', 0): 'the hole', ('toHN', 1): '',
    ('peek', 0): 'T(v) = M: a cycle', ('peek', 1): 'T(v) < M',
    ('home', 0): 'cell -1', ('home', 1): '',
    ('fill', 0): 'fill the marker', ('fill', 1): '',
}

if __name__ == '__main__':
    order, ST, _ = tm.parse(open(sys.argv[1]).read())
    assert set(order) == set(DESC), set(order) ^ set(DESC)
    L = [HEADER.format(n=len(order), std=tm.to_standard(order, ST))]
    for q in order:
        L.append(f'{q}    ; {DESC[q]}')
        for b, t in enumerate(ST[q]):
            c = TRANS[(q, b)]
            L.append(f'    {b} {t[0]} {t[1]} {t[2]}' + (f'    ; {c}' if c else ''))
        L.append('')
    out = '\n'.join(L)
    o2, S2, _ = tm.parse(out)
    assert o2 == order and S2 == ST
    open(sys.argv[2], 'w').write(out)
    print('written', sys.argv[2])
