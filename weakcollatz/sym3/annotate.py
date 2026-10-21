"""Write a commented version of the 3-symbol machine: a header (tape, algorithm), a
description of every state, and a comment on every transition.
Usage: python3 annotate.py weakcollatz3.txt machines/weakcollatz3_10_annotated.txt"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'tools'))
import tm

HEADER = """\
; ============================================================================
; A {n}-state, 3-symbol Turing machine that HALTS IFF THE COLLATZ MAP HAS A
; CYCLE OTHER THAN 1 -> 4 -> 2 -> 1 (the weak Collatz conjecture is false).
; Start on a blank tape (0) in the first state. A transition to `halt` halts;
; `-` marks transitions that are never used (they would halt too).
; Lean proof: lean/TinyCryptids/WeakCollatz3/Main.lean, theorem TM3.WeakCollatz.halts_iff.
; Standard text: {std}
; ============================================================================
;
; SHORTCUT MAP: T(v) = v/2 (v even), (3v+1)/2 (v odd).  T has a cycle through
;   some n >= 3 iff the Collatz map has a cycle other than 1 -> 4 -> 2 -> 1.
;
; ALGORITHM: rounds M = 3, 4, ...: v := M, then v := T(v) until v = 1 or
;   v >= M; HALT iff v = M.
;
; TAPE C(M, v): cells 0 .. M-2 hold 1 except the HOLE (0) at cell v-1; cell
;   M-1 holds the END MARK 2; the rest is blank.  Head on cell 0 in `disp`.
;   (v = M: M-1 ones, then the end mark, which is the hole.)
;
; STEP:
;   v = 1    write 2 on the hole (cell 0), make the end mark a 1, write a new
;            end mark after it, go home (turning the 2 on cell 0 into a 1).
;   halving  `disp` writes a MARKER (0) on cell 0; per round trip the hole moves
;            left one cell and the marker right one.  Neighbours (v = 2k): the
;            marker (cell k-1) is the result hole.  Same cell (v = 2k+1): the
;            hole is on cell k.
;   odd      the ODD MARKER (2) goes on cell k, the hole on k+1; per round trip
;            the odd marker moves left one cell and the hole right two (on the
;            end mark the hole leaves the 2).  When the marker passes cell 0
;            the hole is at 3k+1 = T(v)-1: if it is the end mark, T(v) = M:
;            HALT.  If the hole has to pass the end mark first (T(v) > M): the
;            end mark becomes a 1, a new one goes after it, go home.
;   home     run left over 1s and 2s (writing 1s) to cell -1, step right.
; The blank tape acts as v = 1 and gives C(3, 3).
; ============================================================================

blank_symbol: 0
"""

DESC = {
    'disp': 'dispatch on cell 0: 0 = the hole (v = 1); 1 = write the marker, start halving',
    'toH': 'halving: run right to the hole, fill it (the end mark stays 2)',
    'newH': 'the new hole: one cell left (halving) or two right (odd); 0: the marker (v even)',
    'back': 'run left to a marker, fill it: 0 = halving marker, 2 = odd marker',
    'mark': 'halving: the marker moves right; 0: it meets the hole (v odd)',
    'markO': 'odd: the odd marker moves left; 0: it passed cell 0',
    'toHO': 'odd: run right to the hole, fill it; also v = 1: run to the end mark',
    'hop': 'odd: skip a cell; past the end mark: write the new end mark',
    'home': 'run left over 1s and 2s; at cell -1 step right: the next macro step',
    'check': 'end of the odd step: run right to the hole; the end mark means T(v) = M',
}

TRANS = {
    ('disp', 0): 'v = 1: next round', ('disp', 1): 'the marker', ('disp', 2): '',
    ('toH', 0): 'fill the hole', ('toH', 1): '', ('toH', 2): 'the hole is the end mark (v = M)',
    ('newH', 0): 'the marker (v even): it is the result hole', ('newH', 1): 'the new hole',
    ('newH', 2): 'the end mark: the hole is on it',
    ('back', 0): 'fill the halving marker', ('back', 1): '', ('back', 2): 'fill the odd marker',
    ('mark', 0): 'met the hole: v odd, the odd marker', ('mark', 1): 'the marker', ('mark', 2): '',
    ('markO', 0): 'passed cell 0', ('markO', 1): 'the odd marker', ('markO', 2): '',
    ('toHO', 0): 'fill the hole', ('toHO', 1): '', ('toHO', 2): 'the hole is on the end mark: T(v) > M',
    ('hop', 0): 'the new end mark', ('hop', 1): '', ('hop', 2): 'past the end mark: T(v) > M',
    ('home', 0): 'cell -1', ('home', 1): '', ('home', 2): 'a marker or the v = 1 2: fill it',
    ('check', 0): 'the hole: T(v) < M', ('check', 1): '', ('check', 2): 'T(v) = M: a cycle',
}

if __name__ == '__main__':
    order, ST, _ = tm.parse(open(sys.argv[1]).read())
    assert set(order) == set(DESC), set(order) ^ set(DESC)
    L = [HEADER.format(n=len(order), std=tm.to_standard(order, ST))]
    for q in order:
        L.append(f'{q}    ; {DESC[q]}')
        for b, t in enumerate(ST[q]):
            if t is None: L.append('    -'); continue
            c = TRANS[(q, b)]
            L.append(f'    {b} {t[0]} {t[1]} {t[2]}' + (f'    ; {c}' if c else ''))
        L.append('')
    out = '\n'.join(L)
    o2, S2, _ = tm.parse(out)
    assert o2 == order and S2 == ST
    open(sys.argv[2], 'w').write(out)
    print('written', sys.argv[2])
