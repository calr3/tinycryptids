"""Write a commented version of the 4-symbol twin prime machine: a header (tape, algorithm),
a description of every state, and a comment on every transition.
Usage: python3 annotate.py twinprimes4.txt machines/twinprimes4_10_annotated.txt"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'tools'))
import tm

HEADER = """\
; ============================================================================
; A {n}-state, 4-symbol BEEPING Turing machine ({k} instructions) that
; QUASIHALTS IFF THE TWIN PRIME CONJECTURE IS FALSE.
;
; THE BEEP is the transition of state `beep` reading 0 (marked BEEP below).
; Started on a blank tape in the first state, the machine never halts. It
; takes the beep transition once at step 2, then once for every lesser twin
; prime p (p and p + 2 both prime) other than 5, in increasing order: 3, 11,
; 17, 29, 41, ... So it beeps infinitely often iff there are infinitely many
; twin primes. `-` marks transitions that are never used.
; Lean proof: lean/TinyCryptids/TwinPrimes4/Main.lean,
; theorem TMK.TwinPrimes4.quasihalts_iff (and never_halts).
; Standard text: {std}
; ============================================================================
;
; SYMBOLS: 0 blank, 1 an R cell, 2 the D marker or the R cursor, 3 a D cell.
;
; THE IDEA (as in ../build.py): for m >= 3, m and m + 2 are both prime iff no
;   d with 2 <= d <= m - 1 divides m or m + 2. The machine tests candidates m
;   by trial division with d = 2, 3, ...; one mod walk per d tests both m and
;   m + 2.
;
; TAPE (blank elsewhere):   D R
;   D: d cells, 3s except the MARKER 2 on cell c: a counter mod d.
;   R: r = m - d cells, 1s; during the mod walk the CURSOR 2 moves left.
;
; ALGORITHM (candidate m, divisor d)
;   walk     the marker starts on D's last cell. r times: make the cursor one
;            cell further left (R's last cell first), run left to the marker
;            and move it one cell right (past D's last cell, `adv` reads R's
;            cell 0, a 1 or the cursor: wrap to cell 0), run right to the
;            cursor and fill it. The marker ends on cell (m - 1) mod d.
;   check    `cur` reaches D's last cell: the marker on d - 1 means d | m, on
;            d - 3 means d | m + 2: FAIL. On d - 2, or further left, d passed.
;   shift    d := d + 1, r := r - 1: erase the marker, run right, make R's
;            cell 0 the marker (D's new last cell); run to R's end, walk.
;   rebuild  FAIL: turn D's 3s into 1s (`reb` zigzags: 3 -> 1 R, back over
;            the 1), write a 3 left of the tape and make the next cell the
;            marker: D = 3 2, R = 1^(m-1): candidate m + 1, d = 2.
;   BEEP     R empty after a shift: d = m, every d < m passed. The walk ends
;            at once, the check fails (m divides m), and `reb` reads the blank
;            right of D: a 3 there, `grow` writes a 1, `beep` reads the blank:
;            BEEP. The rebuild follows: candidate m + 3 (m + 1 and m + 2 are no
;            lesser twin primes for m >= 5; after m = 3 the twin prime 5 is
;            skipped).
;   start    the blank tape takes the beep path with an empty D (the beep at
;            step 2) and becomes candidate 3.
; ============================================================================

blank_symbol: 0
"""

DESC = {
    'reb': 'rebuild: run left turning 3s into 1s (zigzag); at the blank write the new D cell',
    'toR': 'run right to the cursor and fill it; at R\'s end: start the walk',
    'cur': 'the cursor one cell left; on D\'s last cell: the check (d - 1)',
    'toM': 'run left to the marker',
    'adv': 'the marker one cell right; past D\'s last cell: wrap',
    'wrap': 'wrap: run left to the blank before D; also: run left to the marker (d passed)',
    'chk2': 'the check: D\'s cell d - 2',
    'chk3': 'the check: D\'s cell d - 3',
    'grow': 'shift: run right, the marker on R\'s cell 0 (d + 1, r - 1); rebuild: the marker on cell 1',
    'beep': 'R was empty (d = m): the BEEP',
}

TRANS = {
    ('reb', 0): 'the blank left of the tape: new D cell 0', ('reb', 1): '',
    ('reb', 3): 'a D cell becomes an R cell; step back over the 1',
    ('toR', 0): 'R\'s end: the walk starts on R\'s last cell', ('toR', 1): '',
    ('toR', 2): 'fill the cursor', ('toR', 3): '',
    ('cur', 1): 'the cursor', ('cur', 2): 'the marker on d - 1: d | m, FAIL',
    ('cur', 3): 'the walk is over: check d - 2',
    ('toM', 1): '', ('toM', 2): 'erase the marker', ('toM', 3): '',
    ('adv', 1): 'past D\'s last cell: wrap', ('adv', 2): 'past D\'s last cell (the cursor on R\'s cell 0): wrap',
    ('adv', 3): 'the marker',
    ('wrap', 0): 'D\'s cell 0', ('wrap', 2): 'the marker (d passed): erase it, shift', ('wrap', 3): '',
    ('chk2', 2): 'the marker on d - 2: d passed, shift', ('chk2', 3): '',
    ('chk3', 2): 'the marker on d - 3: d | m + 2, FAIL', ('chk3', 3): 'd passed: run to the marker',
    ('grow', 0): 'beep path: a 1 after the 3', ('grow', 1): 'the marker: D\'s new last cell',
    ('grow', 3): '',
    ('beep', 0): 'BEEP; then rebuild',
}

if __name__ == '__main__':
    order, ST, _ = tm.parse(open(sys.argv[1]).read())
    assert set(order) == set(DESC), set(order) ^ set(DESC)
    k = sum(t is not None for v in ST.values() for t in v)
    L = [HEADER.format(n=len(order), k=k, std=tm.to_standard(order, ST))]
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
