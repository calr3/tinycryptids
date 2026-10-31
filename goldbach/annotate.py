"""Write a commented version of the 6-symbol Goldbach machine: a header (tape, algorithm),
a description of every state, and a comment on every transition.
Usage: python3 annotate.py machines/goldbach_10.txt machines/goldbach_10_annotated.txt"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm

HEADER = """\
; ============================================================================
; A {n}-state, 6-symbol Turing machine ({k} instructions) that
; HALTS IFF GOLDBACH'S CONJECTURE IS FALSE: started on a blank tape in the
; first state, it halts iff some even number 2n >= 4 is not the sum of two
; primes.
;
; THE HALT is the undefined transition of `e2` reading 5 (marked HALT below).
; The other undefined transitions are never used (`-`).
; Lean proof: lean/TinyCryptids/Goldbach/M10.lean,
; theorem TMK.Goldbach.M10.halts_iff (and halts_iff_not).
; Standard text: {std}
; ============================================================================
;
; SYMBOLS: 0 blank, 1 a cell, 2 = x (a marked cell), 3 = B (the boundary,
;   marked), 4 = b (the boundary, unmarked), 5 = s (the separator).
;
; TAPE at the start of each pair (p, q), p + q = n (blank elsewhere):
;     0 0 [P: 1^p] s [Q: 1^q] 0 0    (Q may hold one stale b, on its 4th cell
;                                     or later)
;
; ALGORITHM (as in ../build.py)
;   pairs    for each even n: (n - 2, 2), (n - 3, 3), ... Test P, then Q if P
;            is prime. Both prime: grow to (n, 2) for n + 2. One composite:
;            the separator moves one cell left (p - 1, q + 1). After (2, n - 2)
;            comes (1, n - 1): `e2` reads the separator on P's second cell and
;            the machine HALTS.
;   test     the primality of a block X (between two delimiters, 0 or s) by
;            trial division in place: the divisor d is X's first d cells D, the
;            rest R starts with the boundary; d | x iff d | r. `e1`, `e2` put
;            the boundary on the third cell (d = 2).
;   round    `mark` marks R's first cell B; a zigzag marks one cell of R (`zr`)
;            and one cell of D (`zl`); when D is fully marked, `rst` unmarks it
;            (a lazy reset). When R runs out, `chk` unmarks everything from the
;            right (B -> b). An unmarked cell of D: d does not divide r, `chk`
;            moves b one cell right (d + 1) and `mark` starts the next round.
;            The left delimiter reached: d | r, X is composite. `mark` reading
;            a delimiter: d = x, X is prime.
;   exits    prime P (`mark` reads s): test Q. Prime Q (`mark` reads 0): grow
;            (two cells after Q, `sh` writes s on Q's last cell, `wl` erases the
;            old one). Composite P (`chk` reads 0): `kr` erases b on the way to
;            the separator, then shift. Composite Q (`chk` reads s): shift at
;            once (s -> 1, `sh` writes s on P's last cell, `wl` returns).
;   boot     `sh` reading 0 runs the growth on the blank tape: (2, 2) after
;            13 steps.
; ============================================================================

blank_symbol: 0
"""

DESC = {
    'mark': 'start a round: mark R\'s first cell B; a delimiter: d = x, the block is prime',
    'zl': 'zigzag: run left to D\'s last unmarked cell and mark it',
    'zr': 'zigzag: run right to R\'s first unmarked cell and mark it; R used up: check',
    'rst': 'D fully marked: unmark it, mark its last cell; growth: the second new cell',
    'chk': 'R used up: unmark from the right (B -> b); then move b right (d + 1)',
    'e1': 'test entry: X\'s first cell',
    'e2': 'test entry: X\'s second cell; the separator here (p = 1): HALT',
    'kr': 'P composite: run right erasing b, to the separator',
    'sh': 'shift: write the separator one cell left of the old one',
    'wl': 'run left to P\'s first cell, erasing an old separator',
}

TRANS = {
    ('mark', 0): 'Q prime: growth, the first new cell', ('mark', 1): 'the boundary B',
    ('mark', 5): 'P prime: test Q',
    ('zl', 0): 'D fully marked (X = P): reset', ('zl', 1): 'mark a cell of D',
    ('zl', 2): '', ('zl', 3): '', ('zl', 5): 'D fully marked (X = Q): reset',
    ('zr', 0): 'R used up (X = Q): check', ('zr', 1): 'mark a cell of R', ('zr', 2): '',
    ('zr', 3): '', ('zr', 4): 'a stale b counts as a 1', ('zr', 5): 'R used up (X = P): check',
    ('rst', 0): 'growth: the second new cell', ('rst', 1): 'growth: the first new cell; shift from Q\'s last cell',
    ('rst', 2): 'unmark D', ('rst', 3): 'D unmarked: mark its last cell',
    ('chk', 0): 'D fully marked: P composite', ('chk', 1): 'an unmarked cell of D: d + 1',
    ('chk', 2): 'unmark', ('chk', 3): 'B -> b', ('chk', 4): 'the boundary one cell right',
    ('chk', 5): 'D fully marked: Q composite, shift',
    ('e1', 1): '', ('e2', 1): 'd = 2',
    ('kr', 1): '', ('kr', 4): 'erase b', ('kr', 5): 'the separator: shift',
    ('sh', 0): 'boot only', ('sh', 1): 'the new separator',
    ('wl', 0): 'P\'s first cell: test P', ('wl', 1): '', ('wl', 5): 'erase the old separator',
}

if __name__ == '__main__':
    order, ST, _ = tm.parse(open(sys.argv[1]).read())
    assert set(order) == set(DESC), set(order) ^ set(DESC)
    k = sum(t is not None for v in ST.values() for t in v)
    L = [HEADER.format(n=len(order), k=k, std=tm.to_standard(order, ST))]
    for q in order:
        L.append(f'{q}    ; {DESC[q]}')
        for b, t in enumerate(ST[q]):
            if t is None:
                L.append('    -    ; HALT' if (q, b) == ('e2', 5) else '    -'); continue
            c = TRANS[(q, b)]
            L.append(f'    {b} {t[0]} {t[1]} {t[2]}' + (f'    ; {c}' if c else ''))
        L.append('')
    out = '\n'.join(L)
    o2, S2, _ = tm.parse(out)
    assert o2 == order and S2 == ST
    open(sys.argv[2], 'w').write(out)
    print('written', sys.argv[2])
