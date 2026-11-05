"""Write a commented version of a merged machine.

Each state of the merged machine is a class of states of the design (singmaster.txt, generated
by build.py). The merged state is named after its non-seed roles, listed with a description,
and every transition line is tagged with the roles that use it.
Usage: python3 annotate.py merged.txt out.txt LeanName
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
from collections import defaultdict
import tm, build, leangen

HEADER = """\
; ============================================================================
; A {n}-state, 2-symbol Turing machine that HALTS IFF SOME N >= 2 OCCURS AT
; LEAST 9 TIMES IN PASCAL'S TRIANGLE (Singmaster's bound 8 fails).
; Start on a blank tape in the first state. A transition to `halt` halts.
; Lean proof: lean/TinyCryptids/Singmaster/{lean}.lean, theorem TM.Singmaster.{lean}.halts_iff.
; ============================================================================
;
; HOW TO READ THIS FILE
;   The machine is the {N}-state design of build.py / singmaster.txt with states
;   merged. States are merged only when their defined transitions agree, so
;   each state below plays one or more ROLES of the design (its name joins
;   them). Each transition line is tagged [role] with the role(s) that use it.
;   A '-' line is never used.
;
; THE IDEA
;   Every occurrence of N >= 2 is in a row n <= N, and row N holds N exactly
;   twice (k = 1, N - 1). So for N = 2, 3, ... the machine counts the entries
;   equal to N in rows 0 .. N-1 and halts at 7. The triangle stays on the tape
;   and grows by one row per N.
;
; TAPE (unary: a block of v + 2 cells holds v; a hole is a single 0):
;      C 0 N 000 row0 000 row1 000 ... 000 row(N-1)
;   C: 9 cells, a hole at cell 1 + (matches so far); halt when a match finds
;   the separator two cells right of the hole.  N: N + 2 cells, a cursor hole
;   (at cell N between comparisons).  Entries of a row separated by 00.
;
; ONE N:  compare each entry E with N: E's cursor moves right from cell 1, N's
;   cursor left from cell N, in lockstep; E = N iff E's cursor is exhausted
;   in the round where N's cursor is at cell 1 (then C += 1).  At the end of
;   the triangle (four 0s): the next row is built at the end from the last row,
;   read right to left; for each cell of a source block the last two blocks of
;   the new row grow by 1 (append two cells, move the separator one cell
;   right); a new source block starts a new block (1 00 111).  Then N gets a
;   cell on its left (C moves one cell left) and C's hole goes back to cell 1.
;   seed: C, N = 1, row 0, entering at the end of the triangle.
; ============================================================================

blank_symbol: 0
"""

DESC = {
    'I': 'E-advance: look two cells right of E\'s hole', 'J': 'E ok: the new hole', 'K': 'E ok: fill the old hole, to N (n)',
    'I2': 'E exhausted: left', 'I3': 'E exhausted: past E\'s hole, to N (d)',
    'B': 'N-advance: look two cells left of N\'s hole; 0: N exhausted, E > N', 'B2': 'N ok: the new hole',
    'B3': 'N ok: fill the old hole, to E (e)',
    'Bd': 'E done: 1: N\'s hole not on cell 1, E < N; 0: E = N, a match', 'Bd2': 'N\'s cell 0, to its hole (tail)',
    'CW': 'match: left to C\'s hole, fill it', 'CI1': 'C += 1: next cell', 'CI2': 'C += 1: 0: the 7th match, HALT',
    'CI3': 'C += 1: the new hole', 'CR': 'right across C, to N',
    'T0': 'tail: fill N\'s hole', 'T1': 'tail: right across N', 'T2': 'tail: N\'s last cell', 'T3': 'tail: N\'s hole on cell N, to E (f)',
    'FE': 'finish E: fill its hole', 'FE2': 'right to the end of the block',
    'X2': 'separator', 'X3': '1: next entry; 0: a new row', 'X4': '1: first entry of a row; 0: end of the triangle, start the next row',
    'X5': 'the entry\'s cursor on cell 1',
    'G1': 'next row: stub 11', 'G2': 'left', 'G3': 'left across the 0s', 'G7': 'the source cursor on the second-to-last cell',
    'AT1': 'new block: 111', 'AT2': 'new block', 'AT3': 'left across it', 'AT4': 'separator', 'AT5': 'the last block + 1, back to the source (s)',
    'U1': 'source cursor: fill the hole', 'U2': 'left', 'U3': '1: the new hole; 0: block done',
    'U4': 'the new hole, walk to the end',
    'R1': 'end: back', 'R2': 'append 11', 'R4': 'left across the last block', 'R5': 'the second-to-last block + 1',
    'R6': 'separator', 'R7': 'the last block loses its first cell', 'R8': 'back to the source (s)',
    'Y2': 'separator', 'Y3': '1: next source block; 0: the row is done, to N (g)',
    'GN1': 'N += 1: left across N, a cell on its left', 'GN3': 'C\'s last cell erased',
    'CW2': 'left across C, fill its hole', 'CX': '1: it was the hole; 0: left of C: a new cell',
    'CY': 'C\'s cell 0', 'CZ': 'C\'s hole on cell 1', 'CQ': 'right across C, to N (r)',
}
FIND = {'e': 'right to E\'s hole, advance E', 'n': 'left to N\'s hole, advance N', 'd': 'left to N\'s hole, E done',
        'f': 'right to E\'s hole, finish E', 's': 'left to the source cursor', 'g': 'left to N\'s hole, N += 1',
        'r': 'right to N\'s hole, to row 0'}
for p, what in FIND.items():
    for s in ('P', 'Z1', 'Z2'):
        DESC[p + s] = f'finder: {what}'
for p, what in (('W', 'another cell'), ('WT', 'first cell of a block')):
    for s in '1234':
        DESC[p + s] = f'walk right to the end of the new row ({what})'

def section(q):
    if q.startswith(('G', 'WT', 'AT', 'U', 'W', 'R', 'Y', 's')):
        return 2 if not q.startswith(('GN',)) else 3
    if q.startswith(('GN', 'CW2', 'CX', 'CY', 'CZ', 'CQ', 'r', 'g')):
        return 3
    if q.startswith(('CW', 'CI', 'CR', 'Bd', 'd')):
        return 1
    return 0

SECTIONS = ['COMPARE AN ENTRY WITH N', 'E DONE: MATCH? C += 1', 'THE NEXT ROW', 'N += 1, C RESET']

def main(src, dst, lean):
    o, S, _ = tm.parse(build.build())
    o2, S2, _ = tm.parse(open(src).read())
    phi = leangen.state_map(o, S, o2, S2)
    for q in o:
        assert q.startswith('seed') or q in DESC, q
    ROLE = {q: DESC.get(q, 'seed: write the first tape') for q in o}
    cls = defaultdict(list)
    for q in o: cls[phi[q]].append(q)
    sec_of = {q: section(q) for q in o}
    pos = {r: i for i, r in enumerate(o)}
    name = {}
    for c, members in cls.items():
        work = [r for r in members if not r.startswith('seed')]
        name[c] = '__'.join(work) if work else members[0]
    name[o2[0]] = 'start_' + name[o2[0]]
    def key(c):
        prim = next((r for r in cls[c] if not r.startswith('seed')), cls[c][0])
        return (c != o2[0], sec_of[prim], pos[prim])
    out = [HEADER.format(n=len(o2), N=len(o), lean=lean)]
    cur = None
    for c in sorted(o2, key=key):
        sec = key(c)[1] if c != o2[0] else -1
        if sec != cur:
            title = 'START' if sec == -1 else SECTIONS[sec]
            out += ['', f'; ---------- {title} ' + '-' * max(0, 60 - len(title)), '']
            cur = sec
        for r in cls[c]:
            out.append(f'; {r:6} {ROLE[r]}')
        out.append(name[c])
        for b, t in enumerate(S2[c]):
            if t is None:
                out.append('    -'); continue
            users = [r for r in cls[c] if S[r][b] is not None]
            tgt = name.get(t[2], t[2])
            out.append(f'    {b} {t[0]} {t[1]} {tgt:24} ; [{", ".join(users)}]')
    text = '\n'.join(out) + '\n'
    o3, S3, _ = tm.parse(text)
    assert o3[0] == name[o2[0]] and len(o3) == len(o2)
    for c in o2:
        assert S3[name[c]] == [None if t is None else (t[0], t[1], name.get(t[2], t[2])) for t in S2[c]]
    open(dst, 'w').write(text)

if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else 'M77')
