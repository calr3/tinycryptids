"""Write a commented version of a merged machine.

Each state of the merged machine is a class of states of the design (gilbreath.txt, generated
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
; A {n}-state, 2-symbol Turing machine that HALTS IFF GILBREATH'S CONJECTURE
; FAILS: iff for some k >= 1 the first entry of row k of the triangle of
; absolute differences of the primes 2, 3, 5, 7, ... is not 1.
; Start on a blank tape in the first state. A transition to `halt` halts.
; Lean proof: lean/TinyCryptids/Gilbreath/{lean}.lean, theorem TM.Gilbreath.{lean}.halts_iff.
; ============================================================================
;
; HOW TO READ THIS FILE
;   The machine is the {N}-state design of build.py / gilbreath.txt with states
;   merged. States are merged only when their defined transitions agree, so
;   each state below plays one or more ROLES of the design (its name joins
;   them). Each transition line is tagged [role] with the role(s) that use it.
;   A '-' line is never used.
;
; THE IDEA
;   The last diagonal of the triangle on the primes so far is D0, D1, ..., with
;   D0 = p the last prime. A new prime m makes it m, |m - D0|, ||m - D0| - D1|, ...
;   and its last entry is the first entry of the new bottom row: it must be 1.
;   D0 is not stored: with g = m - p the stored S = D1, D2, ... becomes
;   g, |g - D1|, ||g - D1| - D2|, ...
;
; TAPE (unary; separators 00 or 000; a hole is a single 0):
;      G 00 M 00 S(n-1) 000 ... 000 S1 000 [zeros] 00 D 00 R
;   G = 1 0 1^(g+1) (hole at cell 1).  M: one cell.  S(i): S(i) + 2 cells.
;   D 00 R: trial division of m = d + r (as in ../legendre): D (d + 2 cells,
;   hole at cell c + 1), R (r + 2 cells, a hole during the mod walk).
;
; ONE CANDIDATE m:  trial division by d = 2, 3, ...;
;   composite: G += 1 (its hole moves left, a cell is added); rebuild D 00 R.
;   prime: the update, a queue: the old values are taken from the right end (B),
;   the new ones are made at the left end (Z, made as 1 0 1).  L is the newest
;   value (first G); one step Z := |L - B|: L's cursor hole advances L times,
;   each time B -= 1, or Z += 1 if B = 0; then while B > 0: B -= 1, Z += 1;
;   B is erased and L loses its hole and last cell.  Z is the next L.
;   When the next block is M: M is erased; Z must be 1 (else HALT); a new M and
;   G = 1 0 1 1 are written on the left; rebuild D 00 R.
;   seed: the tape after the primes 2, 3 (S = [1], g = 1), m = 4.
; ============================================================================

blank_symbol: 0
"""

DESC = {
    'ma1': 'mod walk: fill D\'s hole', 'ma2': 'mod walk: next cell', 'ma3': 'mod walk: 0: D\'s end, wrap',
    'ma4': 'mod walk: the new hole, to R\'s hole', 'maw1': 'wrap: left across D', 'maw2': 'wrap: D\'s cell 0',
    'maw3': 'wrap: the hole on cell 1, to R\'s hole',
    'ra1': 'advance R\'s hole: fill it', 'ra2': 'advance R\'s hole: next cell',
    'ra3': 'advance R\'s hole: 0: R exhausted, test the residue', 'ra4': 'advance R\'s hole: the new hole, to D\'s hole',
    'k1': 'residue: 0: D\'s hole on cell 1, d | m: composite', 'k2': 'residue not 0: fill the hole', 'k3': 'fill the hole',
    'rs1': 'reset D\'s hole: left across D', 'rs2': 'reset: D\'s cell 0', 'rs3': 'reset: the hole on cell 1',
    'sh1': 'shift d += 1, r -= 1: right across D', 'sh2': 'shift: fill the separator', 'sh3': 'shift: R\'s cell 0 erased',
    'sh4': 'next candidate starts here: R\'s cell 0', 'sh5': 'R\'s cell 1',
    'sh6': '0: r = 0, m is prime; 1: R has a cell more', 'sh7': 'the R hole on cell 1, mod walk',
    'c1': 'rebuild D := 2, R := m - 1: right across D', 'c2': 'rebuild: fill the separator', 'c3': 'rebuild: append to R',
    'c4': 'rebuild: back to D\'s hole', 'c5': 'rebuild: D cell 2', 'c6': 'rebuild: D cell 3',
    'c7': 'rebuild: the new separator', 'c8': 'rebuild: the new separator',
    'gi1': 'G += 1: fill the hole', 'gi2': 'G += 1: the new hole', 'gi3': 'G += 1: a new cell 0, back to D (rb)',
    'z1': 'make Z: gap', 'z2': 'make Z: gap', 'z3': 'make Z: its cell 2', 'z4': 'make Z: its hole',
    'z5': 'make Z: its cell 0, to L\'s hole (a)',
    'a1': 'advance L\'s cursor: fill the hole', 'a2': 'advance: next cell', 'a3': 'advance: 0: L\'s last cell, L exhausted',
    'a4': 'advance: the new hole, to B (w)', 'a5': 'L exhausted: keep the last cell', 'a6': 'L exhausted: the hole back, to B (v)',
    'e1': 'B: its next cell', 'e2': 'B: 1: B > 0, one cell less, back to L (A); 0: B = 0',
    'r1': 'B = 0: right', 'r2': 'B = 0: put the cell back, to Z via L (X)',
    'i1': 'Z += 1: fill the hole', 'i2': 'Z += 1: the new hole', 'i3': 'Z += 1: a new cell 0, back to L (a)',
    'u1': 'B: its next cell', 'u2': 'B: 1: B > 0, one cell less, to Z via L (X); 0: B = 0, the step is over',
    's1': 'erase B', 's2': 'left to the next block', 's3': '1: an old value: next step (E); 0: it is M, the update is over',
    's4': 'erase M, to L (Y)',
    't1': 'end of step: fill L\'s hole', 't2': 'end of step: erase L\'s last cell, to Z (n)',
    'y1': 'end of update: fill L\'s hole', 'y2': 'end of update: erase L\'s last cell, to Z (F)',
    'f1': 'check Z = 1: fill its hole', 'f2': 'check: Z cell 2', 'f3': 'check: 0: Z = 0, HALT', 'f4': 'check: 1: Z >= 2, HALT',
    'f5': 'Z = 1: erase its last cell', 'f6': 'left across Z', 'f7': 'gap', 'f8': 'write M', 'f9': 'gap', 'f10': 'gap',
    'f11': 'write G = 1 0 1 1', 'f12': 'write G', 'f13': 'G\'s hole', 'f14': 'G\'s cell 0, to D (rb)',
}
FIND = {'PR': 'right to R\'s hole', 'PM': 'left to D\'s hole', 'PK': 'left to D\'s hole (R exhausted)',
        'PC': 'left past D\'s hole (m prime)', 'rb': 'right to D\'s hole, rebuild', 'g': 'left to G\'s hole, G += 1',
        'n': 'left to the leftmost hole (G or Z), make Z', 'a': 'right to L\'s hole, advance it',
        'A': 'left to L\'s hole, advance it', 'X': 'left to L\'s hole, then on to Z',
        'Z': 'left to Z\'s hole, Z += 1', 'E': 'left to L\'s hole, end of step',
        'Y': 'left to L\'s hole, end of update', 'F': 'left to Z\'s hole, check Z'}
for p, what in FIND.items():
    for s in (('1', '2') if p.startswith('P') else ('P', 'Z1', 'Z2')):
        DESC[p + s] = f'finder: {what}'
for p, what in (('w', 'cursor advanced'), ('v', 'L exhausted')):
    for s in '1234':
        DESC[p + s] = f'walk right to B ({what})'
    DESC[p + 'z'] = f'walk: back to B\'s last cell, erase it ({what})'

def section(q):
    if q.startswith(('ma', 'PR', 'ra', 'PM', 'PK', 'k', 'rs', 'sh', 'PC', 'rb', 'c')):
        return 0
    if q.startswith(('g',)):
        return 1
    if q.startswith(('s', 'E', 't', 'Y', 'y', 'F', 'f')):
        return 3
    return 2

SECTIONS = ['TRIAL DIVISION (../legendre)', 'COMPOSITE: G += 1', 'UPDATE: ONE STEP Z := |L - B|',
            'UPDATE: END OF A STEP, END OF THE UPDATE']

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
    main(sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else 'M97')
