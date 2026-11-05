"""Write a commented version of a merged machine.

Each state of the merged machine is a class of states of the design (erdosmoser.txt, generated
by build.py). The merged state is named after its non-seed roles, listed with a description,
and every transition line is tagged with the roles that use it.
Usage: python3 annotate.py merged.txt out.txt LeanName
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))  # tm.py
from collections import defaultdict
import tm, build, leangen

HEADER = """\
; ============================================================================
; A {n}-state, 2-symbol Turing machine that HALTS IFF THE ERDOS-MOSER
; CONJECTURE FAILS: iff 1^k + 2^k + ... + (m-1)^k = m^k for some k >= 2, m >= 1.
; Start on a blank tape in the first state. A transition to `halt` halts.
; Lean proof: lean/TinyCryptids/ErdosMoser/{lean}.lean, theorem
; TM.ErdosMoser.{lean}.halts_iff.
; ============================================================================
;
; HOW TO READ THIS FILE
;   The machine is the {N}-state design of build.py / erdosmoser.txt with
;   states merged. States are merged only when their defined transitions
;   agree, so each state below plays one or more ROLES of the design (its name
;   joins them). Each transition line is tagged [role] with the role(s) that
;   use it. A '-' line is never used.
;
; TAPE:  K 00 M 00 A 00 R 00 Q
;   K: k + 2 cells, the exponent cursor (hole) on cells 1 .. k + 1; it rests
;     on cell 1 (the anchor) between powers.
;   M: m + 3 cells, a marker hole on cell p (1 <= p <= m); the cells right of
;     it are the base block: base = m + 1 - p, cursor on cells p + 2 .. m + 2
;     (no hole at the start of a round: the cursor is then on p + 2).
;   A = 1 + the sum so far (cells), R the running power, Q scratch.
;
; SEARCH: the pairs (k, m) along the diagonals k + m = s, from (2, 2).
; PER PAIR:
;   powers  the marker starts on cell m (base 1) and moves one cell left
;           after each power: bases 1, 2, ..., m. Each power: R := 1, then k
;           rounds of R := R * base (copy R base - 1 times onto Q, merge),
;           counted by the exponent cursor.
;   next    marker on cell p >= 2: it moves left, R is added into A, R := 1.
;   compare marker on cell 1 (R = m^k): zig-zag A against R: equal -> HALT;
;           else clear, write A = 0 and R = 1, the marker on cell m', and
;           the next pair: (k + 1, m - 1) (the separator between K and M
;           moves right) or (2, k) after (k, 1).
; ============================================================================

blank_symbol: 0
"""

DESC = {
    'bAt': 'base step: on the base cursor (or its first cell)', 'bA2': 'base step: next cell (0: round done), cursor advanced',
    'bD1': 'round done: left to the marker', 'bD2': 'round done: base cell 0',
    'c1': 'copy: right across R', 'c2': 'copy: the separator', 'c3': 'copy: right across Q, append 1',
    'c4': 'copy: left across Q', 'c5': 'copy: the separator', 'c6': 'copy: find the R cursor',
    'a2': 'copy: R cursor next cell', 'a3': 'copy: 2 cells on (0: R copied)', 'a4': 'copy: R cursor advanced',
    'd1': 'copy done: left across R', 'd2': 'copy done: R cell 0', 'd3': 'copy done: R cursor on cell 1',
    'mR': 'merge: right across R', 'm2': 'merge: fill the separator', 'm3': 'merge: right across Q',
    'm4': 'merge: erase', 'm5': 'merge: erase',
    'eAt': 'exponent step: on the cursor', 'eA2': 'exponent step: next cell (0: the power is done)',
    'eD1': 'power done: left across K', 'eD2': 'power done: K cell 0', 'eD3': 'power done: the anchor on K cell 1',
    'N1': 'next base: on the marker', 'N2': 'next base: cell before', 'N3': 'next base: 2 cells before (0: marker on cell 1, compare)',
    'N4': 'next base: the marker moves left', 'N5': 'next base: old marker filled',
    'q0': 'add R into A: fill the R cursor', 'q1': 'add: R cell 0', 'q2': 'add: fill the separator', 'q3': 'add: fill the separator',
    'q4': 'add: right across R, append 1', 'Q1': 'add: R = 1 0 1, its hole', 'Q2': 'add: R cell 0', 'Q3': 'add: the gap',
    'Q4': 'add: the gap',
    'C1': 'compare: M cell 0', 'C2': 'compare: fill the marker',
    'cp5': 'compare: fill the R cursor', 'cp6': 'compare: erase R cell 0',
    'zH1': 'zig-zag: left to A\'s last cell, erase it', 'zA1': 'zig-zag: A\'s cell before (0: A is empty)',
    'zG1': 'zig-zag: right to R\'s first cell, erase it', 'zZ1': 'zig-zag: R\'s next cell (0: R is empty)',
    'zK1': 'zig-zag: A empty: right to R, erase', 'zK2': 'zig-zag: R\'s next cell (0: equal, HALT)',
    'cr1': 'clear: erase R', 'X1': 'clear: left to A', 'X2': 'clear: erase A', 'cr3': 'clear: left to M',
    'P1': 'pattern: M\'s last cell', 'P2': 'pattern: M cell L-2', 'P3': 'pattern: the marker on M cell L-3',
    'P4': 'pattern: M cell L-4', 'P5': 'pattern: M cell L-5 (0: m = 1)', 'P6': 'next pair: left across M',
    'S1': 'next pair (k+1, m-1): K gains a cell', 'S2': 'next pair: the separator', 'S3': 'next pair: M loses cell 0',
    'R1': '(k, 1) -> (2, k): fill the separator', 'R2': '(2, k): left across K', 'R3': '(2, k): K cell 0 / the blank',
    'G1': '(2, k): K grows on the left', 'G2': '(2, k): the anchor', 'G3': '(2, k): old anchor filled', 'G4': '(2, k): K cell 2',
    'G5': '(2, k): new separator', 'G6': '(2, k): new separator',
}
for i in range(4, 12): DESC[f'cr{i}'] = 'restore: write 00 A 00 R'
for i in range(1, 8): DESC[f'D{i}'] = 'restore: back to M'
for p, what in (('MC', 'to the R cursor, copy'), ('MM', 'to the R cursor, merge'), ('NB', 'back to the base cursor'),
                ('LE', 'left: past the R cursor'), ('LF', 'left: past the marker'), ('LG', 'left: to the exponent cursor'),
                ('MB', 'to the marker, next round'), ('MN', 'to the marker, power done'),
                ('MQ', 'to the R cursor, add R into A'), ('CP', 'to the R cursor, compare')):
    for i in (1, 2): DESC[f'{p}{i}'] = f'parser: {what}'

SECTIONS = [
    ('POWERS', lambda q: q.rstrip('0123456789') in ('bAt', 'bA', 'bD', 'MC', 'MM', 'c', 'a', 'd', 'NB', 'mR', 'm', 'LE', 'LF', 'LG',
                                                     'eAt', 'eA', 'eD', 'MB', 'MN')),
    ('NEXT BASE, ADD R INTO A', lambda q: q.rstrip('0123456789') in ('N', 'MQ', 'q', 'Q')),
    ('COMPARE, CLEAR', lambda q: q.rstrip('0123456789') in ('C', 'CP', 'cp', 'zH', 'zA', 'zG', 'zZ', 'zK', 'cr', 'X')),
    ('NEXT PAIR', lambda q: True),
]

def main(src, dst, lean):
    o, S, _ = tm.parse(build.build())
    o2, S2, _ = tm.parse(open(src).read())
    phi = leangen.state_map(o, S, o2, S2)
    ROLE = {q: DESC.get(q, 'seed: write K and M') for q in o}
    cls = defaultdict(list)
    for q in o: cls[phi[q]].append(q)
    sec_of = {q: next(i for i, (_, p) in enumerate(SECTIONS) if p(q)) for q in o}
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
            title = 'START' if sec == -1 else SECTIONS[sec][0]
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
    main(sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else 'M71')
