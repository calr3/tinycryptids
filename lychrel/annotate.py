"""Write a commented version of a merged machine.

Each state of the merged machine is a class of states of the design (lychrel.txt, generated
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
; A {n}-state, 2-symbol Turing machine that HALTS IFF REVERSE-AND-ADD FROM 196
; REACHES A PALINDROME: iff rev10(F^k(196)) = F^k(196) for some k, where
; F(x) = x + rev10(x) (196 is the smallest candidate Lychrel number).
; Start on a blank tape in the first state. A transition to `halt` halts.
; Lean proof: lean/TinyCryptids/Lychrel/{lean}.lean, theorem TM.Lychrel.{lean}.halts_iff.
; ============================================================================
;
; HOW TO READ THIS FILE
;   The machine is the {N}-state design of build.py / lychrel.txt with states
;   merged. States are merged only when their defined transitions agree, so
;   each state below plays one or more ROLES of the design (its name joins
;   them). Each transition line is tagged [role] with the role(s) that use it.
;   A '-' line is never used.
;
; TAPE (numbers in unary; separators are runs of >= 2 zeros, a hole is one 0):
;      D 00 X G T 00 A 00 Q 00 P
;   D  12 cells d0..d11 with a hole at d(p+1): a counter p mod 10.
;   X  x + 3 cells.  T: t + 3 cells with a hole (the cursor of the division),
;      or T is X itself in a round's first iteration.  A: a + 1 cells.
;   Q, P: made at the right end by their first cell (Q with 3 cells).
;
; ONE ROUND (for the current x):  T := x, A := 0;
;   while T > 0: A := 10 A + T mod 10, T := T div 10   (so A = rev10 x);
;   if A = x: HALT;  x := x + A.
;   division  p += 1 (a wrap of p appends a cell to Q) and T's hole moves one
;             cell right, until it reaches T's last cell: Q = T div 10, p =
;             T mod 10.  T is erased, unless it is X.
;   multiply  append a cell to P, p -= 1; when p wraps to 9, erase A's first
;             cell (if A has one cell: stop).  P = 10 A + d.  Then A's last
;             cell is erased: Q and P are the new T and A.  T = 0: compare.
;   compare   a hole walks X from cell x + 1 down to 1, moving one cell of A to
;             X's end per position; A down to its last cell with the hole at
;             cell 1: HALT.  Else the hole is filled (or the rest of A moved)
;             and X's hole goes to cell 1: the next round, T = X.
;   seed      D, X (x = 1) and the multiplication for T = 59, A = 1: the run
;             computes A = 195 and the first round is for x = 196.
; ============================================================================

blank_symbol: 0
"""

DESC = {
    'fA': 'p += 1: on D\'s hole, fill it', 'fC': 'p += 1: next cell', 'fD': 'p += 1: 2 cells on (0: D\'s end, wrap)',
    'fE': 'p += 1: the new hole, then to T\'s hole (n)',
    'fw1': 'p wraps: left across D', 'fw2': 'p wraps: d0', 'fw3': 'p wraps: the hole on d1, then past T\'s hole (w)',
    'e1': 'append to Q: right across T', 'e2': 'append to Q: the gap', 'e3': 'append to Q: right across A',
    'e4': 'append to Q: the separator', 'e5': 'append to Q: 0: no Q yet, make it', 'e6': 'append to Q: right across Q, append',
    'c1': 'make Q: its cell 2', 'c2': 'make Q: its cell 3, back to T\'s hole (bk)',
    'a1': 'advance T\'s hole: fill it', 'a2': 'advance T\'s hole: next cell',
    'a3': 'advance T\'s hole: 2 cells on (0: T\'s end, the division is over)', 'a4': 'advance T\'s hole: the new hole, back to D (hF)',
    'wd1': 'division over: left across T', 'wd2': 'division over: 0 left of T',
    'wd3': 'division over: 1: two 0s and D, T is X (keep it); 0: a gap, erase T',
    'wd5': 'erase T: the gap', 'wd6': 'erase T: the gap', 'er': 'erase T: erase it, then make P (rP4)',
    'bA': 'p -= 1: on D\'s hole, fill it', 'bC': 'p -= 1: the cell before', 'bD': 'p -= 1: 2 cells back (0: D\'s start, wrap)',
    'bE': 'p -= 1: the new hole, then append to P (rP1)',
    'bw1': 'p wraps to 9: right across D', 'bw2': 'p wraps: d11', 'bw3': 'p wraps: the hole on d10, then consume A (rA)',
    'rP1': 'append to P: right across D', 'rP2': 'append to P: the separator', 'rP3': 'append to P: right across X',
    'rP4': 'append to P: the gap', 'rP5': 'append to P: right across A', 'rP6': 'append to P: the separator',
    'rP7': 'append to P: right across Q', 'rP8': 'append to P: the separator', 'rP9': 'append to P: right across P, append, back to D (hB)',
    'rA1': 'consume A: right across D', 'rA2': 'consume A: the separator', 'rA3': 'consume A: right across X',
    'rA4': 'consume A: the gap', 'cA1': 'consume A: its second cell (0: A has one cell, the iteration ends)',
    'cA2': 'consume A: erase its first cell, then append to P (rP5)',
    'iE': 'iteration end: erase A\'s last cell', 'it1': 'iteration end: right to Q', 'it2': 'iteration end: Q cell 1',
    'it3': 'iteration end: Q cell 2', 'it4': 'iteration end: Q cell 3 (0: t = 0, compare)', 'it5': 'iteration end: back',
    'it6': 'iteration end: the hole on T\'s cell 1, back to D (hF)',
    'tz1': 't = 0: erase T', 'tz2': 't = 0: erase T', 'tz3': 't = 0: erase T, then compare',
    'cm0': 'compare: left to X', 'cm1': 'compare: X\'s hole on cell x + 1',
    'ka1': 'compare: right across X', 'ka2': 'compare: the gap', 'ka3': 'compare: A\'s second cell (0: A has one cell left)',
    'ka4': 'compare: erase A\'s first cell', 'kd1': 'compare: left across the gap', 'kd2': 'compare: append the cell to X',
    'kh1': 'compare: left across X', 'kh2': 'compare: after a 0 (0: no hole, the rest of A is moved)',
    'kr1': 'compare: no hole, back to X',
    'kv1': 'compare: hole one cell left (0: it was on cell 1, fill it)', 'kv2': 'compare: the new hole', 'kv3': 'compare: fill the old hole',
    'kn1': 'compare: X cell 0', 'kn2': 'compare: fill the hole on cell 1',
    'fl0': 'A has one cell: left', 'fl1': 'A has one cell: the gap', 'fl2': 'A has one cell: left across X',
    'fl3': 'A has one cell: after a 0 (0: no hole)', 'fl6': 'A has one cell: 0 here: the hole is on cell 1, A = x, HALT',
    'fl7': 'fill X\'s hole: the cell before it', 'fl4': 'fill X\'s hole', 'ix1': 'next round: left across X',
    'fl5': 'next round: the separator', 'ix2': 'next round: X cell 0', 'ix3': 'next round: the hole on X\'s cell 1, then to D (hF)',
}
for p, what in (('hF', 'left to D\'s hole, p += 1'), ('n', 'right to T\'s hole, advance it'),
                ('w', 'right past T\'s hole, append to Q'), ('bk', 'left back to T\'s hole, advance it'),
                ('hB', 'left to D\'s hole, p -= 1')):
    for s in ('P', 'Z1', 'Z2'):
        DESC[p + s] = f'parser: {what}'

def section(q):
    if q.startswith(('hF', 'fA', 'fC', 'fD', 'fE', 'fw', 'n', 'w', 'e', 'c1', 'c2', 'bk', 'a')) \
            and not q.startswith('wd'):
        return 0
    if q.startswith(('wd', 'er', 'hB', 'bA', 'bC', 'bD', 'bE', 'bw', 'rP', 'rA', 'cA', 'iE', 'it', 'tz')):
        return 1
    return 2

SECTIONS = ['DIVISION BY 10 (p += 1, T\'s hole)', 'MULTIPLICATION (p -= 1, P := 10 A + d)',
            'COMPARE, x := x + A']

def main(src, dst, lean):
    o, S, _ = tm.parse(build.build())
    o2, S2, _ = tm.parse(open(src).read())
    phi = leangen.state_map(o, S, o2, S2)
    ROLE = {q: DESC.get(q, 'seed: write the first tape') for q in o}
    for q in o:
        assert q.startswith('seed') or q in DESC, q
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
    main(sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else 'M95')
