"""Generator for a 2-symbol Turing machine that halts iff the Goormaghtigh conjecture is
FALSE: some value other than 31 and 8191 is a repunit (of length >= 3) in two bases.

Search: for V = 4, 5, ...: for each base b = 2 .. V - 2, walk r = 1, b + 1, b^2 + b + 1, ...
(r := r*b + 1) until r >= V; a *hit* if r = V. V is *bad* if it has two hits. The machine
halts after the third bad V (31 and 8191 are the first two), so it needs neither constant.

Tape (blocks of 1s; a 'hole' is a single 0 inside a block):

    F 0^(1+f) Vb 00 Rg

* F: the countdown, fl cells. f = 0, 1, 2 (no hit yet for this V, one hit, at least two)
  is how many of F's last cells a hit has erased (the run before Vb has 1 + f zeros). F has
  4 - g - f cells, g = the number of bad values below V.
* Vb: V cells with the base hole K: b = the number of cells right of K (K on cells
  1 .. V - 3). During a step it also holds the pass cursor P, on cells K + 2 .. V - 1 (on the
  last cell it sits next to the separator).
* Rg: the region, V + 1 cells, the rightmost block. Between steps it is  R H D:  r ones,
  the hole H, d = V - r ones. A step r -> r*b + 1 turns H into the marker M and punches a
  new H on D's first cell, then makes b - 1 passes (P punched on K + 2, moved once per pass);
  in a pass the copy cursor C walks R and each of its r positions moves H one cell right
  (a tick). The cells between M and H are the copies Q. Filling M merges R and Q: r*b + 1
  ones before H. If H must move past the region's last cell, r*b + 1 > V (overflow); if H
  ends on the last cell, r = V (a hit).
* A hit erases F's last cell while f < 2 (f += 1). After the last base (K would reach cell 0)
  Vb grows on the left, F gets its f cells back and moves one cell left; after a bad V
  (f = 2) it gets only one back, and if F was empty the machine halts. Then K goes on cell
  V - 2 of the new Vb (b = 2) and the region grows by one cell.
The seed writes the tape of V = 3 just after its V-end has fixed F (F = 4 cells) and enters
the rest of that V-end, so the search starts at V = 4.
"""
import sys
ST = {}
ORDER = []
def S(name, t0, t1):
    assert name not in ST, name
    ST[name] = [t0, t1]; ORDER.append(name)
def T(w, d, n): return (w, d, n)

def seed():
    # written right to left: the region (4 cells), 00, Vb (4), 0, F (Z0 + 1): the tape of V = 3
    # just after its V-end has grown Vb and fixed F; then into VR1 (K, the region, H)
    pat = ('1' * (Z0 + 1) + '0' + '1111' + '00' + '1111')[::-1]
    for i, ch in enumerate(pat):
        last = i + 1 == len(pat)
        S(f'seed{i}', T(int(ch), 'R' if last else 'L', 'VR1' if last else f'seed{i+1}'), None)

def step():
    # X: on the cell after H. 1: D is not empty: the next step (H -> M, new H on D's first cell)
    S('X', T(0, 'L', 'Y0'), T(0, 'L', 'SA'))     # 0: H on the region's last cell: r = V, a hit
    S('SA', T(0, 'L', 'SB'), None)               # on M
    S('SB', T(0, 'L', 'SC'), T(1, 'L', 'SB'))    # over R
    S('SC', T(0, 'L', 'SD'), None)               # the separator
    S('SD', T(0, 'R', 'SE'), T(1, 'L', 'SD'))    # over Vb to K
    S('SE', None, T(1, 'R', 'SF'))
    S('SF', None, T(0, 'R', 'G1'))               # punch P on K + 2 (the first pass)
    # a pass: to the region's first cell, punch C there
    S('G1', T(0, 'R', 'G2'), T(1, 'R', 'G1'))
    S('G2', T(0, 'R', 'G3'), None)
    S('G3', None, T(0, 'R', 'TJ'))
    # a tick: to H (past M), move H one cell right, back to C (past M), move C
    S('TJ', T(0, 'R', 'TK'), T(1, 'R', 'TJ'))    # over R to M
    S('TK', T(1, 'R', 'TL'), T(1, 'R', 'TK'))    # over Q to H, fill it
    S('TL', T(0, 'L', 'O1'), T(0, 'L', 'TM'))    # 0: past the region's end: overflow
    S('TM', T(0, 'L', 'TN'), T(1, 'L', 'TM'))    # over Q to M
    S('TN', T(1, 'R', 'TO'), T(1, 'L', 'TN'))    # over R to C, fill it
    S('TO', T(0, 'L', 'PQ'), T(0, 'R', 'TJ'))    # 0: C was on R's last cell: the pass is done
    # pass done: back to P and move it (or the passes are done: merge)
    S('PQ', T(0, 'L', 'PR'), T(1, 'L', 'PQ'))
    S('PR', T(0, 'L', 'PS'), None)
    S('PS', T(1, 'R', 'PT'), T(1, 'L', 'PS'))    # fill P
    S('PT', T(0, 'R', 'MU'), T(0, 'R', 'G1'))    # 0: P was on Vb's last cell
    # merge: fill M, then to the cell after H
    S('MU', T(0, 'R', 'MV'), None)
    S('MV', T(1, 'R', 'MW'), T(1, 'R', 'MV'))
    S('MW', T(0, 'R', 'X'), T(1, 'R', 'MW'))

def base_end():
    # overflow (TL read the separator after the region): fill M and C, then P, then K
    S('O1', T(1, 'L', 'O2'), T(1, 'L', 'O1'))
    S('O2', T(1, 'L', 'O3'), T(1, 'L', 'O2'))
    S('O3', T(0, 'L', 'O4'), T(1, 'L', 'O3'))
    S('O4', T(0, 'L', 'O5'), None)
    S('O5', T(1, 'L', 'O6'), T(1, 'L', 'O5'))    # fill P
    S('O6', T(1, 'L', 'K2'), T(1, 'L', 'O6'))    # fill K
    # hit: fill H, then left past K to the run before Vb: update f, back to K
    S('Y0', T(1, 'L', 'A1'), None)
    S('A1', T(0, 'L', 'A2'), T(1, 'L', 'A1'))
    S('A2', T(0, 'L', 'A3'), None)
    S('A3', T(0, 'L', 'A4'), T(1, 'L', 'A3'))    # over Vb's right part, past K
    S('A4', T(0, 'L', 'A5'), T(1, 'L', 'A4'))    # over Vb's left part
    S('A5', T(0, 'L', 'A6'), T(0, 'R', 'B1'))    # 1: f = 0 -> 1 (F loses its last cell)
    S('A6', T(0, 'R', 'B1'), T(0, 'R', 'B1'))    # 1: f = 1 -> 2 (again); 0: f = 2, nothing
    S('B1', T(0, 'R', 'B1'), T(1, 'R', 'B2'))
    S('B2', T(1, 'L', 'K2'), T(1, 'R', 'B2'))    # fill K
    # next base: K moves one cell left (b += 1), unless it is on cell 1
    S('K2', None, T(1, 'L', 'K3'))
    S('K3', T(1, 'L', 'VF1'), T(1, 'R', 'K4'))   # 0: K was on cell 1: the next V (Vb grows)
    S('K4', None, T(0, 'R', 'KR1'))
    S('KR1', T(0, 'R', 'KR2'), T(1, 'R', 'KR1'))
    S('KR2', T(0, 'R', 'H1'), None)
    S('H1', None, T(1, 'R', 'H2'))
    S('H2', None, T(0, 'R', 'X'))                # R = 1, H, D = V - 1
    # next V (K3 has grown Vb into the run): F gets its f cells back and moves one cell left
    # (one cell less after a bad V), K on Vb's third cell from the right, the region grows
    S('VF1', T(0, 'L', 'VF2'), T(0, 'L', 'VF3'))  # 1: f = 0, F's last cell goes
    S('VF2', T(1, 'L', 'VFh'), T(1, 'L', 'VF3'))  # 1: f = 1; 0: f = 2, fill it (a bad V)
    S('VFh', T(0, 'R', HALT), T(1, 'R', 'VR1'))   # 0: F is empty: the z0-th bad value
    S('VF3', T(1, 'R', 'VR1'), T(1, 'L', 'VF3'))  # F grows on the left
    S('VR1', T(0, 'R', 'VR2'), T(1, 'R', 'VR1'))
    S('VR2', T(0, 'L', 'V2'), T(1, 'R', 'VR2'))
    S('V2', None, T(1, 'L', 'V3'))
    S('V3', None, T(1, 'L', 'V4'))
    S('V4', None, T(0, 'R', 'V5'))
    S('V5', T(0, 'R', 'V6'), T(1, 'R', 'V5'))
    S('V6', T(0, 'R', 'V7'), None)
    S('V7', T(1, 'L', 'V14'), T(1, 'R', 'V7'))    # the region grows
    S('V14', T(0, 'R', 'H1'), T(1, 'L', 'V14'))

Z0, HALT = 3, 'halt'
def build(z0=3, halt_state='halt'):
    """Test variant z0: halt at the z0-th bad value (z0 = 1: at 31)."""
    global Z0, HALT
    Z0, HALT = z0, halt_state
    ST.clear(); ORDER.clear()
    seed(); step(); base_end()
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    lines = ['; Halts iff the Goormaghtigh conjecture is false (a third value, after 31 and 8191,',
             '; that is a repunit of length >= 3 in two bases).',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'goormaghtigh.txt', 'w').write(out)
    print(len(ORDER), 'states')
