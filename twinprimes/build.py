"""Generator for a 2-symbol beeping Turing machine that beeps once for every twin
prime pair (p, p + 2), p >= 3, and never halts: it beeps infinitely often iff the
twin prime conjecture is true, i.e. it QUASIHALTS (beeps only finitely often) iff
the twin prime conjecture is FALSE.

The beep is one transition: state G2 reading 0 (marked BEEP below). It is taken
exactly when a candidate m has passed every trial divisor.

It tests m = 3, 4, 5, ... in turn. For m >= 3, m and m + 2 are both prime iff no d
with 2 <= d <= m - 1 divides m or m + 2; one mod walk per d tests both.

Tape (blank left of D and right of R):
  D 0 R
  - D (d cells, cells 0..d-1): the trial divisor d >= 2, all 1s except a hole
    (a single 0) at cell c, a cyclic counter c < d.
  - one 0 separates D and R.
  - R (r cells, cells 0..r-1), r = m - d >= 1: all 1s; during the mod walk a
    hole moving left counts the steps.
Holes are found by scanners that count zeros: from R, skip one 0 (the
separator) and stop at the next (D's hole); from D, likewise to R's hole. So a
hole may sit next to the separator or at a block's end.
Mod walk for d: the D hole starts on D's last cell d - 1; r times, make the R
hole one cell further left (starting at R's last cell), advance the D hole one
cell right (from cell d - 1 back to cell 0). The final hole cell is
c = (d - 1 + r) mod d = (m - 1) mod d, so
  d | m      iff c = d - 1 (D's last cell),
  d | m + 2  iff c = d - 3 (c = d - 1 for d = 2).
Check, reading D's cells d-1, d-2, d-3 from the separator:
  FAIL (c = d-1 or c = d-3): m is not a lesser twin prime; rebuild for m + 1.
  OK: d := d + 1, r := r - 1. Fill the hole; the separator stays 0 and is D's
    new last cell, i.e. the next walk's hole; R's cell 0 is erased and is the
    new separator. If R is now empty, d = m was reached and every d passed:
    BEEP. The beep's successor sees the walk end at once (r = 0) and the check
    fail (the hole on D's last cell: d = m divides m), so m + 1 follows.
Rebuild: fill the hole and the separator, add a 1 at the left end, write D = 10
(d = 2, hole on its last cell) and the separator: R = 1^(m - 1) for m + 1.
The run starts in Z2 on a blank tape: Z2 writes a 1 and the FAIL path runs once
(a pseudo-round, no beep), which builds the tape for m = 3, d = 2.
"""
import sys
ST = {}          # name -> [t0, t1]
ORDER = []
BEEP = ('G2', 0)  # the beep transition: state G2 reading 0
def S(name, t0, t1):
    assert name not in ST, name
    ST[name] = [t0, t1]; ORDER.append(name)
def T(w, d, n): return (w, d, n)

def scan_right(prefix, found):
    """Move right past the next 0 (a separator) to the 0 after it (a hole) and
    perform `found` on that hole."""
    S(prefix+'1', T(0,'R',prefix+'2'), T(1,'R',prefix+'1'))
    S(prefix+'2', found, T(1,'R',prefix+'2'))
def scan_left(prefix, found):
    """Move left past the next 0 (a separator) to the 0 after it (a hole) and
    perform `found` on that hole."""
    S(prefix+'1', T(0,'L',prefix+'2'), T(1,'L',prefix+'1'))
    S(prefix+'2', found, T(1,'L',prefix+'2'))

def walk():
    # move the R hole one cell left: B2 on the cell left of the old hole (just
    # filled), or on R's last cell to start the walk
    S('B2', T(0,'L','X1'), T(0,'L','Y1'))            # 0: the separator: R is done
    scan_left('Y', T(1,'R','A2'))                   # to the D hole: fill it
    # advance the D hole cyclically
    S('A2', T(0,'L','W1'), T(0,'R','Z1'))           # 0: the hole was on the last cell
    S('W1', T(0,'R','W2'), T(1,'L','W1'))
    S('W2', None, T(0,'R','Z1'))                    # hole on cell 0
    scan_right('Z', T(1,'L','B2'))                  # to the R hole: fill it

def check(beep_next='B2'):
    # from the separator, read D's cells d, d-1, d-2
    S('X1', T(1,'R','C1'), T(1,'L','X2'))           # 0: d | m: FAIL
    S('X2', T(1,'R','H1'), T(1,'L','X3'))           # 0: hole on cell d-1: OK
    S('X3', T(1,'R','C1'), T(1,'L','H0'))           # 0: d | m+2: FAIL
    S('H0', T(1,'R','H1'), T(1,'L','H0'))           # fill the hole (cells 1..d-3)
    # OK: d += 1, r -= 1
    S('H1', T(0,'R','G1'), T(1,'R','H1'))           # the separator stays 0: D's new hole
    S('G1', None, T(0,'R','G2'))                    # R's cell 0: the new separator
    S('G2', T(0,'L',beep_next), T(1,'R','SC'))      # 0: BEEP (R is empty: d = m)
    S('SC', T(0,'L','B2'), T(1,'R','SC'))           # to R's last cell: start the walk

def rebuild():
    S('C1', T(1,'L','C4'), T(1,'R','C1'))           # fill the separator
    S('C4', T(1,'R','C5'), T(1,'L','C4'))           # one more cell at the left end
    S('C5', None, T(0,'R','G1'))                    # D = 10: hole on its last cell

def build(variant=None, start='Z2'):
    """variant='halt': halt instead of beeping (test: halts at the first twin prime, 3).
    `start`: the start state (the run starts there on a blank tape)."""
    ST.clear(); ORDER.clear()
    walk(); check('halt' if variant == 'halt' else 'B2'); rebuild()
    ORDER.remove(start); ORDER.insert(0, start)
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {'halt'}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    lines = ['; Beeps (state G2 reading 0) once for every twin prime pair (p, p + 2), p >= 3;',
             '; quasihalts (beeps finitely often) iff the twin prime conjecture is false.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            mark = '   ; BEEP' if (n, r) == BEEP else ''
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}{mark}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'twinprimes.txt', 'w').write(out)
    print(len(ORDER), 'states')
