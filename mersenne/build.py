"""Generator for a 2-symbol beeping Turing machine that beeps once for every Mersenne
prime 2^k - 1 and never halts: it beeps infinitely often iff there are infinitely many
Mersenne primes, i.e. it QUASIHALTS (beeps only finitely often) iff the Mersenne prime
conjecture is FALSE.

The beep is one transition: state G0 reading 0 (marked BEEP below). It is taken exactly
when a candidate m has passed every trial divisor.

For odd m >= 3, m is a Mersenne prime iff no odd d with 3 <= d < m divides m or m + 1:
no odd d divides m iff m is prime (m is odd), and no odd d >= 3 divides m + 1 iff m + 1
is a power of 2 (an odd prime factor q of m + 1 has q <= (m + 1)/2 < m). The machine
tests m = 5, 7, 9, ... in turn (3 is done by the start) with d = 3, 5, 7, ...; one mod
walk per divisor tests both numbers.

Tape (blank left of D and right of R):
  D 0 R
  - D (d cells, cells 0..d-1, d odd >= 3): all 1s except a hole (a single 0) at cell
    c, a cyclic counter c < d. Before a walk the hole is on cell 0, the blank cell left
    of D's d - 1 ones.
  - one 0 separates D and R.
  - R (r cells), d + r = m - 1 (so r is odd): all 1s; during the walk a hole moving
    right counts the steps.
Holes are found by scanners that count zeros: from R, skip one 0 (the separator) and
stop at the next (D's hole); from D, likewise to R's hole. So a hole may sit next to
the separator or at a block's end.
Walk for d: the D hole starts on cell 0; r times, make the next R cell the hole
(starting at R's cell 0), advance the D hole one cell right (from cell d - 1 back to
cell 0), fill the R hole. The final hole cell is c = r mod d = (m - 1) mod d, so
  d | m      iff c = d - 1 (D's last cell),
  d | m + 1  iff c = d - 2.
Walk end: B2 reads the blank after R. E erases R's last cell (r := r - 1). V scans left
over R and fills the separator. Then X1 and X2, alternating, erase D's cells leftwards
from cell d - 1 to the hole (X1 on cells d - 1, d - 3, ..., X2 on cells d - 2, d - 4, ...)
and fill it. Each moves right after the fill; from X2, X1 refills the erased cell right
of the hole and moves on. C4 then reads the cell after these:
  FAIL (c = d-1 or c = d-2): the filled separator, a 1. m is not a Mersenne prime; C4
    scans on to the left end: the rebuild for m + 2.
  OK (c <= d - 3): an erased cell, a 0. C4 writes 1 and steps back, H1 steps on, G0
    erases that cell again and steps on, B2 reads the next erased cell and steps back, E
    writes 1 there and steps on (the cell is filled after all). H1 refills the erased
    cells going right. The first 1 it meets is the old separator, now a cell of D, and
    G0 on R's cell 0 writes the new separator. With the blank left of D as the next
    walk's hole, d := d + 2 and r := r - 2 in all. If R is empty, d = m - 2 was the last
    odd divisor below m and every one passed: BEEP.
After the beep, as after a FAIL, the tape holds one block of m - 1 ones. Rebuild: C4
scans to the left end and writes 1 1 there (C4, then H1), and G0 writes the separator
after them: D = 1 1 with its hole on the blank cell left of them (d = 3), R = m - 2
ones, the tape for m + 2.
The run starts in C4 on a blank tape: C4 and H1 write 1 1, G0 reads a blank and beeps
(m = 3: the block of m - 1 = 2 ones), and the rebuild builds the tape for m = 5.
"""
import sys
ST = {}          # name -> [t0, t1]
ORDER = []
BEEP = ('G0', 0)  # the beep transition: state G0 reading 0
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
    # B2 on the cell right of the R hole just filled (or on R's cell 0 to start the walk)
    S('B2', T(0,'L','E'), T(0,'L','Y1'))             # 0: past R's end: the walk is done
    scan_left('Y', T(1,'R','A2'))                   # to the D hole: fill it
    # advance the D hole cyclically
    S('A2', T(0,'L','W1'), T(0,'R','Z1'))           # 0: the hole was on the last cell
    S('W1', T(0,'R','W2'), T(1,'L','W1'))
    S('W2', None, T(0,'R','Z1'))                    # hole on cell 0
    scan_right('Z', T(1,'R','B2'))                  # to the R hole: fill it

def round_end(beep_next='C4'):
    S('E', T(1,'R','H1'), T(0,'L','V'))             # 1: erase R's last cell; 0: refill (OK path)
    S('V', T(1,'L','X1'), T(1,'L','V'))             # to the separator: fill it
    # erase D's cells leftwards from the separator, X1 and X2 alternating, to the hole
    S('X1', T(1,'R','C4'), T(0,'L','X2'))           # 0: the hole, an odd number of cells left
    S('X2', T(1,'R','X1'), T(0,'L','X1'))           # 0: the hole, an even number of cells left
    # C4 after the hole is filled: 1 (the filled separator): FAIL; 0 (an erased cell): OK
    S('C4', T(1,'L','H1'), T(1,'L','C4'))           # 1: to the left end (rebuild), write 1
    S('H1', T(1,'R','H1'), T(1,'R','G0'))           # refill; 1: the old separator (or a 1)
    S('G0', T(0,'L',beep_next), T(0,'R','B2'))      # 0: BEEP (R is empty); 1: new separator

def build(variant=None, start='C4'):
    """variant='halt': halt instead of beeping (test: halts at the first Mersenne prime, 3).
    `start`: the start state (the run starts there on a blank tape)."""
    ST.clear(); ORDER.clear()
    walk(); round_end('halt' if variant == 'halt' else 'C4')
    ORDER.remove(start); ORDER.insert(0, start)
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {'halt'}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    lines = ['; Beeps (state G0 reading 0) once for every Mersenne prime 2^k - 1;',
             '; quasihalts (beeps finitely often) iff the Mersenne prime conjecture is false.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            mark = '   ; BEEP' if (n, r) == BEEP else ''
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}{mark}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'mersenne.txt', 'w').write(out)
    print(len(ORDER), 'states')
