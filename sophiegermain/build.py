"""Generator for a 2-symbol beeping Turing machine that beeps once for every Sophie
Germain prime p >= 3 (p and 2p + 1 both prime) and never halts: it beeps infinitely
often iff there are infinitely many Sophie Germain primes, i.e. it QUASIHALTS (beeps
only finitely often) iff there are only finitely many.

The beep is one transition: state G0 reading 0 (marked BEEP below).

For odd n >= 5, n and 2n + 1 are both prime iff no odd d with 3 <= d <= n - 2 divides
n or 2n + 1. The machine tests n = 5, 7, 9, ... (3 is done by the start) with
d = 3, 5, 7, ...; one mod walk per divisor tests both numbers.

Tape (blank left of D and right of R), as in ../mersenne:
  D 0 R
  - D (d cells, cells 0..d-1, d odd >= 3): all 1s except a hole at cell c. Before a
    walk the hole is on cell 0, the blank cell left of D's d - 1 ones.
  - one 0 separates D and R.
  - R (r cells), d + r = n - 1: all 1s; during the walk a hole moves right through it.
Walk for d: r times, make the next R cell the hole (R's cell 0 first), move the D hole
TWO cells right (cyclically), fill the R hole. The final hole cell is
c = 2r mod d = (2n - 2) mod d, so
  d | n       iff c = d - 2,
  d | 2n + 1  iff c = d - 3.
Round end (8 states, found by SAT synthesis, ../tools/synth_round.py, k = 8): B2 reads
the blank after R and steps back; E erases R's last cell (r := r - 1) and steps right onto
B2, which reads the blank again; E then reads the erased cell. V scans left to the
separator, X on to the hole and fills it. K1, K2, K3 read the cells after the hole:
  the separator on c + 1 (c = d - 1), or found later by H (c <= d - 4): OK. The separator
    is filled (a cell of D now) and G0 writes the new separator on R's cell 0: d := d + 2,
    r := r - 2, the blank left of D is the next hole. If R is empty there, every d passed:
    BEEP.
  the separator on c + 2 (d | n) or c + 3 (d | 2n + 1): FAIL; it is filled and V scans on.
After the beep or a FAIL the tape is one block of n - 1 ones and V runs to its left end.
The check then runs on the blanks there: V takes the first blank for the separator, X fills
the next one as the hole, K1 finds the "separator" after it and fills it, and G0 writes
the separator after these two cells: D = 1 1 (d = 3), R = n - 2 ones, the tape for n + 2.
The run starts in B2 on a blank tape: E and V pass, X and K1 write 1 1, and G0 beeps (n = 3).
The 20-state hand design used as the synthesis reference is build(variant='ref').
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
    S(prefix+'1', T(0,'R',prefix+'2'), T(1,'R',prefix+'1'))
    S(prefix+'2', found, T(1,'R',prefix+'2'))
def scan_left(prefix, found):
    S(prefix+'1', T(0,'L',prefix+'2'), T(1,'L',prefix+'1'))
    S(prefix+'2', found, T(1,'L',prefix+'2'))

def walk():
    # B2 on the cell right of the R hole just filled (or on R's cell 0 to start the walk)
    S('B2', T(0,'L','E'), T(0,'L','Y1'))            # 0: past R's end: the walk is done
    scan_left('Y', T(1,'R','A2'))                   # to the D hole: fill it
    # move the D hole two cells right, cyclically
    S('A2', T(0,'L','W3'), T(1,'R','A3'))           # 0: the hole was on cell d - 1
    S('A3', T(0,'L','W1'), T(0,'R','Z1'))           # 0: the hole was on cell d - 2
    S('W1', T(0,'R','A3'), T(1,'L','W1'))           # to the left end: hole on cell 0
    S('W3', T(0,'R','A2'), T(1,'L','W3'))           # to the left end: hole on cell 1
    scan_right('Z', T(1,'R','B2'))                  # to the R hole: fill it

def round_end_ref(beep_next='C4'):
    """The 20-state hand design's round end (the reference for the synthesis)."""
    S('E', None, T(0,'L','V'))                      # erase R's last cell
    S('V', T(0,'L','K1'), T(1,'L','V'))             # to the separator
    S('K1', T(1,'R','H'), T(1,'L','K2'))            # 0: hole on d - 1: OK
    S('K2', T(1,'R','F1'), T(1,'L','K3'))           # 0: d | n: FAIL
    S('K3', T(1,'R','F1'), T(1,'L','K4'))           # 0: d | 2n + 1: FAIL
    S('K4', T(1,'R','H'), T(1,'L','K4'))            # to the hole (c <= d - 4): OK
    S('H', T(1,'R','G0'), T(1,'R','H'))             # fill the separator
    S('G0', T(0,'L',beep_next), T(0,'R','B2'))      # 0: BEEP (R is empty); 1: new separator
    S('F1', T(1,'L','C4'), T(1,'R','F1'))           # FAIL: fill the separator
    S('C4', T(1,'L','H1'), T(1,'L','C4'))           # to the left end, write 1
    S('H1', T(1,'R','H1'), T(1,'R','G0'))           # write 1; then G0 writes the separator

def round_end(beep_next='V'):
    """The 8-state round end found by SAT synthesis (synth_round.py, k = 8)."""
    # B2 read the blank after R: E erases R's last cell, steps back onto B2, which reads
    # the blank again, and E (reading the erased cell) hands over to V
    S('E', T(0,'L','V'), T(0,'R','B2'))
    S('V', T(0,'L','X'), T(1,'L','V'))              # to the separator (or the left end)
    S('X', T(1,'R','K1'), T(1,'L','X'))             # to the hole: fill it
    # read the cells after the hole: the separator on c + 1: OK; on c + 2: d | n, FAIL;
    # on c + 3: d | 2n + 1, FAIL; further on: OK
    S('K1', T(1,'R','G0'), T(1,'R','K2'))
    S('K2', T(1,'R','V'), T(1,'R','K3'))            # FAIL: fill the separator, V on R's cell 0
    S('K3', T(1,'L','V'), T(1,'R','H'))             # FAIL: fill the separator, V on D's last cell
    S('H', T(1,'R','G0'), T(1,'R','H'))             # OK: to the separator, fill it
    S('G0', T(0,'L',beep_next), T(0,'R','B2'))      # 0: BEEP (R is empty); 1: new separator
    # FAIL and after the beep: V scans to the block's left end and X, K1 write 1 1 there
    # (as if the blank were the separator and the hole); G0 writes the separator after them

def build(variant=None, start=None):
    """variant='halt': halt instead of beeping (test: halts at the first beep, n = 3);
    variant='ref' (or 'ref-halt'): the 20-state hand design used as the synthesis reference."""
    ST.clear(); ORDER.clear()
    walk()
    if variant in ('ref', 'ref-halt'):
        round_end_ref('halt' if variant == 'ref-halt' else 'C4'); start = start or 'C4'
    else:
        round_end('halt' if variant == 'halt' else 'V'); start = start or 'B2'

    ORDER.remove(start); ORDER.insert(0, start)
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {'halt'}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    lines = ['; Beeps (state G0 reading 0) once for every Sophie Germain prime p >= 3;',
             '; quasihalts (beeps finitely often) iff there are finitely many Sophie Germain primes.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            mark = '   ; BEEP' if (n, r) == BEEP else ''
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}{mark}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'sophiegermain.txt', 'w').write(out)
    print(len(ORDER), 'states')
    open('sophiegermain_ref.txt', 'w').write(build('ref'))
