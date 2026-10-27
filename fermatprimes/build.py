"""Generator for a 2-symbol Turing machine that halts iff some Fermat number
F_n = 2^(2^n) + 1 with n >= 5 is prime, i.e. iff F_4 = 65537 is not the last Fermat prime.

A prime of the form 2^k + 1 has k a power of 2, so the Fermat primes are exactly the primes
m with m - 1 a power of 2. For odd m >= 5 these are the m for which no odd d with
3 <= d <= m - 2 divides m or m - 1: no odd divisor of m means m is prime (m is odd), and no
odd divisor >= 3 of m - 1 means m - 1 is a power of 2 (an odd prime factor q of m - 1 has
q <= (m - 1)/2 <= m - 2). The machine tests m = 3, 5, 7, ... in turn with d = 3, 5, 7, ...,
one mod walk per divisor for both numbers. Such an m is a PASS. The passes up to 65537 are
3, 5, 17, 257, 65537; a counter of 6 cells far right loses one cell at each pass, and the
pass that erases its last cell halts.

Tape (blank left of D; the counter K far right):
  D 0 R ... K
  - D (d cells, cells 0..d-1, d odd >= 3): all 1s except a hole (a single 0) at cell c, a
    counter mod d. Before a walk the hole is on cell 0, the blank cell left of D's d - 1 ones.
  - one 0 separates D and R.
  - R (r cells), d + r = m - 1 (so r is odd): all 1s; during the walk a hole moves right.
  - K: j ones, some blank cells right of R (the gap grows: R shrinks at its right end).
Walk for d: the D hole starts on cell 0; r times, make the next R cell
the hole, advance the D hole one cell right (from cell d - 1 back to cell 0), fill the R
hole. The final hole cell is c = r mod d = (m - 1) mod d, so
  d | m      iff c = d - 1 (D's last cell),
  d | m - 1  iff c = 0     (D's first cell).
Walk end: B2 reads the blank after R. E erases R's last cell (r := r - 1). V scans left over
R and fills the separator. X1 reads D's cell d - 1:
  0: d | m: FAIL. X1 fills it and C4, on the filled separator, runs to the left end.
  1: X erases D's cells leftwards to the hole and steps past it; Q reads that cell:
    0 (the blank left of D): the hole was cell 0, d | m - 1: FAIL. HF refills the hole and
      the erased cells and turns back on the separator: C4 runs to the left end.
    1: d passed. H1 refills the hole and the erased cells; the first 1 it meets is the old
      separator, now a cell of D, and G0 on R's cell 0 writes the new separator. With the
      blank left of D as the next walk's hole, d := d + 2 and r := r - 2 in all.
      If R is empty, d = m - 2 was the last odd divisor below m - 1 and every one passed:
      PASS. P1 runs right to K and erases its first cell; P2 reads the next: 1: P3 runs back
      to the block; 0: K is used up: HALT.
After a FAIL or a pass, the tape holds one block of m - 1 ones. Rebuild: C4 scans to the
left end and writes a 1, H1 writes another, and G0 writes the separator after them:
D = 1 1 with its hole on the blank (d = 3), R = m - 2 ones, the tape for m + 2.
Start: S1 .. S6 write K (6 ones) leftwards, S7 leaves a blank, and C4 and H1 write 1 1 left of
it; G0 reads the blank: the pass for m = 3 (the block of m - 1 = 2 ones), and the rebuild
builds the tape for m = 5 with 5 cells of K left.
"""
import sys
ST = {}          # name -> [t0, t1]
ORDER = []
KCELLS = 6       # the counter: the pass that erases its last cell halts
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
    S('B2', T(0,'L','E'), T(0,'L','Y1'))             # 0: past R's end: the walk is done
    scan_left('Y', T(1,'R','A2'))                   # to the D hole: fill it
    S('A2', T(0,'L','W1'), T(0,'R','Z1'))           # 0: the hole was on the last cell
    S('W1', T(0,'R','W2'), T(1,'L','W1'))
    S('W2', None, T(0,'R','Z1'))                    # hole on cell 0
    scan_right('Z', T(1,'R','B2'))                  # to the R hole: fill it

def round_end():
    S('E', None, T(0,'L','V'))                      # erase R's last cell
    S('V', T(1,'L','X1'), T(1,'L','V'))             # to the separator: fill it
    S('X1', T(1,'R','C4'), T(0,'L','X'))            # cell d - 1; 0: d | m: FAIL
    S('X', T(0,'L','Q'), T(0,'L','X'))              # erase to the hole, step past it
    S('Q', T(0,'R','HF'), T(1,'R','H1'))            # 0: the hole was cell 0: d | m - 1: FAIL
    S('HF', T(1,'R','HF'), T(1,'L','C4'))           # FAIL: refill to the separator, rebuild
    S('H1', T(1,'R','H1'), T(1,'R','G0'))           # refill; 1: the old separator
    S('G0', T(0,'R','P1'), T(0,'R','B2'))           # 0: PASS (R is empty); 1: new separator
    S('P1', T(0,'R','P1'), T(0,'R','P2'))           # to the counter, erase its first cell
    S('P2', T(0,'L','halt'), T(1,'L','P3'))         # 0: that was its last cell: HALT
    S('P3', T(0,'L','P3'), T(1,'L','C4'))           # back to the block
    S('C4', T(1,'L','H1'), T(1,'L','C4'))           # rebuild: to the left end, write 1

def seed(k):
    for i in range(1, k + 1):
        S(f'S{i}', T(1,'L', f'S{i+1}'), None)        # the counter, leftwards
    S(f'S{k+1}', T(0,'L','C4'), None)               # a blank, then 1 1 (C4, H1): m = 3

def build(k=KCELLS):
    """k: the counter's cells; the run halts at the k-th pass (k = 6: after 3, 5, 17, 257,
    65537; test variants k = 2, 3, 4 halt at m = 5, 17, 257)."""
    ST.clear(); ORDER.clear()
    seed(k); walk(); round_end()
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {'halt'}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    lines = ['; Halts iff some Fermat number 2^(2^n) + 1 with n >= 5 is prime.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'fermatprimes.txt', 'w').write(out)
    print(len(ORDER), 'states')
