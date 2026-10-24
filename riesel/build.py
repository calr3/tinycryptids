"""Generator for a 2-symbol Turing machine that halts iff no odd k < 509203 is a
Riesel number: iff every odd k < 509203 has some n >= 1 with k*2^n - 1 prime.
(A Sigma_1 statement: the machine halts iff it is TRUE.)

For k = 3, 5, ..., 509201 in turn it tests Q = k*2 - 1, k*4 - 1, ... by trial
division until one is prime; then it moves on to k + 2.  After the prime for
k = 509201 it halts.  (k = 1 is not run: 1*2^2 - 1 = 3 is prime.)
The initial pseudo-round handles k = 1: its candidate is 3, a prime.

Tape layout (blocks of 1s; separators 0 or 00):
  C 0 K 0 D 00 R
  - C: a binary counter c, in five groups of four bits b3 b2 b1 b0 followed by
    a marker 1, most significant group first: the number of k still to come.
  - K: k + 4 cells while k is tested (no hole).
  - D: d + 1 cells (cells 0..d), the trial divisor d.  Its hole (a single 0)
    steps cyclically over cells 1..d; its HOME is cell d, the last cell.
  - R: r + 1 cells, r = Q - d.  During the mod walk its hole steps from cell 0
    to cell r - 1 (cell 0 makes a run of three 0s with the separator).
Trial division (d = 3, 4, ...): the mod walk advances the D hole r times
(one step per step of the R hole); then d | Q iff the D hole is home.  The
walk ends with the head right of R: back over R, the cell left of the
separator is D's home.
  home (d | Q): composite.  Fill D's hole and the separator, D := 3 (hole at
    cell 3), R := the rest, R hole at cell 0, and the loop doubles R and then
    appends two cells: Q := 2Q + 1 = k*2^(n+1) - 1.
  not home: fill the hole; the first separator cell becomes D's new last cell,
    still 0 (d := d + 1, hole home), R loses its cell 0 (r := r - 1) and gets
    its hole at its new cell 0.  If R is then a single cell, r = 0: Q is
    prime.
  prime: wipe D and R and append one cell to K; the loop moves K one cell
    right (K') and copies it (T); decrement C (halt if it was 0); fill the
    cell left of K' (k += 2); T becomes D := 3 and R, and the loop doubles R
    and appends two cells: Q = 2(k + 2) - 1.
The loop (s*): X is a block whose last cell is under the head, with a block X'
and a block T to its right, single 0s between them (both empty at first).  One
round erases the last cell of X; it reappears as the first cell of X' (X' grows
to the left) and one more cell is appended to T.  The loop stops at the first 0
it meets in X: the R hole at cell 0 or the separator between C and K; t1 tells
them apart (the cell left of it is 0 for R, C's marker 1 for K).
  X = R: fill the gap left by the loop and the X'/T separator: R has 2|R| + 1
         cells, then two more are appended (unless R was its hole only, the
         pseudo-round), the hole at cell 0.
The seed writes C and K, whose region lacks R's cell 0 (g6 makes the R hole on
a blank cell; the candidate is 3, a prime: the pseudo-round for k = 1).
"""
import sys
ST = {}          # name -> [t0, t1]
ORDER = []
def S(name, t0, t1):
    assert name not in ST, name
    ST[name] = [t0, t1]; ORDER.append(name)
def T(w, d, n): return (w, d, n)

def parser_right(prefix, found):
    """Move right to the next hole. Lands at hole+1 (a 1) and performs
    `found` (a transition tuple) on that 1."""
    S(prefix+'1', T(0,'R',prefix+'2'), T(1,'R',prefix+'1'))
    S(prefix+'2', T(0,'R',prefix+'1'), found)
def parser_left(prefix, found):
    """Move left to the next hole. Lands at hole-1 (a 1), performs `found`."""
    S(prefix+'1', T(0,'L',prefix+'2'), T(1,'L',prefix+'1'))
    S(prefix+'2', T(0,'L',prefix+'1'), found)

C0 = 254599
NF = 1           # the pseudo-round for k = 1 (0: the seed writes K for k = 3)
def counter_cells(c):
    """C as a string: groups (msb first) of 4 bits, each followed by a marker 1"""
    assert 0 <= c < 1 << 20
    return ''.join(format((c >> (4 * g)) & 15, '04b') + '1' for g in (4, 3, 2, 1, 0))

def seed():
    # C, its separator, then K for the first step except its last cell: that
    # cell plays the loop's first erased cell (s1), then s4
    k_cells = 8 - 2 * NF
    pat = counter_cells(C0 + NF) + '0' + '1' * (k_cells - 1) + '0'
    for i, ch in enumerate(pat):
        S(f'seed{i}', T(int(ch),'R', f'seed{i+1}' if i+1 < len(pat) else 's4'), None)

def modwalk():
    # advance the D hole (head ends right of it); from the last cell it wraps to cell 1
    S('ma1', T(1,'R','ma2'), None)
    S('ma2', T(0,'L','mw1'), T(0,'R','PR1'))
    S('mw1', T(0,'R','mw2'), T(1,'L','mw1'))
    S('mw2', None, T(1,'R','mw3'))
    S('mw3', None, T(0,'R','PR1'))
    # advance the R hole; past its last position the walk is over (e1)
    parser_right('PR', T(1,'L','ra1'))
    S('ra1', T(1,'R','ra2'), None)
    S('ra2', None, T(1,'R','ra3'))
    S('ra3', T(0,'L','e1'), T(1,'L','ra4'))
    S('ra4', None, T(0,'L','PM1'))
    parser_left('PM', T(1,'R','ma1'))
    # back over R and the separator: is D's last cell (home) the hole?
    S('e1', T(0,'L','e2'), T(1,'L','e1'))
    S('e2', T(0,'L','e3'), None)
    S('e3', T(1,'R','x1'), T(1,'L','f1'))       # 0: d | P: composite
    # shift: fill the hole; separator cell 1 is D's new home; R loses cell 0
    S('f1', T(1,'R','f2'), T(1,'L','f1'))
    S('f2', T(0,'R','f3'), T(1,'R','f2'))
    S('f3', T(0,'R','f4'), None)
    S('f4', None, T(0,'R','f5'))
    S('f5', None, T(0,'R','f6'))                # the R hole at R's new cell 0
    S('f6', T(0,'L','w1'), T(1,'L','PM2'))      # 0: r = 0: P is prime

def rebuild():
    # composite: fill the separator, back to D's cell 0, then D := 3 (g*)
    S('x1', T(1,'R','x2'), None)
    S('x2', T(1,'L','x3'), None)
    S('x3', T(0,'R','x4'), T(1,'L','x3'))
    S('x4', None, T(1,'R','g1'))
    # from D's cell 1: D := 3 with its hole at cell 3, separator, R hole at R's
    # cell 0, then to the end of R and the loop.  (g6 also on a blank cell: the
    # pseudo-round)
    S('g1', None, T(1,'R','g2'))
    S('g2', None, T(1,'R','g3'))
    S('g3', None, T(0,'R','g4'))
    S('g4', None, T(0,'R','g5'))
    S('g5', None, T(0,'R','g6'))
    S('g6', T(0,'R','g7') if NF else None, T(0,'R','g7'))
    S('g7', T(0,'L','s1'), T(1,'R','g7'))

def wipe():
    # prime: erase R and D (their 0s first), append a cell to K, back onto it
    S('w1', T(0,'L','w1'), T(0,'L','w2'))
    S('w2', T(1,'R','w3'), T(0,'L','w2'))
    S('w3', T(0,'L','s1'), None)

def loop():
    S('s1', T(0,'L','t1'), T(0,'R','s4'))         # 0: X used up
    S('s4', T(1,'R','s6'), None)                  # X' grows on the left
    S('s6', T(0,'R','s6c'), T(1,'R','s6'))
    S('s6c', T(1,'L','s7'), T(1,'R','s6c'))       # T grows on the right
    S('s7', T(0,'L','s7c'), T(1,'L','s7'))
    S('s7c', T(0,'L','s1'), T(1,'L','s7c'))
    S('t1', T(0,'R','a1'), T(1,'L','D0'))         # 0: X was R; 1: X was K, C's marker

def double_end():
    # X = R: fill the gap and the X'/T separator, then to the D hole.  In the
    # normal case two cells are appended to R, so Q becomes 2Q + 1.  In the
    # pseudo-round (R was its hole only) nothing is appended: Q = 5.
    S('a1', T(0,'R','a2'), None)
    S('a2', T(1,'R','a4'), None)
    S('a4', T(1,'R','a4b'), T(1,'R','a4'))      # 0: fill separator, then look at T
    S('a4b', T(0,'L','a6'), T(1,'R','a5'))       # 0: pseudo-round (no T); 1: T starts
    S('a5', T(1,'R','a5b'), T(1,'R','a5'))       # 0: append the first cell
    S('a5b', T(1,'L','a6'), None)                # 0: append the second cell, turn back
    S('a6', T(0,'L','PM1'), T(1,'L','a6'))

def counter(halt_state):
    S('Dm', T(0,'R',halt_state), T(1,'L','D0'))   # 0: c was 0: HALT
    for i in range(4):
        S(f'D{i}', T(1,'L', f'D{i+1}' if i < 3 else 'Dm'), T(0,'R','ret'))
    S('ret', T(0,'R','b2'), T(1,'R','ret'))

def newk():
    # fill the gap (k += 2), cross K'; T becomes the region from its cell 1
    S('b2', T(1,'R','b4'), None)
    S('b4', T(0,'R','b6'), T(1,'R','b4'))
    S('b6', None, T(1,'R','g1'))

def build(halt_state='halt', c0=254599, nf=1):
    global C0, NF
    C0, NF = c0, nf
    ST.clear(); ORDER.clear()
    seed(); modwalk(); rebuild(); wipe(); loop(); double_end(); counter(halt_state); newk()
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    what = ('every odd k < 509203 has a prime k*2^n-1 (no Riesel number below 509203)' if c0 == 254599
            else f'every odd k <= {2 * c0 + 3} has a prime k*2^n-1 (test variant)')
    lines = [f'; Halts iff {what}.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'riesel.txt', 'w').write(out)
    print(len(ORDER), 'states')
