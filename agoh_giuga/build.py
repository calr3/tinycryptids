"""Generator for a 2-symbol Turing machine that halts iff the Agoh-Giuga conjecture is false:
iff some composite n >= 2 has n | 1^(n-1) + 2^(n-1) + ... + (n-1)^(n-1) + 1.

For n = 3, 4, 5, ... the machine computes, for i = n - 1 down to 2, the power i^(n-1) in unary
(../firoozbakht's Horner run) and adds i^(n-1) - 1 to B, a counter mod n (a cyclic hole).
After each i it checks B = 0; the first time B != 0 it sets a flag.  If n is prime every
i^(n-1) - 1 is 0 mod n (Fermat), so B stays 0 and the flag is never set; if n is composite,
a divisor i of n has i^(n-1) != 1 mod n, so some B is nonzero and the flag is set.  At the
end B = sum_{i=1}^{n-1} i^(n-1) + 1 - n, and the machine HALTS iff the flag is set and B = 0.

Numbers are in unary: a block of v + 2 cells holds v, its cells 1..v are the positions of a
cyclic hole.  Tape (blocks separated by '00'):

    N 00 J 00 I 00 x 00 K 00 S 00 R [00 Q]

  - N holds n; its hole is the exponent of the Horner run (at cell 1 at rest).
  - J (no hole, at least one cell) and I (holds i, base hole at cell 1 at rest): |J| + |I|
    is fixed during a round; i -= 1 moves the J/I separator one cell right.
  - x 00 K (no holes): the flag.  Not set: x = 1, K = 11; set: x = 11, K = 1.
  - S holds n; its hole is B (at cell 1 iff B = 0).
  - R = 101 at rest (holds 1); the Horner run makes it i^(n-1).
One i:
  - Horner run (exponent N, base I, skipped S): R := i^(n-1); ends at N (state PD1).
  - consume: R's last cell is erased and S's hole advances, until R = 101 again: B += R - 1.
  - check: is S's hole at cell 1?  If not, set the flag.
  - shift: i -= 1.  If now i = 1 the round ends: HALT if the flag is set and B = 0;
    otherwise the reset for n + 1: N and the J/I region grow by one cell, I := n, J one
    cell, flag cleared, S grows by one cell with its hole at cell 1, R moves one cell right.
The seed writes the round start of n = 3.
"""
import sys
ST = {}          # name -> [t0, t1]
ORDER = []
def S(name, t0, t1):
    assert name not in ST, name
    ST[name] = [t0, t1]; ORDER.append(name)
def T(w, d, n): return (w, d, n)

def parser_right(prefix, found):
    """Move right to the next hole. Lands at hole+1 (a 1) and performs `found` there."""
    S(prefix+'1', T(0,'R',prefix+'2'), T(1,'R',prefix+'1'))
    S(prefix+'2', T(0,'R',prefix+'1'), found)
def parser_left(prefix, found, sep=True):
    """Move left to the next hole. Lands at hole-1 (a 1), performs `found`.  sep=False: only 1s
    are crossed before the hole (no '00' handling)."""
    S(prefix+'1', T(0,'L',prefix+'2'), T(1,'L',prefix+'1'))
    S(prefix+'2', T(0,'L',prefix+'1') if sep else None, found)

def adv(p, nonwrap, wrap):
    """Advance the cyclic hole the head is on.  nonwrap = (dir, next): the new hole is
    written and the head moves dir; wrap = (dir, next): the hole was at the last position,
    it is written at cell 1 and the head moves dir."""
    S(p+'1', T(1,'R',p+'2'), None)
    S(p+'2', None, T(1,'R',p+'3'))
    S(p+'3', T(0,'L',p+'5'), T(1,'L',p+'4'))     # 0: the hole was at the last position
    S(p+'4', None, (0,)+nonwrap)
    S(p+'5', T(0,'R',p+'6'), T(1,'L',p+'5'))
    S(p+'6', None, T(1,'R',p+'7'))
    S(p+'7', None, (0,)+wrap)

def copy_loop(c, done):
    """Copy the block left of the head (cursor = its hole) onto the end of the block after the
    '00'.  Entered at c1 on the separator's first cell.  When the cursor has passed the last
    cell, the head walks back to the block's cell 0 and does `done`."""
    S(c+'c1', T(0,'R',c+'c2'), T(1,'R',c+'c1'))
    S(c+'c2', T(0,'R',c+'c3'), None)
    S(c+'c3', T(1,'L',c+'c4'), T(1,'R',c+'c3'))
    S(c+'c4', T(0,'L',c+'c5'), T(1,'L',c+'c4'))
    S(c+'c5', T(0,'L',c+'c6'), None)
    S(c+'c6', T(1,'R',c+'a2'), T(1,'L',c+'c6'))
    S(c+'a2', None, T(1,'R',c+'a3'))
    S(c+'a3', T(0,'L',c+'d1'), T(1,'L',c+'a4'))
    S(c+'a4', None, T(0,'R',c+'c1'))
    S(c+'d1', T(0,'R',c+'d2'), T(1,'L',c+'d1'))
    S(c+'d2', None, done)

def seed(n0, eoff, soff):
    # the round end of n = n0 - 1 (N holds n0 - 1 + eoff; the I/J region filled: I = 2, J = 1;
    # K = 11; S hole-less, n0 - 1 + soff + 2 cells; R = 101); back to S's last cell, then the reset
    pat = ('10' + '1' * (n0 - 1 + eoff) + '00' + '1111111' + '00' + '11' + '00'
           + '1' * (n0 + 1 + soff) + '00' + '101')
    for i, ch in enumerate(pat):
        S(f'seed{i}', T(int(ch), 'L' if i + 1 == len(pat) else 'R', f'seed{i+1}'), None)
    k = len(pat)
    S(f'seed{k}', T(0,'L',f'seed{k+1}'), None)    # R's cell 1
    S(f'seed{k+1}', None, T(1,'L',f'seed{k+2}'))
    S(f'seed{k+2}', T(0,'L',f'seed{k+3}'), None)
    S(f'seed{k+3}', T(0,'L','x1'), None)

def horner():
    """../firoozbakht's Horner run.  From R's cursor going left: R's hole, the skipped hole (S),
    the base (I), the exponent (N).  Each non-wrapping advance of the exponent hole is a round
    R := R * base (base - 1 copies of R appended after '00', then the separator filled and two
    cells erased).  The exponent hole starts at cell 1: R = base^(n - 1)."""
    parser_left('HE', T(1,'L','HF1'), sep=False)  # crosses R's cursor
    parser_left('HF', T(1,'L','HG1'))
    parser_left('HG', T(1,'L','HH1'))
    parser_left('HH', T(1,'R','ea1'))
    adv('ea', ('R','MB1'), ('R','PD1'))           # exponent
    parser_right('MB', T(1,'L','ba1'))
    adv('ba', ('R','MC1'), ('R','MM1'))           # base
    parser_right('MC', T(1,'R','MD1'))
    parser_right('MD', T(1,'R','c1'))             # R's cursor: copy
    parser_right('MM', T(1,'R','MN1'))
    parser_right('MN', T(1,'R','mR'))             # R's cursor: merge
    copy_loop('', T(1,'R','d3'))                  # copy R onto the end of Q
    S('d3', None, T(0,'L','NB1'))                 # reset R's cursor to cell 1
    parser_left('NB', T(1,'L','NC1'))
    parser_left('NC', T(1,'R','ba1'))             # back to the base
    # merge: R 00 Q -> R + Q
    S('mR', T(1,'R','m2'), T(1,'R','mR'))
    S('m2', T(1,'R','m3'), None)
    S('m3', T(0,'L','m4'), T(1,'R','m3'))
    S('m4', None, T(0,'L','m5'))
    S('m5', None, T(0,'L','HE1'))

def consume():
    """B += R - 1: erase R's last cell and advance S's hole, until R = 101."""
    parser_right('PD', T(1,'R','PE1'))           # past I's hole
    parser_right('PE', T(1,'R','PC1'))           # past S's hole
    parser_right('PC', T(1,'R','r1'))            # R's hole
    S('r1', T(0,'L','r2'), T(1,'R','r1'))         # to R's end
    S('r2', None, T(1,'L','r3'))
    S('r3', T(0,'L','PK1'), T(1,'R','r4'))        # 0: R = 101: done
    S('r4', None, T(0,'L','PN1'))                 # erase R's last cell
    parser_left('PN', T(1,'L','PO1'), sep=False)  # past R's hole
    parser_left('PO', T(1,'R','ca1'))            # S's hole
    adv('ca', ('R','PC1'), ('R','PC1'))

def check():
    """Is S's hole at cell 1 (B = 0)?  If not, set the flag.  Then i -= 1, or the round ends."""
    parser_left('PK', T(1,'L','k1'))
    S('k1', T(0,'L','Y1'), T(1,'L','f1'))         # 0: S's hole at cell 1
    # flag: J 00 K = .. 1 00 11 -> .. 11 00 1 (cells -6 and -4 of S)
    S('f1', T(0,'L','f2'), T(1,'L','f1'))
    S('f2', T(0,'L','f3'), None)
    S('f3', None, T(1,'L','f4'))
    S('f4', T(0,'L','f5'), T(0,'L','f5'))
    S('f5', T(0,'L','f6'), None)
    S('f6', T(1,'L','y1'), T(1,'L','y1'))
    # left to the K/J separator, then to the J/I separator
    S('Y1', T(0,'L','Y2'), T(1,'L','Y1'))
    S('Y2', T(0,'L','y1'), T(1,'L','Y1'))
    S('y1', T(0,'L','y2'), T(1,'L','y1'))
    S('y2', T(0,'L','t1'), None)
    # I's cell i - 1: the hole iff i = 2
    S('t1', None, T(1,'L','t2'))
    S('t2', None, T(1,'L','t3'))
    S('t3', T(1,'R','tt1'), T(1,'R','t4'))        # 0: i = 2: the round ends
    # i -= 1: I's last cell joins the I/J separator, whose last cell becomes J's cell 0
    S('t4', None, T(1,'R','t5'))
    S('t5', None, T(0,'R','t6'))
    S('t6', T(0,'R','t7'), None)
    S('t7', T(1,'L','HG1'), None)

def round_end(halt_state):
    """S's hole at cell 1 (B = 0) and the flag set (K = 1): HALT.  Otherwise the reset for
    n + 1, going left: S's hole is filled, S grows by a cell on its left with its hole at the
    new cell 1, K := 11, J := 1, the I/J region takes N's last two cells, I := the rest (n),
    N grows by three cells on its left with its hole at the new cell 1; then the Horner run."""
    # the round ends: fill I's hole and the I/J separator
    S('tt1', None, T(1,'R','tt2'))
    S('tt2', None, T(1,'R','tt3'))
    S('tt3', T(1,'R','tt4'), None)
    S('tt4', T(1,'R','PZ1'), None)
    parser_right('PZ', T(1,'L','z1'))            # S's hole
    S('z1', T(0,'L','z2'), None)
    S('z2', None, T(1,'L','z3'))
    S('z3', T(0,'L','z4'), T(1,'R','za'))         # 0: S's hole at cell 1: B = 0
    S('z4', T(0,'L','z5'), None)
    S('z5', None, T(1,'L','z6'))
    S('z6', T(0,'R',halt_state), T(1,'R','pa1'))  # 0: K = 1: the flag is set: HALT
    S('pa1', None, T(1,'R','pa2'))
    S('pa2', T(0,'R','x1'), None)
    # B != 0: fill S's hole
    S('za', None, T(1,'R','zb'))
    S('zb', T(1,'L','x1'), None)
    S('x1', T(0,'R','xR'), T(1,'L','x1'))         # to S's cell -1, then to its cell 1
    S('xR', None, T(1,'R','h1'))
    # S's cell 1 .. -10, right to left: 1, 0 (S's new cell 1), 1 (new cell 0), 0 0, K = 11, 0 0,
    # J = 1, 0 0 (the symbols read: '0', '1' or 'b' for both)
    for j, (ch, rd) in enumerate(zip('101001100100', 'b1001b0b1111')):
        nxt = f'h{j+2}' if j + 1 < 12 else 'g1'
        t = T(int(ch),'L',nxt)
        S(f'h{j+1}', t if rd in '0b' else None, t if rd in '1b' else None)
    # over the region (all 1s) to the N/I separator, whose cells become I's cells 0 and 1;
    # N's last two cells join the separator
    S('g1', T(0,'L','g2'), T(1,'L','g1'))
    S('g2', T(1,'L','g3'), None)
    S('g3', None, T(0,'L','g4'))
    S('g4', None, T(0,'L','g5'))
    # N grows by three cells on its left, its hole at the new cell 1
    S('g5', T(1,'L','g6'), T(1,'L','g5'))         # fill N's hole
    S('g6', None, T(1,'L','g7'))
    S('g7', T(1,'L','g8'), None)
    S('g8', T(0,'L','g9'), None)                  # N's new hole
    S('g9', T(1,'R','ea1'), None)

# test variants: (N - n, S - n).  'smod': B mod n - 1, halts at n = 4;
# 'shift': exponent n and B mod n + 1, halts at n = 5
VARIANTS = {None: (0, 0), 'smod': (0, -1), 'shift': (1, 1)}

def build(halt_state='halt', variant=None):
    ST.clear(); ORDER.clear()
    seed(4, *VARIANTS[variant]); horner(); consume(); check(); round_end(halt_state)
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    what = "the Agoh-Giuga conjecture is false" if variant is None else f'test variant {variant}'
    lines = [f'; Halts iff {what}.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'agoh_giuga.txt', 'w').write(out)
    print(len(ORDER), 'states')
