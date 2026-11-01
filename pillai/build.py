"""Generator for a 2-symbol Beeping Booping Turing machine for Pillai's conjecture: for each
k >= 1, a^x - b^y = k has finitely many solutions with a, b, x, y >= 2.

The machine never halts. For each (x, y, a, b) of the search it beeps a^x - b^y - 1 times and
then boops when a^x > b^y, and does neither otherwise. So a beep count between consecutive
boops repeats forever iff some k = a^x - b^y >= 1 has infinitely many solutions, iff Pillai's
conjecture is false.

Tape (blocks of 1s separated by '00'; a 'hole' is a single 0 inside a block):

    x 00 y 00 a 00 b 00 M 00 A 0 R 0 Q

* x, y (exponents): E + 2 cells (E >= 2), the exponent cursor on cells 1 .. E + 1 (on the
  last one it sits next to the separator, a run of three 0s that the parsers, counting 0s
  modulo 2, still read as a hole; they only meet it from the right). Between tuples x holds
  the anchor on cell 1, the exponent cursor of the first power. When x's power is done the
  cursor moves on to y's cell 1, and when y's is done, to a's cell 1.
* a, b (bases): beta + 2 cells (beta >= 2). The base being powered has a marker hole on cell
  1 and, during a round, a cursor on cells 3 .. beta + 1.
* So every block of the tuple has minimum length 4.
* M: a fixed 1-cell block that ends the tuple.
* A: 1 + a^x cells after the first power; empty between tuples.
* R: the running power, r cells for the value r (no hole of its own). The single 0 between A
  and R is R's hole. When A is empty, it and the separator after M make three 0s.
* Q: scratch for the copies of R, after a single 0.

Per tuple (the routines of ../fermat/, with a second exponent block):
1. Setup: the marker goes on a's cell 1 and the initial R = 1 is added into the empty A.
2. Powers R := a^x, added into A, then R := b^y.
3. Compare by a zig-zag that erases A's last cell and R's first, alternately. If R runs out
   first, A has 1 + a^x - b^y cells left: one is erased, and if more are left (a^x > b^y) the
   next is erased too and each further one is erased with a beep (the beep: `zX3` reading 1),
   a^x - b^y - 1 beeps, then the boop (`zX3` reading 0).
4. Clear and restore A (empty) and R = 1, fill the cursor left in a, put the anchor back on
   x's cell 1, and enumerate the next tuple (NEXCOM order of the block lengths minus 4).
"""
import sys
ST = {}
ORDER = []
def S(name, t0, t1):
    assert name not in ST, name
    ST[name] = [t0, t1]; ORDER.append(name)
def T(w, d, n): return (w, d, n)

BEEP, BOOP = ('zX3', 1), ('zX3', 0)

def parser_right(prefix, found):
    """Move right to the next hole. Lands at hole+1 (a 1) and performs `found` there."""
    S(prefix+'1', T(0,'R',prefix+'2'), T(1,'R',prefix+'1'))
    S(prefix+'2', T(0,'R',prefix+'1'), found)
def parser_left(prefix, found):
    """Move left to the next hole. Lands at hole-1 (a 1) and performs `found` there."""
    S(prefix+'1', T(0,'L',prefix+'2'), T(1,'L',prefix+'1'))
    S(prefix+'2', T(0,'L',prefix+'1'), found)

def seed():
    # x = 3 with a hole on cell 1, which counts the blocks still to write: each round moves it one
    # cell right and appends 00 1111 at the right end (y, a, b = 2); when it was on x's last cell,
    # M = 1 is appended instead and A and R follow via cr4. The hole stays on x's last cell; the
    # parser home finds it (X1 fills it, H5 puts the anchor on cell 1).
    for i, ch in enumerate('10111'):
        S(f'sd{i}', T(int(ch), 'R' if i < 4 else 'L', f'sd{i+1}' if i < 4 else 'PL1'), None)
    parser_left('PL', T(1,'R','S1'))             # back to the hole
    S('S1', T(0,'R','S2'), None)                 # on the hole
    S('S2', T(0,'R','T1'), T(0,'L','S3'))        # 0: the hole was on x's last cell: M (T1)
    S('S3', T(1,'R','S4'), None)                 # fill the old hole (the new one is right of it)
    S('S4', T(0,'R','R1'), None)                 # over the new hole
    S('R1', T(0,'R','R2'), T(1,'R','R1'))        # right to three 0s
    S('R2', T(0,'R','R3'), T(1,'R','R1'))
    S('R3', T(1,'R','W2'), T(1,'R','R1'))        # 0: the blank: append 1111 after 00
    S('W2', T(1,'R','W3'), None)
    S('W3', T(1,'R','W4'), None)
    S('W4', T(1,'L','PL1'), None)
    S('T1', T(0,'R','T2'), T(1,'R','T1'))        # right to three 0s
    S('T2', T(0,'R','T3'), T(1,'R','T1'))
    S('T3', T(1,'R','cr4'), T(1,'R','T1'))       # 0: the blank: M = 1 after 00, then A and R

def enumerate_tuples():
    # head on x's cell 2 (the anchor is on cell 1)
    S('en2', None, T(1,'R','en3'))
    S('en3', None, T(1,'R','en4'))
    S('en4', T(0,'R','f1'), T(1,'R','e6'))       # x > min ?
    # h = 1: x -= 1, y += 1 (separator 1 moves left)
    S('e6', T(0,'L','e7'), T(1,'R','e6'))
    S('e7', None, T(0,'R','e8'))
    S('e8', T(0,'R','e9'), None)
    S('e9', T(1,'L','HS1'), None)
    parser_left('HS', T(1,'R','su0'))           # back to the anchor -> setup
    # find the first non-minimal block B_h, h >= 2 (all-minimal never occurs)
    S('f1', T(0,'R','f2'), None)
    for i in range(2, 6):
        S(f'f{i}', None, T(1,'R',f'f{i+1}'))
    S('f6', T(0,'R','f1'), T(1,'R','k1'))
    S('k1', T(0,'R','k2'), T(1,'R','k1'))
    S('k2', T(0,'R','k3'), None)
    S('k3', None, T(1,'R','k4'))
    S('k4', T(0,'L','HL1'), T(1,'L','n2'))       # 0: B_h is the last block (b)
    S('n2', None, T(1,'L','n3'))
    S('n3', T(1,'L','n4'), None)                 # B_h -= 1, B_{h+1} += 1
    S('n4', T(0,'L','n5'), None)
    S('n5', None, T(0,'L','n6'))
    for i in range(6, 10):
        S(f'n{i}', None, T(1,'L',f'n{i+1}'))
    S('n10', T(0,'L','HS2'), T(1,'L','HU1'))     # B_h > min -> transfer (HS2: mid-separator)
    # last: x += 1 (at its free left end), then transfer b's excess to x
    parser_left('HL', T(1,'L','g1'))
    S('g1', T(1,'R','g2'), None)
    S('g2', None, T(0,'R','g3'))                 # the anchor moves with cell 1
    S('g3', T(1,'L','uh'), None)
    parser_left('HU', T(1,'R','uh'))
    S('uh', T(0,'R','u1'), None)
    # one unit from B_h to x: separators 1..h-1 move right by one
    S('u1', T(1,'R','u2'), T(1,'R','u1'))
    S('u2', T(0,'R','u3'), None)
    S('u3', None, T(0,'R','u4'))
    for i in range(4, 7):
        S(f'u{i}', None, T(1,'R',f'u{i+1}'))
    S('u7', T(1,'R','u2'), T(1,'R','u8'))        # 0: a minimal block, go on
    S('u8', T(0,'L','HS1'), T(1,'L','HU1'))

def setup():
    # on the anchor: over x and y, then the next-base step puts the marker on a's cell 1 and
    # adds R = 1 into the empty A
    S('su0', T(0,'R','su1'), None)
    S('su1', T(0,'R','su2'), T(1,'R','su1'))
    S('su2', T(0,'R','nb1'), None)

def pow_routines():
    # --- base step: advance the base cursor (one more copy of R) or finish the round. A round
    # starts with no cursor (MB lands on the base's cell 2 and enters bA2).
    S('bAt', T(1,'R','bA2'), None)
    S('bA2', T(0,'R','MM2'), T(0,'R','MC1'))     # 0: the cursor was on the last cell: merge
    parser_right('MC', T(0,'R','c1'))            # to R; punch the copy cursor on R's first cell
    parser_right('MM', T(1,'R','m1'))            # to R: merge Q into R
    # --- copy R onto the end of Q: the copy cursor walks R (it may reach R's last cell)
    S('c1', T(0,'R','c2'), T(1,'R','c1'))        # to R's end, over the single 0
    S('c2', T(1,'L','c3'), T(1,'R','c2'))        # to Q's end, append a cell
    S('c3', T(0,'L','c4'), T(1,'L','c3'))        # back over Q and the single 0
    S('c4', T(1,'R','c5'), T(1,'L','c4'))        # back to the copy cursor, fill it
    S('c5', T(0,'L','c6'), T(0,'R','c1'))        # 0: R ended, the copy is done; 1: next cursor
    S('c6', T(0,'L','NB1'), T(1,'L','c6'))       # back over R to its hole (the gap after A)
    parser_left('NB', T(1,'R','bAt'))            # back to the base cursor
    # --- merge: R 0 Q -> R+Q (fill the 0, erase Q's last cell), back to the gap after A
    S('m1', T(1,'R','m2'), T(1,'R','m1'))
    S('m2', T(0,'L','m3'), T(1,'R','m2'))
    S('m3', None, T(0,'L','m4'))
    S('m4', T(0,'L','LF1'), T(1,'L','m4'))
    parser_left('LF', T(1,'L','LG1'))            # skip the marker
    parser_left('LG', T(1,'R','eAt'))            # the exponent cursor
    # --- exponent step (the cursor may sit on the block's last cell)
    S('eAt', T(1,'R','eA2'), None)
    S('eA2', T(0,'R','eF1'), T(0,'R','MB1'))     # 0: the cursor was on the last cell
    parser_right('MB', T(1,'R','bA2'))           # to the marker: next round
    S('eF1', T(0,'R','eF2'), None)               # power done: the cursor moves on to cell 1
    S('eF2', None, T(1,'R','eF3'))               # of the next block
    S('eF3', None, T(0,'R','MN1'))
    parser_right('MN', T(1,'L','nb0'))           # to the marker
    # --- next base: move the marker to the next block, or compare at M
    S('nb0', T(1,'R','nb1'), None)
    S('nb1', T(0,'R','nb2'), T(1,'R','nb1'))
    S('nb2', T(0,'R','nb3'), None)
    S('nb3', None, T(1,'R','nb4'))
    S('nb4', T(0,'R','CP2'), T(0,'R','MQ1'))    # 0: M -> compare
    # --- add R into A: fill the gap between them, then cut R = 1 from the end of the block
    parser_right('MQ', T(1,'L','q0'))
    S('q0', T(1,'R','q1'), None)
    S('q1', T(1,'L','q2'), T(1,'R','q1'))
    S('q2', None, T(0,'L','LF1'))                # the new gap; then back to the exponent cursor

def compare_and_clear(boop):
    # head on the separator after M (CP2): to R, the zig-zag starts on the gap after A
    parser_right('CP', T(1,'L','zH1'))
    # zig-zag: erase the rightmost cell of A, then the leftmost of R, each time looking whether
    # the block is now empty. A has 1 + a^x cells and R has b^y.
    S('zH1', T(0,'L','zH1'), T(0,'L','zA1'))
    S('zA1', T(0,'R','zK1'), T(1,'R','zG1'))     # 0: A is empty (A <= R): clear the rest of R
    S('zG1', T(0,'R','zG1'), T(0,'R','zZ1'))
    S('zZ1', T(0,'L','zX1'), T(1,'L','zH1'))     # 0: R is empty: A has 1 + a^x - b^y cells
    S('zK1', T(0,'R','zK1'), T(0,'R','cr1'))
    S('zX1', T(0,'L','zX1'), T(0,'L','zX2'))     # erase one more cell of A
    S('zX2', T(0,'L','cr3'), T(0,'L','zX3'))     # 0: a^x = b^y; 1: a^x > b^y, erase it
    S('zX3', boop, T(0,'L','zX3'))               # the beep: erase the rest of A
    # clear what is left of R, then back to M
    S('cr1', T(0,'L','cr3'), T(0,'R','cr1'))
    S('cr3', T(0,'L','cr3'), T(1,'R','cr4'))
    # restore: A (empty) and R = 1, then to the cursor left in a
    pat = '00' + '0' + '1'
    for i, ch in enumerate(pat):
        last = i + 1 == len(pat)
        S(f'cr{4+i}', T(int(ch), 'L' if last else 'R', 'HE2' if last else f'cr{5+i}'), None)
    # fill the cursor left in a's cell 1 (in the seed: the anchor), then the anchor on x's cell 1
    parser_left('HE', T(1,'R','X1'))
    S('X1', T(1,'L','H1'), None)
    S('H1', T(0,'L','H2'), T(1,'L','H1'))
    S('H2', T(0,'L','H3'), T(1,'L','H1'))
    S('H3', T(0,'R','H4'), T(1,'L','H1'))
    S('H4', T(0,'R','H4'), T(1,'R','H5'))
    S('H5', None, T(0,'R','en2'))

def build(variant=None):
    """variant (tests only): 'halt' halts at the first boop."""
    ST.clear(); ORDER.clear()
    boop = None if variant == 'halt' else T(0,'L','cr3')
    seed(); enumerate_tuples(); setup(); pow_routines(); compare_and_clear(boop)
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST)
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    lines = ["; Beeping Booping TM for Pillai's conjecture: for each (x, y, a, b), a, b, x, y >= 2,",
             '; a^x - b^y - 1 beeps (zX3 reading 1) and a boop (zX3 reading 0) iff a^x > b^y.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'pillai.txt', 'w').write(out)
    print(len(ORDER), 'states')
