"""Generator for a 2-symbol Turing machine that halts iff Beal's conjecture is FALSE:
iff a^x + b^y = c^z has a solution with a, b, c >= 1, x, y, z >= 3 and gcd(a, b) = 1.

Tape (blocks of 1s separated by '00'; a 'hole' is a single 0 inside a block):

    x 00 y 00 z 00 a 00 b 00 c 00 M 00 A 00 R 00 Q

* Exponent blocks x, y, z: length E + 1 (E >= 3), cursor on cells 1 .. E. On the last
  cell, next to the separator, the hole makes a run of three 0s; the parsers (they count
  0s modulo 2) still read it as a hole when they come from the right, the only side
  they come from while the cursor can be there.
* Base blocks a, b, c: length beta + 3 (beta >= 1), cursor on cells 2 .. beta + 1 (never
  next to a separator).
* So every block of the tuple has minimum length 4. x carries the permanent anchor hole
  on cell 1 (also the exponent cursor of the first power).
* M = 1 is a fixed marker, A the accumulator (a^x + b^y), R the running power, Q scratch.

Search: NEXCOM order (Nijenhuis-Wilf) of the block lengths minus 4, as in fermat/build.py.
For each tuple:
1. Coprimality walk: holes H_a, H_b on the first cursor cells of a and b. Each tick advances
   both cyclically; when H_a wraps (every beta_a ticks) H_b's old position decides: first
   cell -> coprime, last cell -> not coprime (see carmichael/build.py). Not coprime: next
   tuple (H_a is taken away as the exponent cursor is after a power). Coprime: H_a stays
   as the base cursor.
2. Powers (fermat/build.py's routine): R := 1, then E rounds of R := R * beta, for (x, a),
   (y, b), (z, c). At the end of a power the exponent cursor moves on to cell 1 of the next
   block, the base cursor to the next block (or onto M: compare). R is added into A after
   the first two powers.
3. Compare A with R = c^z by a zig-zag: HALT iff equal. Else clear the stack, restore A,
   take the cursor left in a back to x's cell 1 and enumerate the next tuple.
"""
import sys
ST = {}
ORDER = []
def S(name, t0, t1):
    assert name not in ST, name
    ST[name] = [t0, t1]; ORDER.append(name)
def T(w, d, n): return (w, d, n)

def parser_right(prefix, found):
    """Move right to the next hole. Lands at hole+1 (a 1) and performs `found` there."""
    S(prefix+'1', T(0,'R',prefix+'2'), T(1,'R',prefix+'1'))
    S(prefix+'2', T(0,'R',prefix+'1'), found)
def parser_left(prefix, found):
    """Move left to the next hole. Lands at hole-1 (a 1) and performs `found` there."""
    S(prefix+'1', T(0,'L',prefix+'2'), T(1,'L',prefix+'1'))
    S(prefix+'2', T(0,'L',prefix+'1'), found)

def seed():
    # x = 4 with its anchor, y = z = 3, a = b = c = 1, M; then A via cr4
    pat = '10111' + '001111' * 5 + '001'
    for i, ch in enumerate(pat):
        S(f'seed{i}', T(int(ch), 'R', f'seed{i+1}' if i + 1 < len(pat) else 'cr4'), None)

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
    parser_left('HS', T(1,'R','gA0'))           # back to the anchor -> coprimality test
    # find the first non-minimal block B_h, h >= 2 (all-minimal never occurs)
    S('f1', T(0,'R','f2'), None)
    for i in range(2, 6):
        S(f'f{i}', None, T(1,'R',f'f{i+1}'))
    S('f6', T(0,'R','f1'), T(1,'R','k1'))
    S('k1', T(0,'R','k2'), T(1,'R','k1'))
    S('k2', T(0,'R','k3'), None)
    S('k3', None, T(1,'R','k4'))
    S('k4', T(0,'L','HL1'), T(1,'L','n2'))       # 0: B_h is the last block (c)
    S('n2', None, T(1,'L','n3'))
    S('n3', T(1,'L','n4'), None)                 # B_h -= 1, B_{h+1} += 1
    S('n4', T(0,'L','n5'), None)
    S('n5', None, T(0,'L','n6'))
    for i in range(6, 10):
        S(f'n{i}', None, T(1,'L',f'n{i+1}'))
    S('n10', T(0,'L','HS2'), T(1,'L','HU1'))     # B_h > min -> transfer (HS2: mid-separator)
    # last: x += 1 (at its free left end), then transfer c's excess to x
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

def coprimality():
    # from x's anchor: H_a on a's cell 2, H_b on b's
    S('gA0', T(0,'R','gA1'), None)
    S('gA1', T(0,'R','gA2'), T(1,'R','gA1'))     # x
    S('gA2', T(0,'R','gA3'), None)
    S('gA3', T(0,'R','gA4'), T(1,'R','gA3'))     # y
    S('gA4', T(0,'R','gA5'), None)
    S('gA5', T(0,'R','gA6'), T(1,'R','gA5'))     # z
    S('gA6', T(0,'R','gA7'), None)
    S('gA7', None, T(1,'R','gA8'))
    S('gA8', None, T(1,'R','gA9'))
    S('gA9', None, T(0,'R','gB1'))               # H_a
    S('gB1', T(0,'R','gB2'), T(1,'R','gB1'))
    S('gB2', T(0,'R','gB3'), None)
    S('gB3', None, T(1,'R','gB4'))
    S('gB4', None, T(1,'R','gB5'))
    S('gB5', None, T(0,'L','GK1'))               # H_b
    # a tick: advance H_a; if it wraps, check H_b, else advance H_b
    S('GK1', T(0,'L','GK2'), T(1,'L','GK1'))
    S('GK2', T(0,'L','WA'), None)
    S('WA', T(1,'R','WA2'), T(1,'L','WA'))
    S('WA2', None, T(1,'R','WA3'))
    S('WA3', T(0,'L','WW1'), T(1,'L','WA4'))     # 0: H_a was on the last cursor cell
    S('WA4', None, T(0,'R','WB1'))
    S('WB1', T(0,'R','WB2'), T(1,'R','WB1'))
    S('WB2', T(0,'R','WB3'), None)
    S('WB3', T(1,'R','WB4'), T(1,'R','WB3'))
    S('WB4', None, T(1,'R','WB5'))
    S('WB5', T(0,'L','BW1'), T(1,'L','WB6'))     # 0: H_b wraps
    S('WB6', None, T(0,'L','GK1'))
    S('BW1', T(0,'R','BW2'), T(1,'L','BW1'))
    S('BW2', None, T(1,'R','BW3'))
    S('BW3', None, T(1,'R','BW4'))
    S('BW4', None, T(0,'L','GK1'))
    # H_a wraps: back to a's cell 2, then look at H_b
    S('WW1', T(0,'R','WW2'), T(1,'L','WW1'))
    S('WW2', None, T(1,'R','WW3'))
    S('WW3', None, T(1,'R','WW4'))
    S('WW4', None, T(0,'R','TC1'))
    S('TC1', T(0,'R','TC2'), T(1,'R','TC1'))
    S('TC2', T(0,'R','TC3'), None)
    S('TC3', None, T(1,'R','TC4'))
    S('TC4', None, T(1,'R','TC5'))
    S('TC5', T(1,'R',COPRIME), T(1,'R','TC6'))   # H_b on its first cell: coprime
    S('TC6', T(1,'R','TC7'), T(1,'R','TC6'))
    S('TC7', None, T(1,'R','TC8'))
    S('TC8', T(0,'L',NOTCOPRIME), T(1,'L','TC9'))   # 0: H_b wraps: not coprime
    S('TC9', None, T(0,'L','GK1'))
    # not coprime: H_b is gone; HE fills H_a, goes home and finds the anchor (H5)

def pow_routines():
    # --- base step: advance the base cursor (one more copy of R) or finish the round
    S('bAt', T(1,'R','bA2'), None)
    S('bA2', None, T(1,'R','bA3'))
    S('bA3', T(0,'L','bD1'), T(1,'L','bA4'))     # 0: the cursor was on the last cell
    S('bA4', None, T(0,'R','MC1'))
    parser_right('MC', T(1,'R','c1'))            # to the R hole -> copy
    S('bD1', T(0,'R','bD2'), T(1,'L','bD1'))      # base cursor back to cell 2
    S('bD2', None, T(1,'R','bD3'))
    S('bD3', None, T(1,'R','bD4'))
    S('bD4', None, T(0,'R','MM1'))
    parser_right('MM', T(1,'R','mR'))            # to the R hole -> merge Q into R
    # --- copy R (cursor = R hole) onto the end of Q
    S('c1', T(0,'R','c2'), T(1,'R','c1'))
    S('c2', T(0,'R','c3'), None)
    S('c3', T(1,'L','c4'), T(1,'R','c3'))
    S('c4', T(0,'L','c5'), T(1,'L','c4'))
    S('c5', T(0,'L','c6'), None)
    S('c6', T(1,'R','a2'), T(1,'L','c6'))
    S('a2', None, T(1,'R','a3'))
    S('a3', T(0,'L','d1'), T(1,'L','a4'))
    S('a4', None, T(0,'R','c1'))
    S('d1', T(0,'R','d2'), T(1,'L','d1'))
    S('d2', None, T(1,'R','d3'))
    S('d3', None, T(0,'L','NB1'))
    parser_left('NB', T(1,'R','bAt'))            # back to the base hole
    # --- merge: R 00 Q -> R+Q
    S('mR', T(1,'R','m2'), T(1,'R','mR'))
    S('m2', T(1,'R','m3'), None)
    S('m3', T(0,'L','m4'), T(1,'R','m3'))
    S('m4', None, T(0,'L','m5'))
    S('m5', None, T(0,'L','LE1'))
    parser_left('LE', T(1,'L','LF1'))            # skip the R hole
    parser_left('LF', T(1,'L','LG1'))            # skip the base hole
    parser_left('LG', T(1,'R','eAt'))            # the exponent hole
    # --- exponent step
    S('eAt', T(1,'R','eA2'), None)
    S('eA2', T(0,'R','eF1'), T(0,'R','MB1'))     # 0: the cursor was on the last cell
    parser_right('MB', T(1,'L','bAt'))           # next round
    S('eF1', T(0,'R','eF2'), None)               # power done: the exponent cursor moves on
    S('eF2', None, T(1,'R','eF3'))
    S('eF3', None, T(0,'R','MN1'))
    parser_right('MN', T(1,'L','nb0'))
    # --- next base: move the base cursor to the next block, or compare at the marker
    S('nb0', T(1,'R','nb1'), None)
    S('nb1', T(0,'R','nb2'), T(1,'R','nb1'))
    S('nb2', T(0,'R','nb3'), None)
    S('nb3', None, T(1,'R','nb4'))
    S('nb4', T(0,'R','CP2'), T(1,'R','nb5'))    # 0: the marker -> compare
    S('nb5', None, T(0,'R','MQ1'))
    parser_right('MQ', T(1,'L','q0'))            # to the R hole: add R into A
    S('q0', T(1,'L','q1'), None)
    S('q1', None, T(1,'L','q2'))
    S('q2', T(1,'L','q3'), None)
    S('q3', T(1,'R','q4'), None)
    S('q4', T(0,'L','q5'), T(1,'R','q4'))
    S('q5', None, T(0,'L','q6'))
    S('q6', None, T(0,'L','q7'))
    S('q7', None, T(0,'L','q8'))
    S('q8', None, T(0,'L','t1'))
    # --- go to the end of the stack, push R = 1 0 1, find the base hole
    S('t1', T(0,'R','t2'), T(1,'R','t1'))
    S('t2', T(0,'R','t3'), T(1,'R','t1'))
    S('t3', T(1,'R','p1'), T(1,'R','t1'))
    S('p1', T(0,'R','p2'), None)
    S('p2', T(1,'L','p3'), None)
    S('p3', T(0,'L','NB1'), None)

def compare_and_clear(halt_state):
    # stack: M 00 A 00 R (hole at cell 1); head at M+1
    parser_right('CP', T(1,'L','cp5'))
    S('cp5', T(1,'L','cp6'), None)               # fill the R hole
    S('cp6', None, T(1,'L','zH1'))
    # zig-zag: erase the rightmost cell of A and the leftmost of R alternately
    S('zH1', T(0,'L','zH1'), T(1,'L','zA1'))
    S('zA1', T(0,'R','zA3'), T(1,'R','zA2'))
    S('zA2', None, T(0,'R','zG1'))
    S('zG1', T(0,'R','zG1'), T(1,'R','zZ1'))
    S('zZ1', T(0,'L','cz1'), T(1,'L','zZ2'))      # 0: R had one cell, A more
    S('zZ2', None, T(0,'L','zH1'))
    S('zA3', None, T(0,'R','zK1'))               # A's last cell
    S('zK1', T(0,'R','zK1'), T(0,'R','zK2'))
    S('zK2', T(0,'R',halt_state), T(0,'R','cr1'))  # equal -> HALT
    # clear the stack, restore A = 11
    S('cr1', T(0,'L','cr3'), T(0,'R','cr1'))
    S('cz1', None, T(0,'L','cz2'))
    S('cz2', T(0,'L','cz2'), T(0,'L','cz3'))
    S('cz3', T(0,'L','cr3'), T(0,'L','cz3'))
    S('cr3', T(0,'L','cr3'), T(1,'R','cr4'))
    S('cr4', T(0,'R','cr5'), None)
    S('cr5', T(0,'R','cr6'), None)
    S('cr6', T(1,'R','cr7'), None)
    S('cr7', T(1,'L','HE1'), None)
    # the exponent cursor (now on a's cell 1) back to x's cell 1 as the anchor; after a pair
    # that is not coprime, H_a is filled and the anchor is still there
    parser_left('HE', T(1,'R','X1'))
    S('X1', T(1,'L','H1'), None)
    S('H1', T(0,'L','H2'), T(1,'L','H1'))
    S('H2', T(0,'L','H3'), T(1,'L','H1'))
    S('H3', T(0,'R','H4'), T(1,'L','H1'))
    S('H4', T(0,'R','H4'), T(1,'R','H5'))
    S('H5', T(0,'R','en2'), T(0,'R','en2'))

COPRIME, NOTCOPRIME = 't1', 'HE1'
def build(halt_state='halt', variant=None):
    """variant (tests only): 'nogcd' treats every pair as coprime, 'swap' halts on a pair
    that is not coprime."""
    global COPRIME, NOTCOPRIME
    COPRIME, NOTCOPRIME = 't1', {'nogcd': 't1', 'swap': halt_state}.get(variant, 'HE1')
    ST.clear(); ORDER.clear()
    seed(); enumerate_tuples(); coprimality(); pow_routines(); compare_and_clear(halt_state)
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert variant or not unused, unused
    lines = ['; Halts iff Beal\'s conjecture is false (searches for a^x + b^y = c^z,',
             '; x, y, z >= 3, gcd(a, b) = 1).',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'beal.txt', 'w').write(out)
    print(len(ORDER), 'states')
