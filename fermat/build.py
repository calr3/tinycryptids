"""Generator for a 2-symbol Turing machine that halts iff Fermat's Last
Theorem is FALSE (i.e. it searches for a counterexample).

Tape (blocks of 1s separated by '00'; a 'hole' is a single 0 inside a block):

    E 00 B2 00 B3 00 B4 00 M 00 A 0 R 0 Q

* E = B1: E + 2 cells (E >= 3), the exponent cursor on cells 1 .. E + 1 (on the last one it
  sits next to the separator, a run of three 0s, which the parsers still read as a hole).
  Between powers it rests on cell 1 (the anchor).
* B2, B3, B4 = x, y, z: value + 2 cells. The base being powered has a marker hole on cell 1
  and, during a round, a cursor on cells 3 .. value + 1.
* M: a fixed 1-cell block that ends the tuple.
* A: the accumulator, 1 + x^E + y^E cells after the second power; empty between tuples.
* R: the running power, r cells for the value r (no hole of its own). The single 0 between A
  and R is R's hole: every parser that goes to R stops there. When A is empty, it and the
  separator after M make a run of three 0s, still a hole.
* Q: scratch for the copies of R, after a single 0.
Search order: NEXCOM order of compositions of (B1..B4), every composition of every total, so
every (E >= 3, x, y, z >= 1) is checked.
Check: A = 1 + x^E + y^E (accumulated), R = z^E; halt iff A has one cell more than R.
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

def pow_routines():
    # --- base step: advance the base cursor (one more copy of R) or finish the round. A round
    # starts with no cursor (MB lands on the first base cell and enters bA2).
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
    # --- exponent step (the cursor may sit on E's last cell)
    S('eAt', T(1,'R','eA2'), None)
    S('eA2', T(0,'L','eD1'), T(0,'R','MB1'))     # 0: the cursor was on the last cell
    parser_right('MB', T(1,'R','bA2'))           # to the marker: next round
    S('eD1', T(0,'R','eD2'), T(1,'L','eD1'))     # power done: the cursor back to cell 1
    S('eD2', None, T(1,'R','eD3'))
    S('eD3', None, T(0,'R','MN1'))
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

def compare_and_clear(halt_state='halt'):
    # head on the separator after M (CP2): to R, the zig-zag starts on the gap after A
    parser_right('CP', T(1,'L','zH1'))
    # zig-zag: erase the rightmost cell of A, then the leftmost of R, each time looking whether
    # the block is now empty. A has 1 + x^E + y^E cells and R has z^E: they are equal iff R
    # runs out first with exactly one cell of A left.
    S('zH1', T(0,'L','zH1'), T(0,'L','zA1'))
    S('zA1', T(0,'R','zK1'), T(1,'R','zG1'))     # 0: A is empty (A <= R): clear the rest of R
    S('zG1', T(0,'R','zG1'), T(0,'R','zZ1'))
    S('zZ1', T(0,'L','zX1'), T(1,'L','zH1'))     # 0: R is empty
    S('zK1', T(0,'R','zK1'), T(0,'R','cr1'))
    S('zX1', T(0,'L','zX1'), T(0,'L','zX2'))     # erase one more cell of A
    S('zX2', T(0,'R',halt_state), T(0,'L','zX3'))  # 0: A is empty too: x^E + y^E = z^E -> HALT
    # clear the stack: what is left of R (cr1) or of A (zX3), then back to M
    S('cr1', T(0,'L','cr3'), T(0,'R','cr1'))
    S('zX3', T(0,'L','cr3'), T(0,'L','zX3'))
    S('cr3', T(0,'L','cr3'), T(1,'R','cr4'))
    # restore: A (empty, or A_INIT for the tests) and R = 1, then to the anchor
    pat = '00' + A_INIT + '0' + '1'
    for i, ch in enumerate(pat):
        last = i + 1 == len(pat)
        S(f'cr{4+i}', T(int(ch), 'L' if last else 'R', 'HE2' if last else f'cr{5+i}'), None)
    parser_left('HE', T(1,'R','en1'))            # entered on R's hole (HE2)

def enumerate_and_setup():
    # head at B1 cell1 (state en1 = just read cell0)
    k = EMIN + 2                                 # minimal length of B1
    S('en1', T(0,'R','en2'), None)               # on the permanent E hole
    for i in range(2, k):
        S(f'en{i}', None, T(1,'R',f'en{i+1}'))
    S(f'en{k}', T(0,'R','f1'), T(1,'R','e6'))    # B1 > min ?
    # h = 1: B1 -= 1, B2 += 1 (separator 1 moves left)
    S('e6', T(0,'L','e7'), T(1,'R','e6'))
    S('e7', None, T(0,'R','e8'))
    S('e8', T(0,'R','e9'), None)
    S('e9', T(1,'L','HS1'), None)
    parser_left('HS', T(1,'R','su0'))           # back to the E hole -> setup
    # scan for first non-minimal block B_h, h >= 2
    S('f1', T(0,'R','f2'), None)
    S('f2', None, T(1,'R','f3'))
    S('f3', None, T(1,'R','f4'))                 # all-minimal never occurs (seed starts past it)
    S('f4', None, T(1,'R','f5'))
    S('f5', T(0,'R','f1'), T(1,'R','k1'))
    S('k1', T(0,'R','k2'), T(1,'R','k1'))
    S('k2', T(0,'R','k3'), None)
    S('k3', None, T(1,'R','k4'))
    S('k4', T(0,'L','HL1'), T(1,'L','n2'))       # 0: B_h is B4 (last)
    S('n2', None, T(1,'L','n3'))
    S('n3', T(1,'L','n4'), None)                 # B_h -= 1, B_{h+1} += 1
    S('n4', T(0,'L','n5'), None)
    S('n5', None, T(0,'L','n6'))
    S('n6', None, T(1,'L','n7'))
    S('n7', None, T(1,'L','n8'))
    S('n8', None, T(1,'L','n9'))
    S('n9', T(0,'L','HS2'), T(1,'L','HU1'))      # B_h > min -> transfer (HS2: mid-separator)
    # last: B1 += 1 (at its free left end) then transfer B4's excess to B1
    parser_left('HL', T(1,'L','g1'))            # to the E hole, then grow B1 on the left
    S('g1', T(1,'R','g2'), None)
    S('g2', None, T(0,'R','g3'))                 # the hole moves with cell 1
    S('g3', T(1,'L','uh'), None)                 # back onto the moved cursor
    parser_left('HU', T(1,'R','uh'))
    S('uh', T(0,'R','u1'), None)
    # one unit from B_h to B1: separators 1..h-1 move right by one
    S('u1', T(1,'R','u2'), T(1,'R','u1'))
    S('u2', T(0,'R','u3'), None)
    S('u3', None, T(0,'R','u4'))
    S('u4', None, T(1,'R','u5'))
    S('u5', None, T(1,'R','u6'))
    S('u6', T(1,'R','u2'), T(1,'R','u7'))
    S('u7', T(0,'L','HS1'), T(1,'L','HU1'))
    # setup: the anchor as the marker of the next-base step: the marker goes on B2's cell 1,
    # R = 1 is added into the empty A (A = 1), then the first power
    S('su0', T(0,'R','nb1'), None)

def seed():
    # write E = 4 (its anchor on cell 1), B2 = B3 = B4 = 1 and M, then restore A and R via cr4
    pat = '10' + '1'*(EMIN+1) + '00111'*3 + '001'   # seed tuple (EMIN+1, 1, 1, 1), E hole at cell 1
    for i, ch in enumerate(pat):
        nxt = f'seed{i+1}' if i+1 < len(pat) else 'cr4'
        S(f'seed{i}', T(int(ch),'R',nxt), None)

EMIN, A_INIT = 3, ''
def build(halt_state='halt', emin=3, a_init=''):
    """Test variants: emin (smaller minimum exponent), a_init = '1' * d (A starts with d cells,
    so the machine halts iff x^E + y^E + d = z^E)."""
    global EMIN, A_INIT
    EMIN, A_INIT = emin, a_init
    ST.clear(); ORDER.clear()
    seed(); enumerate_and_setup(); pow_routines(); compare_and_clear(halt_state)
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    lines = ['; Halts iff Fermat\'s Last Theorem is false (searches for x^E+y^E=z^E, E>=3).',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'fermat.txt', 'w').write(out)
    print(len(ORDER), 'states')
