"""Generator for a 2-symbol Turing machine that halts iff the Erdos-Moser conjecture is FALSE:
iff 1^k + 2^k + ... + (m-1)^k = m^k for some k >= 2, m >= 1.

Tape (blocks of 1s separated by '00'; a 'hole' is a single 0 inside a block):

    K 00 M 00 A 00 R 00 Q

* K: k + 1 cells (k >= 2), the exponent cursor on cells 1 .. k (as in beal/: on cell k it sits
  next to the separator). Between powers it rests on cell 1 (the anchor).
* M: m + 4 cells (m >= 1) with a marker hole on cell p (1 <= p <= m) and the base cursor on
  cells p + 2 .. m + 2. The cells right of the marker are the base block of fermat/'s power
  routine (the marker plays the separator): the base is m + 1 - p.
* A accumulates 1 + the sum, R is the running power, Q scratch (fermat/build.py).

Search: the pairs (k, m) along the diagonals k + m = s: (2, s-2), (3, s-3), ..., (s-1, 1), then
(2, s-1). For each pair:
1. The marker starts on cell m (base 1) and moves left one cell per power: bases 1, 2, ..., m.
2. Powers (fermat/build.py's routine): R := 1, then k rounds of R := R * base. After a power
   with the marker on p >= 2, the marker and the cursor move one cell left and R is added into
   A; with the marker on cell 1 (base m), A is compared with R.
3. Compare by a zig-zag: HALT iff equal. Else clear the stack, restore A, put the marker and the
   cursor at the right end of M, and go to the next pair: K += 1, M -= 1 by moving the
   separator one cell right, or after (k, 1): K := 2 and M := k by moving it back near K's start.
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
    # K = 2 (anchor on cell 1), M = 1 without holes: the end of the pair (2, 1), at cr4
    pat = '10' + '1' * KMIN + '00' + '1111'
    for i, ch in enumerate(pat):
        S(f'seed{i}', T(int(ch), 'R', f'seed{i+1}' if i + 1 < len(pat) else 'cr4'), None)

def pow_routines():
    # --- base step: advance the base cursor (one more copy of R) or finish the round
    S('bAt', T(1,'R','bA2'), T(1,'R','bA2'))     # 1: the first step of a round (no hole yet)
    S('bA2', T(0,'L','bD1'), T(0,'R','MC1'))     # 0: the cursor was on the last cell
    parser_right('MC', T(1,'R','c1'))            # to the R hole -> copy
    S('bD1', T(0,'R','bD2'), T(1,'L','bD1'))      # back to the marker (no hole: cursor on its first cell)
    S('bD2', None, T(1,'R','MM1'))
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
    parser_left('LF', T(1,'L','LG1'))            # skip the marker
    parser_left('LG', T(1,'R','eAt'))            # the exponent hole
    # --- exponent step (beal/: the cursor may sit on K's last cell)
    S('eAt', T(1,'R','eA2'), None)
    S('eA2', T(0,'L','eD1'), T(0,'R','MB1'))     # 0: the cursor was on the last cell
    parser_right('MB', T(1,'R','bAt'))           # to the marker, then the first base cell: next round
    S('eD1', T(0,'R','eD2'), T(1,'L','eD1'))     # power done: the exponent cursor back to cell 1
    S('eD2', None, T(1,'R','eD3'))
    S('eD3', None, T(0,'R','MN1'))
    parser_right('MN', T(1,'L','N1'))            # to the marker
    # --- next base: marker on cell 1 -> compare; else marker and cursor one cell left, R into A
    S('N1', T(0,'L','N2'), None)
    S('N2', None, T(1,'L','N3'))
    S('N3', T(0,'R','C1'), T(1,'R','N4'))        # 0: the marker is on cell 1
    S('N4', None, T(0,'R','N5'))
    S('N5', T(1,'R','MQ1'), None)
    parser_right('MQ', T(1,'L','q0'))            # to the R hole: add R into A
    S('q0', T(1,'L','q1'), None)
    S('q1', None, T(1,'L','q2'))
    S('q2', T(1,'L','q3'), None)
    S('q3', T(1,'R','q4'), None)
    # the end of the merged block becomes the gap and R = 1 0 1, then to the anchor
    S('q4', T(1,'L','Q1'), T(1,'R','q4'))
    S('Q1', None, T(0,'L','Q2'))
    S('Q2', None, T(1,'L','Q3'))
    S('Q3', None, T(0,'L','Q4'))
    S('Q4', None, T(0,'L','LF1'))

def compare_and_clear(halt_state):
    # the marker is on cell 1: fill it, then to the R hole
    S('C1', None, T(1,'R','C2'))
    S('C2', T(1,'R','CP1'), None)
    parser_right('CP', T(1,'L','cp5'))
    S('cp5', T(1,'L','cp6'), None)               # fill the R hole
    S('cp6', None, T(0,'L','zH1'))               # erase R's first cell: R has m^k + 1 cells
    # zig-zag: erase the rightmost cell of A, then the leftmost of R, each time looking whether
    # the block is now empty
    S('zH1', T(0,'L','zH1'), T(0,'L','zA1'))
    S('zA1', T(0,'R','zK1'), T(1,'R','zG1'))     # 0: A is empty
    S('zG1', T(0,'R','zG1'), T(0,'R','zZ1'))
    S('zZ1', T(0,'L','X1'), T(1,'L','zH1'))      # 0: R is empty, A is not
    S('zK1', T(0,'R','zK1'), T(0,'R','zK2'))
    S('zK2', T(0,'R',halt_state), T(0,'R','cr1'))  # 0: both empty -> HALT
    # clear the stack: what is left of R (cr1) or of A (X1, X2), then back to M's last cell
    S('cr1', T(0,'L','cr3'), T(0,'R','cr1'))
    S('X1', T(0,'L','X1'), T(0,'L','X2'))
    S('X2', T(0,'L','cr3'), T(0,'L','X2'))
    S('cr3', T(0,'L','cr3'), T(1,'R','cr4'))
    # restore A and R = 1 0 1, back to M's last cell
    pat = '00' + A_INIT + '00' + '101'
    for i, ch in enumerate(pat):
        last = i + 1 == len(pat)
        S(f'cr{4+i}', T(int(ch), 'L' if last else 'R', 'D1' if last else f'cr{5+i}'), None)
    back = '0100' + '1' * len(A_INIT) + '00'               # read leftwards from R's hole
    for i, ch in enumerate(back):
        t = T(int(ch), 'L', f'D{i+2}' if i + 1 < len(back) else 'P1')
        S(f'D{i+1}', t if ch == '0' else None, t if ch == '1' else None)
    S('P1', None, T(1,'L','P2'))
    # marker on cell m (= M's 3rd cell from the right)
    S('P2', None, T(1,'L','P3'))
    S('P3', None, T(0,'L','P4'))
    S('P4', None, T(1,'L','P5'))
    S('P5', T(1,'L','R1'), T(1,'L','P6'))        # 0: m = 1 (the marker is on cell 1)
    S('P6', T(0,'L','S1'), T(1,'L','P6'))
    # m >= 2: (k + 1, m - 1), the separator moves one cell right
    S('S1', T(1,'R','S2'), None)
    S('S2', T(0,'R','S3'), None)
    S('S3', None, T(0,'L','LG2'))               # to the anchor: the first power
    # m = 1: (2, k): fill the separator, K grows by one cell on the left (the anchor moves
    # with cell 1), a new separator after K's cell KMIN
    S('R1', T(1,'L','R2'), None)
    S('R2', T(0,'L','R3'), T(1,'L','R2'))
    S('R3', T(0,'R','G1'), T(1,'L','R2'))
    S('G1', T(1,'R','G2'), None)
    S('G2', None, T(0,'R','G3'))
    # cells 1 .. KMIN of the new K are 1s (cell 1 was the old anchor), then the separator
    cells = ['1'] * KMIN + ['0', '0']
    for i, ch in enumerate(cells):
        last = i + 1 == len(cells)
        t = T(int(ch), 'L' if last else 'R', 'LG2' if last else f'G{i+4}')
        S(f'G{i+3}', t if i == 0 else None, None if i == 0 else t)

KMIN, A_INIT = 2, '1'
def build(halt_state='halt', kmin=2, a_init='1'):
    """Test variants: kmin = 1 (halts on 1 + 2 = 3), a_init = '1' * (1 + d) (halts iff
    sum + d = m^k)."""
    global KMIN, A_INIT
    KMIN, A_INIT = kmin, a_init
    ST.clear(); ORDER.clear()
    seed(); pow_routines(); compare_and_clear(halt_state)
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    lines = ['; Halts iff the Erdos-Moser conjecture is false (searches for',
             '; 1^k + ... + (m-1)^k = m^k, k >= 2).',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'erdosmoser.txt', 'w').write(out)
    print(len(ORDER), 'states')
