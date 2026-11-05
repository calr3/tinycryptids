"""Generator for a 2-symbol Turing machine that halts iff the second
Hardy-Littlewood conjecture is FALSE: iff pi(x) + pi(y) < pi(x + y) for some
x, y >= 2.

The search.  Let q_1 = 1, q_2 = 3, q_3 = 5, ... be 1 followed by the odd primes
(for x >= 2, pi(x) counts them: 1 stands in for 2), and h_i = (q_{i+1} - q_i)/2
the half gaps (h_1 = 1).  A counterexample with x + y = n exists iff one with
x + y = the largest prime <= n exists, and for a prime n = q_{G+1} it exists iff
for some i <= G - 1
    h_G + h_{G-1} + ... + h_{G+1-i}  <  h_1 + h_2 + ... + h_i
(the k-th prime counting down from n is too close to n compared with the k-th
prime counting up from 1).  The machine tests m = 5, 7, 9, ... by trial
division and, at each prime, runs E := 0; for i = 1 .. G-1:
E += h_{G+1-i}; E -= h_i, halting if E would drop below 0.

Tape (blocks of 1s separated by '00'; a gap block for h has h + 2 cells):
    [E] 0000 B' 00 A 00 C 00 D 00 R
  - B' = h_{N-1} ... h_2 h_1 (newest first) and A = h_1 h_2 ... h_{N-1}
    (oldest first), N = number of q found so far.  A's first block h_1 holds
    a hole at cell 1 (the "parked" cursor).
  - C has c + 2 cells: c = (m - q_N)/2 for the candidate m (the next gap).
  - D (d+2 cells, hole) and R (r+2 cells, hole): trial division of m = d + r
    from d = 3, the mod walk of legendre/ (as in sierpinski/).
  - E (e + 1 cells) and the 4-zero gap exist only during the check.
The check, after the prime m: the top cursor (a hole) walks C and then A
right to left (h_G, h_{G-1}, ...), the bottom cursor walks B' right to left
(h_1, h_2, ...), one cell per trip to E at the far left: a top cell adds a
cell to E, a bottom cell removes one; halt if E has only its base cell.  The
bottom cursor runs out after h_{G-1}; then E has h_G cells, gets two more
and becomes B''s new first block; the top cursor ends on A's h_1 (parked),
and C stays as A's new last block.
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

def blk(h, hole=None):
    s = ['1'] * (h + 2)
    if hole is not None: s[hole] = '0'
    return ''.join(s)

def seed_tape(gaps, m):
    """the tape at the prime m (state sh6, head on the cell after R), for the
    half gaps `gaps` = h_1 .. h_{N-1} found before m; C = the new gap."""
    assert gaps[0] == 1 and m % 2 == 1
    q = 1 + 2 * sum(gaps)
    c = (m - q) // 2
    assert c >= 1
    Bp = '00'.join(blk(h) for h in reversed(gaps))
    A = '00'.join(blk(h, 1 if i == 0 else None) for i, h in enumerate(gaps))
    return Bp + '00' + A + '00' + blk(c) + '00' + '10' + '1' * m + '00' + '11'

def seed(gaps, m):
    pat = seed_tape(gaps, m)
    for i, ch in enumerate(pat):
        S(f'seed{i}', T(int(ch),'R', f'seed{i+1}' if i+1 < len(pat) else 'sh6'), None)

def modwalk():
    # legendre/ and sierpinski/: advance the D hole cyclically (head ends right
    # of it), then the R hole
    S('ma1', T(1,'R','ma2'), None)
    S('ma2', None, T(1,'R','ma3'))
    S('ma3', T(0,'L','maw1'), T(1,'L','ma4'))     # 0: the hole was at the last cell
    S('ma4', None, T(0,'R','PR1'))
    S('maw1', T(0,'R','maw2'), T(1,'L','maw1'))
    S('maw2', None, T(1,'R','maw3'))
    S('maw3', None, T(0,'R','PR1'))
    parser_right('PR', T(1,'L','ra1'))
    S('ra1', T(1,'R','ra2'), None)
    S('ra2', None, T(1,'R','ra3'))
    S('ra3', T(0,'L','PK1'), T(1,'L','ra4'))      # 0: R exhausted (hole gone)
    S('ra4', None, T(0,'L','PM1'))
    parser_left('PM', T(1,'R','ma1'))
    # is the D hole at cell 1?
    parser_left('PK', T(1,'L','k1'))
    S('k1', T(0,'R','x1'), T(1,'R','k2'))         # 0: d | m: composite
    S('k2', None, T(1,'R','k3'))
    S('k3', T(1,'L','rs1'), None)                 # fill hole, reset it to cell 1
    S('rs1', T(0,'R','rs2'), T(1,'L','rs1'))
    S('rs2', None, T(1,'R','rs3'))
    S('rs3', None, T(0,'R','sh1'))
    # shift: d += 1, r -= 1
    S('sh1', T(1,'R','sh2'), T(1,'R','sh1'))
    S('sh2', T(0,'R','sh3'), None)
    S('sh3', None, T(0,'R','sh4'))
    S('sh4', None, T(1,'R','sh5'))
    S('sh5', None, T(1,'R','sh6'))
    S('sh6', T(0,'L','PS1'), T(1,'L','sh7'))      # 0: r = 0: m is prime
    S('sh7', None, T(0,'L','PM1'))                # R hole at cell 1, mod walk

def rebuild():
    # composite, from the cell left of D (D hole at cell 1): fill the D/R
    # separator, append 3 cells, back to the D hole
    S('x1', None, T(1,'R','x2'))
    S('x2', T(0,'R','c1'), None)
    S('c1', T(1,'R','c2'), T(1,'R','c1'))
    S('c2', T(1,'R','c3'), None)
    S('c3', T(1,'R','a1'), T(1,'R','c3'))
    S('a1', T(1,'R','a2'), None)
    S('a2', T(1,'L','RL'), None)
    # prime, from D's cell 2 after the check: move the D hole to cell 5, fill
    # the separator, append 7 cells
    S('q1', T(1,'R','q2'), None)
    S('q2', None, T(1,'R','q3'))
    S('q3', None, T(1,'R','q4'))
    S('q4', None, T(1,'R','q5'))
    S('q5', None, T(0,'R','c1p'))
    S('c1p', T(1,'R','c2p'), T(1,'R','c1p'))
    S('c2p', T(1,'R','c3p'), None)
    S('c3p', T(1,'R','e1'), T(1,'R','c3p'))
    S('e1', T(1,'R','e2'), None)
    S('e2', T(1,'R','e3'), None)
    S('e3', T(1,'R','c3'), None)
    # back to the hole, three cells further left, then write
    #   (composite, from the C/D separator) C's new cell, 00, D = 3 with its
    #   hole, 00, R's cell 0 and hole;
    #   (prime, from D's cell 2) the same, after the new C's first two cells
    S('RL', T(0,'L','RL1'), T(1,'L','RL'))
    S('RL1', None, T(1,'L','RL2'))
    S('RL2', T(0,'L','W0'), T(1,'L','W0'))
    S('W0', T(1,'R','W1'), T(1,'R','W1'))
    S('W1', T(0,'R','W2'), T(0,'R','W2'))
    S('W2', None, T(0,'R','W3'))
    S('W3', T(1,'R','W4'), None)
    S('W4', None, T(0,'R','W5'))
    S('W5', None, T(1,'R','W6'))
    S('W6', None, T(1,'R','W7'))
    S('W7', None, T(1,'R','W8'))
    S('W8', None, T(0,'R','W9'))
    S('W9', None, T(0,'R','W10'))
    S('W10', None, T(1,'R','W11'))
    S('W11', None, T(0,'L','PM1'))

def check(variant):
    # start: from after R (m prime), to the D hole, put the top hole on C's
    # last interior cell, then to the parked hole: the bottom cursor advances
    parser_left('PS', T(1,'L','t1'))
    S('t1', T(0,'L','t2'), None)
    S('t2', T(0,'L','t3'), None)
    S('t3', None, T(1,'L','t4'))
    S('t4', None, T(0,'L','PB1'))
    parser_left('PB', T(1,'R','Bf'))
    # a cursor moves left: fill its hole; if it was on cell 1 the block is done
    # and the cursor goes to the next block's last interior cell
    S('Bf', T(1,'L','Ba'), None)
    S('Ba', None, T(1,'L','Bb'))
    S('Bb', T(0,'L','Bn1'), T(1,'R','Bc'))
    S('Bc', None, T(0,'L','H1s'))                 # next bottom cell: subtract
    S('Bn1', T(0,'L','Bn2'), None)
    S('Bn2', T(1,'L','END1'), T(1,'L','Bn3'))     # 0: the 4-zero gap: B' done
    S('Bn3', None, T(0,'L','H1a'))                # next pair: the top cell adds
    S('Tf', T(1,'L','Ta'), None)
    S('Ta', None, T(1,'L','Tb'))
    S('Tb', T(0,'L','Tn1'), T(1,'R','Tc'))
    S('Tc', None, T(0,'L','H1a'))                 # next top cell: add
    S('Tn1', T(0,'L','Tn2'), None)
    S('Tn2', None, T(1,'L','Tn3'))
    S('Tn3', None, T(0,'L','H1s'))                # this pair's bottom block
    # add: left to the run of three 0s (the 4-zero gap, or the blank before
    # B' at the first add), then to E's left end; add a cell (two if E is new)
    S('H1a', T(0,'L','H2a'), T(1,'L','H1a'))
    S('H2a', T(0,'L','H3a'), T(1,'L','H1a'))
    S('H3a', T(0,'L','H4a'), T(1,'L','H1a'))
    S('H4a', T(0,'L','H5a'), None)
    if variant == 'tight':      # E starts with no slack: halt iff some sums are equal
        S('H5a', T(1,'R','AR1'), T(1,'L','Xa'))
    else:
        S('H5a', T(1,'L','H6a'), T(1,'L','Xa'))
        S('H6a', T(1,'R','AR1'), None)
    S('Xa', T(1,'R','AR1'), T(1,'L','Xa'))
    # back to the top cursor: the second hole
    parser_right('AR', T(1,'R','AQ1'))
    parser_right('AQ', T(1,'L','Tf'))
    # subtract: to E's left end, remove a cell; halt if only the base was left
    S('H1s', T(0,'L','H2s'), T(1,'L','H1s'))
    S('H2s', T(0,'L','H3s'), T(1,'L','H1s'))
    S('H3s', T(0,'L','H4s'), T(1,'L','H1s'))
    S('H4s', T(0,'L','Xs'), None)
    S('Xs', T(0,'R','Ys'), T(1,'L','Xs'))
    S('Ys', None, T(0,'R','Zs'))
    S('Zs', T(0,'R','halt'), T(1,'R','SR1'))      # 0: E < 0: counterexample, HALT
    parser_right('SR', T(1,'L','Bf'))
    # end: close the gap (E becomes B''s first block), then past the parked hole
    # to the D hole: the prime rebuild
    S('END1', T(1,'R','EP1'), None)
    parser_right('EP', T(1,'R','EQ1'))
    parser_right('EQ', T(1,'L','q1'))

def build(variant=None, gaps=(1,), m0=5):
    ST.clear(); ORDER.clear()
    seed(list(gaps), m0); modwalk(); rebuild(); check(variant)
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {'halt'}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    what = ('pi(x) + pi(y) < pi(x + y) for some x, y >= 2 (the second Hardy-Littlewood conjecture fails)'
            if variant is None and tuple(gaps) == (1,) and m0 == 5 else f'(test variant {variant} {gaps} {m0})')
    lines = [f'; Halts iff {what}.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'hardylittlewood2.txt', 'w').write(out)
    print(len(ORDER), 'states')
