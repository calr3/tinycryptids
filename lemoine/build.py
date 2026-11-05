"""Generator for a 2-symbol Turing machine that halts iff Lemoine's conjecture is false:
iff some odd n >= 7 is not p + 2q with p, q prime.

For n = 7, 9, 11, ... and q = 2, 3, ... (p = n - 2q, while p >= 3) the machine tests p and
then q for primality, each by ../legendre's trial division (mod walk and shift) on a pair
  D 00 R   (D: d + 2 cells, the trial divisor d >= 2, with a hole at cell c + 1;
            R: r + 2 cells; m = d + r is the number tested).
A pair is *normalized* when d = 2: D = 1011.

Tape:
  1 0 [Dp 00 Rp] 0^G [Dq 00 Rq] 0 1
  - the left sentinel 1 0 and the right sentinel 0 1 tell the two pairs apart;
  - the P pair holds p (normalized when it is tested), the Q pair holds q;
  - the gap G = 2q at a test (even, so parsers cross it): each q += 1 erases two cells at the end of
    Rp, and when n is done the gap is filled into Rp: then p -= 2 gives
    p' = p + 2q - 2 = (n + 2) - 4.
Loop:
  TP (test p): composite -> NQ; prime -> TQ.
  TQ (normalize Q, test q): composite -> NQ; prime -> NN (n has a representation).
  NQ: q += 1 (a cell after Rq; the right sentinel moves), p -= 2 (two cells off Rp),
      normalize P; TP.  If p = 1 now, R has one cell and the test start HALTS.
  NN: erase Q and the right sentinel, fill the gap into Rp, write a fresh gap 00,
      Q = 1011 00 1 and the sentinel (the seed's tail), then as NQ: q += 1 (q = 2),
      p -= 2, normalize P, TP.
The seed writes 1 0 [1011 00 11111] 00 [1011 00 1] 0 1 and does q += 1: p = 5 before the
p -= 2, so n = 7.  Variant q0: the Q pair starts at q0 (n = p + 2q with q >= q0; first
n = 3 + 2 q0).
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
def parser_left(prefix, found):
    """Move left to the next hole. Lands at hole-1 (a 1), performs `found`."""
    S(prefix+'1', T(0,'L',prefix+'2'), T(1,'L',prefix+'1'))
    S(prefix+'2', T(0,'L',prefix+'1'), found)

def seed(q0):
    # sentinel, P (p = 5 before the p -= 2), gap, Q (q = q0 - 1: R one cell short), 0 1; then
    # head right of the sentinel in w, which does q += 1 as after a composite
    pat = '10' + '1011' + '00' + '11111' + '00' + '1011' + '00' + '1' * (q0 - 1) + '01'
    global SEED_GAP
    SEED_GAP = 13                      # seed13 writes the gap's first 0 (NN joins there)
    for i, ch in enumerate(pat):
        S(f'seed{i}', T(int(ch), 'R', f'seed{i+1}' if i + 1 < len(pat) else 'w'), None)

def test(halt_state):
    # ../legendre's mod walk: advance the D hole cyclically, then the R hole
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
    S('k1', T(0,'L','k1b'), T(1,'R','k2'))        # 0: d | m: composite
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
    S('sh5', T(0,'R',halt_state), T(1,'R','sh6'))   # 0: R has one cell: p = 1, HALT
    S('sh6', T(0,'R','pd'), T(1,'L','sh7'))       # 0: r = 0: m is prime
    S('sh7', None, T(0,'L','PM1'))                # R hole at cell 1, mod walk

def dispatch():
    # composite: k1b reads the cell left of D's separator cell: sentinel (P) or gap (Q)
    S('k1b', T(0,'R','PN2'), T(1,'R','v1'))
    S('v1', T(0,'R','v2'), None)                  # P: skip D's cells -1, 0, 1
    S('v2', None, T(1,'R','v3'))
    S('v3', T(0,'R','PN1'), None)
    # prime: pd reads two cells right of R: the sentinel (Q) or the gap (P)
    S('pd', T(0,'R','PS1'), T(0,'L','U'))

def nq():
    # the parser finds the Q hole, then the single 0 before the right sentinel
    parser_right('PN', T(1,'R','w'))
    S('w', T(1,'L','w2'), T(1,'R','PN1'))         # 1: Dq cell 3, go on; 0: past the sentinel
    S('w2', None, T(0,'L','w3'))                  # the sentinel moves one cell right
    S('w3', T(1,'L','PQ1'), None)                 # q += 1
    parser_left('PQ', T(1,'L','z'))               # back over Q, then the gap
    S('z', T(0,'L','z'), T(0,'L','e2'))           # p -= 2
    S('e2', None, T(0,'L','r1'))

def normalize():
    # from the right end of R: fill the separator, back to the D hole, D := 2
    S('r1', T(1,'L','r2'), T(1,'L','r1'))
    S('r2', T(1,'L','r3'), None)
    S('r3', T(0,'R','c5'), T(1,'L','r3'))
    S('c5', None, T(1,'R','c6'))
    S('c6', None, T(1,'R','c7'))
    S('c7', None, T(0,'R','c8'))
    S('c8', None, T(0,'R','sh4'))

def tq():
    # the parser finds the Q hole, then the single 0 before the right sentinel
    parser_right('PS', T(1,'R','u1'))
    S('u1', T(0,'L','u2'), T(1,'R','PS1'))
    S('u2', None, T(1,'L','u3'))
    S('u3', T(0,'L','r1'), None)                  # normalize Q from the end of Rq

def nn():
    # from the erased right sentinel: erase Rq, its separator, Dq with its hole and cell 0
    S('U', T(0,'L','X'), T(0,'L','x7'))           # 0: end+1 or a separator / hole; 1: Dq cell 0
    S('X', T(0,'L','U'), T(0,'L','X'))
    S('x7', T(1,'L','x7'), T(1,'R','x8'))         # fill the gap
    S('x8', T(0,'R',f'seed{SEED_GAP + 1}'), T(1,'R','x8'))   # as seed13: the new gap

def build(halt_state='halt', q0=2):
    """q0: the Q pair starts at q0 (test variants: q0 = 3, 4)."""
    ST.clear(); ORDER.clear()
    seed(q0); test(halt_state); dispatch(); nq(); normalize(); tq(); nn()
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    what = "Lemoine's conjecture is false" if q0 == 2 else \
        f'some odd n >= {3 + 2 * q0} is not p + 2q with p, q prime, q >= {q0} (test variant)'
    lines = [f'; Halts iff {what}.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'lemoine.txt', 'w').write(out)
    print(len(ORDER), 'states')
