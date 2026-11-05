"""Generator for a 2-symbol Turing machine that halts iff Legendre's conjecture
is false: iff for some n >= 1 there is no prime p with n^2 < p < (n+1)^2.

It tests m = 2, 3, 4, ... in turn. Interval n is m = n^2 .. n^2 + 2n (for n = 1
only m = 2, 3); n^2 itself is never prime, so the interval has a prime iff
(n^2, (n+1)^2) has one.

Tape layout (blocks of 1s separated by '00'):
  [F] Q 00 D 00 R
  - Q (2n+3 cells): its hole (a single 0) at cell k+1 marks the k-th candidate
    m = n^2 + k of interval n.
  - F: the flag "a prime was seen in this interval", a 1 at Q[-2] (Q[-1] is 0).
    At the end of the interval F and the 0 next to it become the first two
    cells of the next Q (2n+5 cells, hole at cell 1).
  - D (d+2 cells) holds the trial divisor d >= 2; its hole (at cell c+1,
    0 <= c < d) is a cyclic counter c.  Cells 0 and d+1 are always 1.
  - R (r+2 cells) holds r = m - d, so d + r = m.  During the mod walk it has
    a hole (cells 1..r) counting the steps walked.
Candidate m, for d = 2 .. m-1 (r = m-2 .. 1):
  mod walk: r steps, each advancing the D hole cyclically; then d | r (iff
    d | m) iff the hole is back at cell 1.  If so, m is composite.
  else shift: d += 1, r -= 1; when r = 0, m is prime: set the flag.
Then advance the Q hole.  If it runs off Q, the interval is over: HALT if the
flag is not set, else the flag joins Q.  Rebuild D := 2, R := m - 1 (for m + 1).
The seed writes the tape for m = 2 (n = 1, k = 1).
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

def seed():
    # Q = 11011 (n = 1, k = 1), 00, D = 1011 (d = 2), 00, R = 11 (r = 0):
    # written left to right; the last two cells play the roles of sh4, sh5.
    pat = '11011' + '00' + '1011' + '00' + '11'
    for i, ch in enumerate(pat):
        S(f'seed{i}', T(int(ch),'R', f'seed{i+1}' if i+1 < len(pat) else 'sh6'), None)

def modwalk():
    # advance the D hole cyclically (head ends right of it), then the R hole
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
    S('k1', T(0,'L','PQ2'), T(1,'R','k2'))        # 0: d | m: composite
    S('k2', None, T(1,'R','k3'))
    S('k3', T(1,'L','rs1'), None)                 # fill hole, reset it to cell 1
    S('rs1', T(0,'R','rs2'), T(1,'L','rs1'))
    S('rs2', None, T(1,'R','rs3'))
    S('rs3', None, T(0,'R','sh1'))

def shift():
    # head in D (a 1 right of the hole at cell 1): d += 1, r -= 1
    S('sh1', T(1,'R','sh2'), T(1,'R','sh1'))
    S('sh2', T(0,'R','sh3'), None)
    S('sh3', None, T(0,'R','sh4'))
    S('sh4', None, T(1,'R','sh5'))
    S('sh5', None, T(1,'R','sh6'))
    S('sh6', T(0,'L','PC1'), T(1,'L','sh7'))      # 0: r = 0: m is prime
    S('sh7', None, T(0,'L','PM1'))                # R hole at cell 1, mod walk

def prime():
    # set the flag: past the D hole to the Q hole, left to Q's start, then
    # back to the Q hole
    parser_left('PC', T(1,'L','PP1'))
    parser_left('PP', T(1,'L','fl1'))
    S('fl1', T(0,'L','fl2'), T(1,'L','fl1'))
    S('fl2', T(1,'R','PF2'), T(1,'R','PF2'))      # the flag (maybe set already)
    parser_right('PF', T(1,'L','q1'))

def advance(halt_state, grow):
    parser_left('PQ', T(1,'R','q1'))
    S('q1', T(1,'R','q2'), None)
    S('q2', None, T(1,'R','q3'))
    S('q3', T(0,'L','ie1'), T(1,'L','q4'))        # 0: past the last candidate
    S('q4', None, T(0,'R','PN1'))
    # end of the interval: the flag decides
    S('ie1', T(0,'L','ie2'), T(1,'L','ie1'))
    if grow:
        S('ie2', T(0,'R',halt_state), T(1,'R','PN2'))   # flag + 0 start the new Q
    else:   # test variant: Q keeps its length (intervals of 3 candidates)
        S('ie2', T(0,'R',halt_state), T(0,'R','iv1'))
        S('iv1', T(0,'R','iv2'), None)
        S('iv2', None, T(1,'R','iv3'))
        S('iv3', None, T(0,'R','PN1'))
    parser_right('PN', T(1,'R','c1'))             # to the D hole (cell 1)

def rebuild():
    # D := 2 (cells 0..3), separator at cells 4, 5, R := the rest plus one cell
    S('c1', T(1,'R','c2'), T(1,'R','c1'))
    S('c2', T(1,'R','c3'), None)
    S('c3', T(1,'L','c4'), T(1,'R','c3'))
    S('c4', T(0,'R','c5'), T(1,'L','c4'))
    S('c5', None, T(1,'R','c6'))
    S('c6', None, T(1,'R','c7'))
    S('c7', None, T(0,'R','c8'))
    S('c8', None, T(0,'R','sh4'))                 # then as after a shift

def build(halt_state='halt', grow=True):
    """grow=False: test variant with intervals of 3 numbers (halts at 25..27)."""
    ST.clear(); ORDER.clear()
    seed(); modwalk(); shift(); prime(); advance(halt_state, grow); rebuild()
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    what = "Legendre's conjecture is false" if grow else 'three consecutive composites start at 1 mod 3 (test variant)'
    lines = [f'; Halts iff {what}.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'legendre.txt', 'w').write(out)
    print(len(ORDER), 'states')
