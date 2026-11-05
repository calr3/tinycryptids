"""Generator for a 2-symbol Turing machine that halts iff Oppermann's conjecture is false: iff
for some n >= 2 there is no prime in (n^2 - n, n^2) or none in (n^2, n^2 + n).

With the quarter-squares q(j) = floor(j^2 / 4) (q(2n-1) = n^2 - n, q(2n) = n^2,
q(2n+1) = n^2 + n), the intervals of the conjecture are (q(j), q(j+1)) for j >= 3. Interval j
is taken as the ceil(j/2) numbers q(j) .. q(j+1) - 1; q(j) is prime only for j = 3 (q = 2, and
3 is in both versions), so it has a prime iff (q(j), q(j+1)) has one. The machine tests
m = 2, 3, 4, ... in turn.

Tape layout (blocks of 1s separated by '00'):
  [F] Q 00 D 00 R
  - Q (j+2 cells): its hole (a single 0) at cell 2k+1 marks the k-th number m = q(j) + k of
    interval j. The hole moves two cells per number, so the j cells hold ceil(j/2) numbers.
  - F: the flag "a prime was seen in this interval", a 1 at Q[-2] (Q[-1] is 0).
    At the end of the interval F is erased and the 0 next to it becomes cell 0 of the next Q
    (j+3 cells, hole at cell 1, the old cell 0).
  - D (d+2 cells) holds the trial divisor d >= 2; its hole (at cell c+1,
    0 <= c < d) is a cyclic counter c.  Cells 0 and d+1 are always 1.
  - R (r+2 cells) holds r = m - d, so d + r = m.  During the mod walk it has
    a hole (cells 1..r) counting the steps walked.
Candidate m, for d = 2 .. m-1 (r = m-2 .. 1):
  mod walk: r steps, each advancing the D hole cyclically; then d | r (iff
    d | m) iff the hole is back at cell 1.  If so, m is composite.
  else shift: d += 1, r -= 1; when r = 0, m is prime: set the flag.
Then move the Q hole two cells.  If it runs off Q, the interval is over: HALT if the
flag is not set, else Q grows by one cell.  Rebuild D := 2, R := m - 1 (for m + 1).
The seed writes the tape for m = 2 (j = 3, k = 0).
"""
import sys
SEED = '10111' + '00' + '1011' + '00' + '11'
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
    # Q = 10111 (j = 3, k = 0), 00, D = 1011 (d = 2), 00, R = 11 (r = 0):
    # written left to right; the last two cells play the roles of sh4, sh5.
    pat = SEED
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
    S('q1', T(1,'R','q2'), None)                  # fill the hole (cell p)
    S('q2', None, T(1,'R','q3'))
    S('q3', T(0,'L','ie1'), T(1,'R','q4'))        # 0: p was the last cell
    S('q4', T(0,'L','ie1'), T(1,'L','q5'))        # 0: p + 1 was the last cell
    S('q5', None, T(0,'R','PN1'))                 # the hole at cell p + 2
    # end of the interval: the flag decides
    S('ie1', T(0,'L','ie2'), T(1,'L','ie1'))
    S('ie2', T(0,'R',halt_state), T(0,'R','g1'))  # erase the flag
    if grow:    # the 0 left of Q becomes cell 0, the old cell 0 the hole
        S('g1', T(1,'R','g2'), None)
        S('g2', None, T(0,'R','PN1'))
    else:       # test variant: Q keeps its length (intervals of 2 numbers)
        S('g1', T(0,'R','g2'), None)
        S('g2', None, T(1,'R','g3'))
        S('g3', None, T(0,'R','PN1'))
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
    """grow=False: test variant with intervals of 2 numbers (halts at 8, 9)."""
    ST.clear(); ORDER.clear()
    seed(); modwalk(); shift(); prime(); advance(halt_state, grow); rebuild()
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    what = "Oppermann's conjecture is false" if grow else 'two consecutive composites start at 0 mod 2 (test variant)'
    lines = [f'; Halts iff {what}.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'oppermann.txt', 'w').write(out)
    print(len(ORDER), 'states')
