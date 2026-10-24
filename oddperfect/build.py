"""Generator for a 2-symbol Turing machine that halts iff an odd perfect number
exists (it searches n = 1, 3, 5, ... for sum of proper divisors = n).

Tape layout during the round for n (blocks of 1s separated by '00'):
  T 00 D 00 R
  - T (n+3 cells, cells 0..n+2) is a saturating counter u = min(s, n+1) of the sum
    s of the proper divisors found so far: a hole (single 0) at cell u+1.  The
    hole may sit on T's last cell (u = n+1, saturated): a run of three 0s with
    the separator, which every parser looking for it crosses from the right.
  - D (d+1 cells, cells 0..d) holds the candidate divisor d >= 1.  During the
    mod walk its hole steps cyclically over cells 1..d; its HOME is cell d, the
    last one (as in ../sierpinski).
  - R (r+1 cells, cells 0..r) holds r = n - d >= 1, so d + r = n.  During the
    mod walk it has a hole at cells 0..r-1 counting the steps walked.
Round for n, for d = 1 .. n-1 (r = n-1 .. 1):
  mod walk: r steps, each advancing the D hole cyclically and then the R hole;
    when the R hole falls off R, back over R: d | r (iff d | n) iff the D hole
    is home (the first cell met left of the separator).
  add (d | n): the D hole walks from home down to cell 0, one cell per step,
    and each step advances the T hole (which stays put on T's last cell:
    saturation costs no state, t2 just writes the hole back).  D ends without
    a hole.
  shift: fill the D hole if there is one; the first separator cell becomes D's
    new home (d += 1), R loses its cell 0 (r -= 1) and gets its hole at its new
    cell 0.  If R is then a single cell, r = 0: the round is over.
Round end: write R's new last cells (6 ones from the right), back to D, mark
  cell 1 of D (the next D), then to the T hole: it is at cell n+1 iff s = n:
  HALT.  Otherwise fill it, T gets two cells on the left (the new hole at cell
  1), and back right to the mark: D := 1 (home at cell 1), R := n + 1 with its
  hole at cell 0: the round for n + 2.
The seed writes T = 10, 00, D = 1: the end of a pseudo-round n = -1, which the
round end turns into the round for n = 1 (empty: r = 0), then n = 3, ...
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

SEED = '1000100'  # T = 10 (hole on its last cell), 00, D cell 0; then f6 at p+3
# the abundant test variant starts at the end of the round n = 1 instead: the pseudo-round
# n = -1 has a saturated T, which that variant would take for an abundant number
SEED_N1 = '10110010000'

def seed(pat):
    for i, ch in enumerate(pat):
        S(f'seed{i}', T(int(ch), 'R', f'seed{i+1}' if i + 1 < len(pat) else 'f6'), None)

def modwalk():
    # advance the D hole (head ends right of it); from home (cell d) it wraps to cell 1
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
    # back over R and the separator: is D's home the hole?
    S('e1', T(0,'L','e2'), T(1,'L','e1'))
    S('e2', T(0,'L','e3'), None)
    S('e3', T(1,'L','a2'), T(1,'L','f1'))         # 0: d | n: add d to T

def shift():
    # fill the D hole; the first separator cell is D's new home; R loses cell 0
    S('f1', T(1,'R','f2'), T(1,'L','f1'))
    S('f2', T(0,'R','f3'), T(1,'R','f2'))
    S('f3', T(0,'R','f4'), None)
    S('f4', None, T(0,'R','f5'))
    S('f5', None, T(0,'R','f6'))                  # the R hole at R's new cell 0
    S('f6', T(0,'R','h1'), T(1,'L','PM2'))        # 0: r = 0: the round is over

def add():
    # the D hole one cell left (from home: e3 fills it); off cell 0: done (shift)
    S('a1', T(1,'L','a2'), None)
    S('a2', T(0,'R','f2'), T(0,'L','PT1'))
    parser_left('PT', T(1,'R','t1'))
    S('t1', T(1,'R','t2'), None)
    S('t2', T(0,'L','t2'), T(0,'R','PA1'))       # 0: T's last cell: keep the hole there
    parser_right('PA', T(1,'L','a1'))

def roundend(halt_state, abundant):
    # R's new cells from the right, back over D to its cell 0, mark its cell 1
    S('h1', T(1,'L','h1'), T(1,'L','k1'))
    S('k1', T(0,'R','k2'), T(1,'L','k1'))
    S('k2', None, T(1,'R','k3'))
    S('k3', None, T(0,'L','PC1'))
    # the T hole: at cell n+1 (s = n) the two cells after it are 1, 0
    parser_left('PC', T(1,'R','x1'))
    S('x1', T(1,'R','x2'), None)
    S('x2', T(0,'L', halt_state if abundant else 'z1'), T(1,'R','x3'))  # 0: saturated
    S('x3', T(0,'L', 'z1' if abundant else halt_state), T(1,'L','z1'))  # 0: s = n
    # T: two more cells on the left, the hole at its new cell 1
    S('z1', T(0,'L','z2'), T(1,'L','z1'))
    S('z2', T(1,'R','PZ2'), None)
    # back to the mark: D := 1, then as after a shift
    parser_right('PZ', T(0,'R','f4'))

def build(halt_state='halt', abundant=False):
    """abundant=True: test variant that halts at the first odd abundant n (945)."""
    ST.clear(); ORDER.clear()
    seed(SEED_N1 if abundant else SEED); modwalk(); shift(); add(); roundend(halt_state, abundant)
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    what = 'an odd abundant number exists (test variant)' if abundant else 'an odd perfect number exists'
    lines = [f'; Halts iff {what} (searches n = 1, 3, 5, ... comparing sigma(n) - n with n).',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'oddperfect.txt', 'w').write(out)
    print(len(ORDER), 'states')
