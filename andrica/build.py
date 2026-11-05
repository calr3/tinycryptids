"""Generator for a 2-symbol Turing machine that halts iff Andrica's conjecture is false:
iff some consecutive primes p < q have 4p <= (q - p - 1)^2.

Let t(m) be the least t with t^2 >= 4m.  Then 4p <= g^2 iff t(p) <= g, so the conjecture
fails iff after some prime p the next t(p) numbers p + 1, ..., p + t(p) are all composite.
The machine tests m = 2, 3, 4, ... by ../legendre's trial division and keeps a countdown:
a prime resets it to t(m), a composite counts down, and the machine halts when the
countdown runs out.

Tape (blocks of 1s separated by '00'):
  H 00 U 00 T 00 D 00 R
  - H (t + 1 cells, t = t(m)) has a hole at cell 2j - 1, where m is the j-th number with
    t(m) = t (there are floor(t/2) of them: t(m) = t for floor((t-1)^2/4) < m <= floor(t^2/4)).
    The hole moves on by two cells per number; when it would leave H, t += 1: H's last cell
    becomes the separator's first cell, the separator's last cell becomes U's new cell 0,
    and H gets two new cells on the left, with the hole at the new cell 1.
  - U 00 T (U may be empty: then four 0s), |U| + |T| = t: the countdown is |T|.  A prime puts
    the separator at the left end (|U| = 0, |T| = t), each composite moves it one cell right;
    at the composite that empties T the machine HALTs.  U grows when H wraps, so |T| does
    not change: the machine halts at the t(p)-th composite in a row after the prime p.
  - D 00 R: ../legendre's pair, d + r = m (D has d + 2 cells with a hole, R has r + 2).
Round m (starting at sh4 with d = 2): trial division ends at k1 (composite) or sh6 (prime);
the head goes left to the U/T separator (a scan for the second 00; for a prime a parser
first crosses D's hole): composite -> move it right (HALT if T is empty now), prime -> fill
it and write it at U's left end; a parser finds H's hole: advance it by two (or grow H and
U); a parser finds D's hole; rebuild D := 2, R := m - 1 (one cell more) for m + 1.
The seed writes the tape for m = 2: 1011 00 00 111 00 1011 00 11.

Test variants: 'short' (T never grows: halts at m = 10, three composites after 7) and
'slow' (T starts with 2 cells, H grows by 3 cells at each wrap: halts at m = 126,
the 13 composites after 113).
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

def seed(t0):
    pat = '1011' + '00' + '00' + '1' * t0 + '00' + '1011' + '00' + '11'
    for i, ch in enumerate(pat):
        S(f'seed{i}', T(int(ch), 'R', f'seed{i+1}' if i + 1 < len(pat) else 'sh6'), None)

def test():
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
    S('k1', T(0,'L','y1'), T(1,'R','k2'))        # 0: d | m: composite
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
    S('sh6', T(0,'L','PC1'), T(1,'L','sh7'))      # 0: r = 0: m is prime
    S('sh7', None, T(0,'L','PM1'))                # R hole at cell 1, mod walk

def countdown(halt_state):
    # composite: find the U/T separator (00) to the left; move it one cell right (T loses a
    # cell); T empty: HALT
    S('y1', T(0,'L','y2'), T(1,'L','y1'))
    S('y2', T(1,'R','z1'), T(1,'L','y1'))         # 0: the separator's left cell
    S('z1', T(0,'R','z2'), None)
    S('z2', None, T(0,'R','z3'))
    S('z3', T(0,'R',halt_state), T(1,'L','PH1'))   # 0: T had one cell: HALT
    # prime: past the D hole, find the U/T separator; fill it, new separator at the region's
    # cells 0, 1 (U empty)
    parser_left('PC', T(1,'L','x0'))
    S('x0', T(0,'L','x1'), None)
    S('x1', T(0,'L','x2'), T(1,'L','x1'))
    S('x2', T(1,'R','f2'), T(1,'L','x1'))
    S('f2', T(1,'L','f3'), None)
    S('f3', T(0,'R','f4'), T(1,'L','f3'))
    S('f4', None, T(0,'R','f5'))
    S('f5', None, T(0,'L','PH2'))

def phase(tgrow, hgrow):
    parser_left('PH', T(1,'R','a1'))
    S('a1', T(1,'R','a2'), None)
    S('a2', None, T(1,'R','a3'))
    if tgrow:
        S('a3', T(0,'R','w1'), T(1,'R','a4'))     # 0, both: H's hole was at its last two cells
        S('a4', T(0,'R','w1'), T(1,'L','a5'))
    else:
        S('a3', T(0,'L','w4'), T(1,'R','a4'))
        S('a4', T(0,'L','w4'), T(1,'L','a5'))
    S('a5', None, T(0,'R','PN1'))
    # wrap: H's last cell joins the separator, which gives U a new cell 0
    if tgrow:
        S('w1', T(1,'L','w2'), None)
        S('w2', T(0,'L','w3'), None)
        S('w3', None, T(0,'L','w4'))
    # n = hgrow + tgrow new cells left of H (2 in the real machine), the hole at new cell 1;
    # w4 scans left over H and writes the new cells right to left from the blank
    n = hgrow + tgrow
    cells = [0 if i == 1 else 1 for i in range(n)]
    names = ['w4'] + [f'w{5 + i}' for i in range(n - 1)] + ['wh']
    for i in range(n):                            # names[i] writes new cell n - 1 - i
        t = T(cells[n - 1 - i], 'L' if i + 1 < n else 'R', names[i + 1])
        S(names[i], t, T(1,'L','w4') if i == 0 else None)
    # on new cell 1: the hole (written already, or old cell 0 when n = 1); one cell past it
    S('wh', T(0,'R','PN1') if n > 1 else None, T(0,'R','PN1') if n == 1 else None)

def ret():
    parser_right('PN', T(1,'R','c1'))
    # D := 2 (cells 0..3), separator at cells 4, 5, R := the rest plus one cell
    S('c1', T(1,'R','c2'), T(1,'R','c1'))
    S('c2', T(1,'R','c3'), None)
    S('c3', T(1,'L','c4'), T(1,'R','c3'))
    S('c4', T(0,'R','c5'), T(1,'L','c4'))
    S('c5', None, T(1,'R','c6'))
    S('c6', None, T(1,'R','c7'))
    S('c7', None, T(0,'R','c8'))
    S('c8', None, T(0,'R','sh4'))

VARIANTS = {None: (3, 1, 1), 'short': (3, 0, 1), 'slow': (2, 1, 3)}

def build(halt_state='halt', variant=None):
    ST.clear(); ORDER.clear()
    t0, tgrow, hgrow = VARIANTS[variant]
    seed(t0); test(); countdown(halt_state); phase(tgrow, hgrow); ret()
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    what = "Andrica's conjecture is false" if variant is None else f'test variant {variant}'
    lines = [f'; Halts iff {what}.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'andrica.txt', 'w').write(out)
    print(len(ORDER), 'states')
