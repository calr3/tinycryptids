"""Generator for a 2-symbol beeping Turing machine that beeps once for every m >= 2 with
m^2 | F(m - 1) if m = 1, 4 mod 5, else m^2 | F(m + 1) (F the Fibonacci numbers), so it beeps
infinitely often iff there are infinitely many Wall-Sun-Sun primes: it quasihalts iff there
are finitely many.  See README.md for why the composite m that pass are finitely many.

This is ../wallsunsun's machine without its trial division.  Tape at the start of round m:
    B 00 E 00 D
  - B (m + 1 cells, no hole): the odometer; its m - 1 inner cells are the bits of a binary
    string without two adjacent 1s (bit 1 = a hole).
  - E (m + 2 cells): the low base-m digit, a cyclic hole on cells 1 .. m.
  - D (m + 2 cells, its hole on cell 1): the high base-m digit.
Round m (entered at e1 on the separator left of D):
  * E's hole is put on cell m (digit m - 1); counting the m cells left of it mod 5 decides
    the first string: 10...0 if m = 1, 4 mod 5, else 0...0.
  * Odometer: tick E (on a wrap also D), go to the next string, tick, and so on, F(m + 1)
    (or F(m - 1)) ticks in all.
  * The check: E's hole back on cell m and D's on cell 1 iff m^2 | F(m -+ 1): that
    transition (q9 reading 0) is the BEEP.
  * Next round: E's hole is filled and E grows by a cell on the left (B gives its last cell
    and gets two on the left); D's hole is filled, D gets a cell on the right and its hole
    goes to cell 1.
Test variants: `extra` cells more in B, other residues `holes`, the round m0 the seed writes.
q7 reading 0 is taken iff E's hole is on cell m (m | F(m -+ 1)): a second beep for tests.
"""
import sys
ST = {}
ORDER = []
BEEP = ('q9', 0)
def S(name, t0, t1):
    assert name not in ST, name
    ST[name] = [t0, t1]; ORDER.append(name)
def T(w, d, n): return (w, d, n)

def canon(m):
    """The tape at the start of round m (state e1, the head on D's cell 0)."""
    return '1' * (m + 1) + '00' + '1' * (m + 2) + '00' + '10' + '1' * m

def parser_right(prefix, found):
    """Move right to the next hole. Lands at hole+1 (a 1) and performs `found` there."""
    S(prefix + '1', T(0, 'R', prefix + '2'), T(1, 'R', prefix + '1'))
    S(prefix + '2', T(0, 'R', prefix + '1'), found)

def parser_left(prefix, found):
    S(prefix + '1', T(0, 'L', prefix + '2'), T(1, 'L', prefix + '1'))
    S(prefix + '2', T(0, 'L', prefix + '1'), found)

def dadv(p, cont, wrap, cdir, wdir):
    """Advance a cyclic hole (cells 1..d of a block), starting on the hole (cell h).
    No wrap (h < d): the hole moves to h+1; the head ends on cell h+2 (cdir R) or h (L).
    Wrap (h = d): the hole moves to cell 1; the head ends on cell 2 (wdir R) or 0 (L)."""
    S(p + '1', T(1, 'R', p + '2'), None)
    S(p + '2', None, T(1, 'R', p + '3'))
    S(p + '3', T(0, 'L', p + 'w1'), T(1, 'L', p + '4'))
    S(p + '4', None, T(0, cdir, cont))
    S(p + 'w1', T(0, 'R', p + 'w2'), T(1, 'L', p + 'w1'))
    S(p + 'w2', None, T(1, 'R', p + 'w3'))
    S(p + 'w3', None, T(0, wdir, wrap))

def seed(extra, m0):
    # round m0 without D's hole: B, 00, E, 00, D written left to right; f3 makes the hole
    pat = '1' * (m0 + 1 + extra) + '00' + '1' * (m0 + 2) + '00' + '1' * (m0 + 2)
    for i, ch in enumerate(pat):
        last = i + 1 == len(pat)
        S(f'seed{i}', T(int(ch), 'L' if last else 'R', 'f3' if last else f'seed{i+1}'), None)

def init(holes):
    """From the separator left of D: E's hole on cell m, m mod 5 from the m cells left of
    it, maybe B's first bit."""
    S('e1', T(0, 'L', 'e2'), T(1, 'L', 'e1'))
    S('e2', T(0, 'L', 'e3'), None)
    S('e3', None, T(1, 'L', 'w'))
    S('w', None, T(0, 'L', 'm0'))
    for k in range(5):
        S(f'm{k}', T(0, 'L', 'h1') if k in holes else T(0, 'R', 'QE1'), T(1, 'L', f'm{(k + 1) % 5}'))
    S('h1', T(0, 'L', 'h3'), None)
    S('h3', T(0, 'R', 'h4'), T(1, 'L', 'h3'))
    S('h4', None, T(1, 'R', 'h5'))
    S('h5', None, T(0, 'R', 'QE1'))

def odometer():
    S('sc', T(1, 'L', 'sc'), T(1, 'L', 'nb'))         # 0: clear a hole
    S('nb', T(1, 'L', 'nb2'), T(1, 'R', 'st'))        # 1: the candidate can be set
    S('nb2', T(0, 'R', 'ov'), T(1, 'L', 'nb'))        # 0: past B: the last string
    S('st', None, T(0, 'R', 'QE1'))
    S('ov', None, T(0, 'R', 'q1'))
    parser_right('QE', T(1, 'L', 'a1'))
    dadv('a', 'rL', 'QD1', 'L', 'R')
    parser_right('QD', T(1, 'L', 'b1'))
    dadv('b', 'PB1', 'PB1', 'L', 'L')
    parser_left('PB', T(1, 'L', 'rL'))
    S('rL', T(0, 'L', 'r2'), T(1, 'L', 'rL'))
    S('r2', T(0, 'L', 'r3'), None)
    S('r3', T(1, 'L', 'sc'), T(1, 'L', 'sc'))           # 0: only in round 1 (no inner cells)

def check():
    """E's hole on cell m and D's on cell 1: beep.  Then to the next round."""
    S('q1', T(0, 'R', 'q2'), T(1, 'R', 'q1'))
    S('q2', T(0, 'R', 'q3'), None)
    S('q3', T(0, 'R', 'q4'), T(1, 'R', 'q3'))
    S('q4', None, T(1, 'R', 'q5'))
    S('q5', T(0, 'R', 'q7'), T(1, 'R', 'g0'))         # 0: E's hole on cell m
    S('q7', T(0, 'R', 'q8'), None)
    S('q8', None, T(1, 'R', 'q9'))
    S('q9', T(0, 'L', 'q10'), T(1, 'L', 'q10'))       # 0: BEEP (D's hole on cell 1)
    S('q10', None, T(1, 'L', 'q11'))
    S('q11', T(0, 'L', 'g0'), None)

def nextround():
    S('g0', T(0, 'L', 'g1'), T(1, 'R', 'g0'))
    S('g1', T(1, 'L', 'g2'), T(1, 'L', 'g1'))
    S('g2', T(0, 'L', 'g3'), T(1, 'L', 'g1'))         # 1: that 0 was E's hole
    S('g3', None, T(0, 'L', 'g4'))
    S('g4', T(1, 'L', 'g5'), T(1, 'L', 'g4'))
    S('g5', T(1, 'R', 'PF1'), None)
    # to D's hole: fill it, one more cell on the right, the hole on cell 1
    parser_right('PF', T(1, 'L', 'f1'))
    S('f1', T(1, 'R', 'f2'), None)
    S('f2', T(1, 'L', 'f3'), T(1, 'R', 'f2'))
    S('f3', T(0, 'R', 'f4'), T(1, 'L', 'f3'))
    S('f4', None, T(1, 'R', 'f5'))
    S('f5', None, T(0, 'L', 'e1'))

def build(extra=0, holes=(1, 4), m0=2, with_seed=True):
    ST.clear(); ORDER.clear()
    if with_seed:
        seed(extra, m0)
    init(holes); odometer(); check(); nextround()
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST)
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    return ORDER[:], {k: v[:] for k, v in ST.items()}

def write(order, states, f, title):
    f.write(f'; {title}\n; {len(order)} states, 2 symbols. Generated by build.py.\n'
            f'; Beep: {BEEP[0]} reading {BEEP[1]}.\n\nblank_symbol: 0\n\n')
    for s in order:
        f.write(s + '\n')
        for r, t in enumerate(states[s]):
            f.write('    -\n' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}\n')
    f.write('\n')

if __name__ == '__main__':
    order, states = build()
    with open('wallsunsuninf.txt', 'w') as f:
        write(order, states, f, 'Beeps once per m >= 2 with m^2 | F(m -+ 1): quasihalts iff finitely many Wall-Sun-Sun primes.')
    print(len(order), 'states -> wallsunsuninf.txt')
    order, states = build(with_seed=False)
    with open('wallsunsuninf_noseed.txt', 'w') as f:
        write(order, states, f, 'The design without its seed (merged first, then seedfit.py fits a seed).')
    print(len(order), 'states -> wallsunsuninf_noseed.txt')
