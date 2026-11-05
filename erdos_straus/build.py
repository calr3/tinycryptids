"""Generator for a 2-symbol Turing machine that halts iff the Erdos-Straus conjecture is FALSE:
iff some n >= 2 has no solution of 4/n = 1/x + 1/y + 1/z in positive integers.

The search. A solution sorted x <= y <= z has n/4 < x <= 3n/4; with a = 4x - n, m = nx and
D = ay - m (= 4xy - n(x + y)) it has D >= 1, z = my / D, and z >= y iff D <= m. Conversely any
D >= 1 with D | my gives the solution z = my / D. So for n = 2, 3, ...:

    for x = 1, 2, ...:  U = 4x
        if U <= n: next x                       (a <= 0: the debt phase)
        if U > 3n: HALT                         (no solution for n)
        a = U - n, m = n x
        for y = 1, 2, ...:  W = a y
            if W > 2m + 2: next x               (D > m; the last two tests are spare)
            if W > m and (W - m) | m y: next n  (a solution)

Tape (blocks of 1s separated by '00'; a 'hole' is a single 0 inside a block):

    A 00 R 00 N 00 M 00 K [00 D 00 P]

* A: a + 1 cells (a = 0 in the debt phase); the consume cursor runs over cells 1 .. a.
* R: 2n + 3 - a cells. In the debt phase its hole is on cell 2n + 1 - 2U (two cells per unit of
  U, from the right). When U passes n the hole would land left of R: from then on each unit of U
  moves the separator A | R one cell right (A grows, R shrinks); HALT when R would keep fewer
  than 3 cells (a > 2n).
* N: n + 1 cells; its cursor runs over cells 1 .. n (M += n, K += n).
* M: m + 1 cells; its cursor runs over cells 1 .. m (P += m).
* K: the y counter, m + 4 cells at the start of a y loop. First lap: its hole moves left, from
  cell m + 2 (W = 0) to cell 1 (W = m + 1). Second lap: the hole stays on cell 1 and each unit
  moves the separator K | D one cell left (K shrinks, D grows), until K = 1 0 1.
* D: d + 1 cells, d = max(1, W - m); P: p + 1 cells, p = m y. Both exist only in the y loop.
The test d | p is ../oddperfect's mod walk on D 00 P (D's hole cyclic over cells 1 .. d,
home = cell d; P's hole counts p steps from cell 0).
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
def to_end_right(prefix, done):
    """Right to the first run of three 0s; `done` is taken reading the third 0."""
    S(prefix+'1', T(0,'R',prefix+'2'), T(1,'R',prefix+'1'))
    S(prefix+'2', T(0,'R',prefix+'3'), T(1,'R',prefix+'1'))
    S(prefix+'3', done, T(1,'R',prefix+'1'))
def to_end_left(prefix, done):
    S(prefix+'1', T(0,'L',prefix+'2'), T(1,'L',prefix+'1'))
    S(prefix+'2', T(0,'L',prefix+'3'), T(1,'L',prefix+'1'))
    S(prefix+'3', done, T(1,'L',prefix+'1'))
def k_finder(prefix, found1, found2):
    """Right to the K hole: `found1` at hole+1 when the hole is on a cell >= 2, `found2` reading
    the hole when it is on cell 1 (the first single 0 met is the K hole; the separators met are
    single runs of two 0s)."""
    S(prefix+'1', T(0,'R',prefix+'2'), T(1,'R',prefix+'1'))
    S(prefix+'2', T(0,'R',prefix+'3'), found1)
    S(prefix+'3', None, T(1,'R',prefix+'4'))
    S(prefix+'4', found2, T(1,'R',prefix+'1'))

RATE = 4      # the numerator (test variants change it)
SLACK = 3     # R keeps SLACK cells; SLACK >= RATE - 1 (test variants with RATE > 4)
HALT = 'halt'
NOHIT = False # test variant: a divisor is not a hit (every x of n0 is searched to the end)

def ST_S(s):
    """The transition of the s-th last separator move: fill the cell, move right."""
    return T(1,'R', f'S{s-1}' if s > 1 else 'Z1')

def xstep():
    # the N cursor to cell 1, from the right (K's last cell) or from R (debt)
    S('g1', T(0,'L','g2'), T(1,'L','g1'))         # K
    S('g2', T(0,'L','g3'), None)
    S('g3', T(0,'L','g4'), T(1,'L','g3'))         # M
    S('g4', T(0,'L','g5'), None)
    S('g5', T(0,'R','g6'), T(1,'L','g5'))         # N
    S('g6', None, T(1,'R','g7'))
    S('g7', None, T(0,'R','cb1'))
    S('gd1', T(0,'R','gd2'), T(1,'R','gd1'))      # (from the debt hole) the rest of R
    S('gd2', T(0,'R','g6'), None)
    # per N cell: M += 1 (the separator M | K one cell right), K += 1 (two cells at its end)
    S('cb1', T(0,'R','cb2'), T(1,'R','cb1'))      # the rest of N
    S('cb2', T(0,'R','cb3'), None)
    S('cb3', T(1,'R','cb4'), T(1,'R','cb3'))      # M; its separator's first cell -> M
    S('cb4', T(0,'R','cb5'), None)
    S('cb5', None, T(0,'R','cb6'))                # K's first cell -> separator
    S('cb6', T(1,'R','cb7'), T(1,'R','cb6'))
    S('cb7', T(1,'L','CL1'), None)
    parser_left('CL', T(1,'R','ca1'))             # back to the N cursor
    S('ca1', T(1,'R','ca2'), None)
    S('ca2', T(0,'L','q1'), T(0,'R','cb1'))       # 0: the cursor was on N's last cell
    # the RATE units of U: left over N to R; R's hole (debt) or the separator A | R
    S('q1', T(0,'L','q2'), T(1,'L','q1'))
    S('q2', T(0,'L','q3'), None)
    S('q3', T(0,'L','q4'), T(1,'L','q3'))
    S('q4', ST_S(RATE), T(1,'R','w0'))            # 0: the separator (no debt): RATE moves
    # debt: the hole walks 2 RATE cells left; a 0 at the even offset 2k is the separator: the
    # hole would land left of R at unit k, which with the remaining units is a separator move
    S('w0', T(1,'L','w1'), None)
    for j in range(1, 2 * RATE + 1):
        nxt = T(1,'L',f'w{j+1}') if j < 2 * RATE else T(0,'R','gd1')   # (the hole lands: next x)
        cross = T(0,'L',f'S{RATE + 1 - j // 2}') if j % 2 == 0 else None
        S(f'w{j}', cross, nxt)
    # s moves of the separator A | R: fill s cells from it, zero the next two, then R must
    # keep SLACK cells
    for s in range(RATE, 0, -1):
        S(f'S{s}', ST_S(s), ST_S(s))
    S('Z1', T(0,'R','Z2'), T(0,'R','Z2'))
    S('Z2', T(0,'R',HALT), T(0,'R','H1'))           # 0: R had 3 cells and 4 moves (a > 2n)
    for i in range(1, SLACK + 1):
        S(f'H{i}', T(0,'R',HALT), T(1,'R',f'H{i+1}' if i < SLACK else 'su1'))
    # set up the y loop: K's hole on its last-but-one cell, D = 11, P = 1 at the end
    to_end_right('su', T(0,'L','sa1'))
    S('sa1', T(0,'L','sa2'), None)
    S('sa2', T(0,'L','sa3'), None)
    S('sa3', None, T(1,'L','sa4'))
    S('sa4', None, T(0,'R','sa5'))
    S('sa5', None, T(1,'R','sa6'))
    S('sa6', T(0,'R','sa7'), None)
    S('sa7', T(0,'R','sa8'), None)
    S('sa8', T(1,'R','sa9'), None)
    S('sa9', T(1,'R','sa10'), None)
    S('sa10', T(0,'R','sa11'), None)
    S('sa11', T(0,'R','sa12'), None)
    S('sa12', T(1,'L','YK1'), None)

def yloop():
    # P += M: from the right, cross the K hole, the M cursor to cell 1
    parser_left('YK', T(1,'L','ym1'))
    S('ym1', T(0,'L','ym2'), T(1,'L','ym1'))      # K's first cells
    S('ym2', T(0,'L','ym3'), None)
    S('ym3', T(0,'R','ym4'), T(1,'L','ym3'))      # M
    S('ym4', None, T(1,'R','ym5'))
    S('ym5', None, T(0,'R','ce1'))
    to_end_right('ce', T(0,'L','ce4'))            # one cell onto P's end per M cell
    S('ce4', T(0,'L','ce5'), None)
    S('ce5', T(1,'L','MK1'), None)
    parser_left('MK', T(1,'L','MM1'))             # cross the K hole
    parser_left('MM', T(1,'R','mc1'))             # the M cursor
    S('mc1', T(1,'R','mc2'), None)
    S('mc2', T(0,'L','u1'), T(0,'R','ce1'))       # 0: M is done
    # W += a: the A cursor to cell 1 (left end), one unit per A cell
    to_end_left('u', T(0,'R','ul4'))
    S('ul4', T(0,'R','ul5'), None)
    S('ul5', T(0,'R','ul6'), None)
    S('ul6', None, T(1,'R','ul7'))
    S('ul7', None, T(0,'R','f1'))
    k_finder('f', T(1,'L','k1'), T(0,'R','l1'))
    # first lap: the K hole one cell left
    S('k1', T(1,'L','k2'), None)
    S('k2', None, T(0,'L','AC1'))
    # second lap: the separator K | D one cell left, unless K = 1 0 1 (the y loop is over)
    S('l1', T(0,'L','l2'), T(1,'R','l1'))
    S('l2', None, T(1,'L','l3'))
    S('l3', T(1,'R','x1'), T(1,'R','l4'))         # 0: K = 1 0 1
    S('l4', None, T(0,'R','l5'))
    S('l5', T(0,'R','l6'), None)
    S('l6', T(1,'L','AK1'), None)
    parser_left('AK', T(1,'L','AC1'))             # cross the K hole
    parser_left('AC', T(1,'R','ac1'))             # the A cursor
    S('ac1', T(1,'R','ac2'), None)
    S('ac2', T(0,'R','af1'), T(0,'R','f1'))       # 0: A is done
    # second lap (the K hole on cell 1): the test d | p; first lap: next y
    S('af1', T(0,'R','F1'), None)
    k_finder('F', T(1,'L','YK1'), T(0,'R','ms1'))
    # mod walk setup: the walk's first step done by hand: D's hole from home (cell d) to cell 1,
    # P's hole from cell 0 (no hole needed there) on to cell 1 (ra2)
    S('ms1', T(0,'R','ms2'), T(1,'R','ms1'))      # K
    S('ms2', T(0,'R','ms3'), None)
    S('ms3', None, T(1,'R','ms4'))
    S('ms4', None, T(0,'R','ms5'))                # D's cell 1
    S('ms5', T(0,'R','ms6'), T(1,'R','ms5'))      # D
    S('ms6', T(0,'R','ms7'), None)
    S('ms7', None, T(1,'R','ra2'))                # P's cell 0
    # the y loop is over (K = 1 0 1, d = m + 2): K := K 00 D less 4 cells (m + 4), P erased
    S('x1', None, T(1,'R','x2'))
    S('x2', T(1,'R','x3'), None)
    S('x3', T(1,'R','x4'), None)
    S('x4', T(0,'R','x5'), T(1,'R','x4'))         # D
    S('x5', T(0,'R','x6'), None)
    S('x6', T(0,'L','x7'), T(0,'R','x6'))         # erase P
    S('x7', T(0,'L','x7'), T(0,'L','x8'))
    S('x8', None, T(0,'L','x9'))
    S('x9', None, T(0,'L','x10'))
    S('x10', None, T(0,'L','XA1'))
    # fill the A cursor (left behind by the stop), then over A and R to N's cell 0
    parser_left('XA', T(1,'R','xa1'))
    S('xa1', T(1,'R','xa2'), None)
    S('xa2', T(0,'R','xa3'), T(1,'R','xa2'))      # A
    S('xa3', T(0,'R','gd1'), None)

def modwalk():
    # ../oddperfect/build.py
    S('ma1', T(1,'R','ma2'), None)
    S('ma2', T(0,'L','mw1'), T(0,'R','PR1'))
    S('mw1', T(0,'R','mw2'), T(1,'L','mw1'))
    S('mw2', None, T(1,'R','mw3'))
    S('mw3', None, T(0,'R','PR1'))
    parser_right('PR', T(1,'L','ra1'))
    S('ra1', T(1,'R','ra2'), None)
    S('ra2', None, T(1,'R','ra3'))
    S('ra3', T(0,'L','e1'), T(1,'L','ra4'))
    S('ra4', None, T(0,'L','PM1'))
    parser_left('PM', T(1,'R','ma1'))
    S('e1', T(0,'L','e2'), T(1,'L','e1'))
    S('e2', T(0,'L','e3'), None)
    S('e3', T(1,'L','YK1') if NOHIT else T(0,'L','NK1'), T(1,'L','nf1'))  # 0: d | p: next n
    # not a divisor: fill D's hole, next y
    S('nf1', T(1,'L','YK1'), T(1,'L','nf1'))

def nstep():
    # left over D, the K hole and M; erase from M to the end (up to four 0s)
    parser_left('NK', T(1,'L','n2'))
    S('n2', T(0,'L','n3'), None)
    S('n3', T(0,'L','n4'), None)
    S('n4', T(0,'R','er1'), T(1,'L','n4'))        # M
    S('er1', T(0,'R','er2'), T(0,'R','er1'))
    S('er2', T(0,'R','er3'), T(0,'R','er1'))
    S('er3', T(0,'R','er4'), T(0,'R','er1'))
    S('er4', T(0,'L','er5'), T(0,'R','er1'))
    S('er5', T(0,'L','er5'), T(1,'R','nc1'))      # back to N's last cell
    # N += 1 at its end, then left to the separator A | R
    S('nc1', T(1,'L','nc2'), None)
    S('nc2', T(0,'L','nc3'), T(1,'L','nc2'))      # N
    S('nc3', T(0,'L','nr2'), None)
    # R += a + 2: fill the separator A | R, A's cell 0 becomes a separator cell, A := 1 two
    # cells further left
    S('nr2', T(1,'L','nr3'), T(1,'L','nr2'))      # R
    S('nr3', T(1,'L','nr4'), None)
    S('nr4', T(0,'L','nr5'), T(1,'L','nr4'))      # A
    S('nr5', T(1,'R','nr6'), None)
    S('nr6', T(0,'R','nr7'), None)
    S('nr7', None, T(0,'R','nh1'))
    # R's hole on its last-but-one cell (U = 0)
    S('nh1', T(0,'L','nh2'), T(1,'R','nh1'))
    S('nh2', None, T(1,'L','nh3' if SLACK == 3 else 'nhx0'))
    for i in range(SLACK - 3):                    # (test variants with RATE > 4)
        S(f'nhx{i}', None, T(1,'L',f'nhx{i+1}' if i + 1 < SLACK - 3 else 'nh3'))
    S('nh3', None, T(0,'R','NE1'))
    # M = 1, K = 1111 at the end, then the N loop of the first x
    to_end_right('NE', T(1,'R','nw1'))
    S('nw1', T(0,'R','nw2'), None)
    S('nw2', T(0,'R','nw3'), None)
    S('nw3', T(1,'R','nw4'), None)
    S('nw4', T(1,'R','nw5'), None)
    S('nw5', T(1,'R','nw6'), None)
    S('nw6', T(1,'L','g1'), None)

def seed(pat):
    """Writes the tape, then enters er5 (the n-step after the erase)."""
    for i, ch in enumerate(pat):
        S(f'seed{i}', T(int(ch), 'R', f'seed{i+1}' if i + 1 < len(pat) else 'er5'), None)

def seed_pattern(n0):
    """The end of a solved round n0 - 1 with a = 1: A 00 R 00 N."""
    n = n0 - 1
    return '11' + '00' + '1' * (2 * n + SLACK - 1) + '00' + '1' * (n + 1)

def build(halt_state='halt', n0=2, rate=4, nohit=False):
    """Test variants: n0 = 1 (halts at n = 1), rate = k (searches k/n = 1/x + 1/y + 1/z),
    nohit (no test succeeds: halts at n0 after all its x)."""
    global HALT, RATE, SLACK, NOHIT
    HALT, RATE, SLACK, NOHIT = halt_state, rate, max(3, rate - 1), nohit
    ST.clear(); ORDER.clear()
    seed(seed_pattern(n0)); xstep(); yloop(); modwalk(); nstep()
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    lines = ['; Halts iff the Erdos-Straus conjecture is false (searches, for n = 2, 3, ...,',
             '; the pairs x, y with D = 4xy - n(x+y) >= 1 for D | nxy; halts at the first n',
             '; without one).',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'erdos_straus.txt', 'w').write(out)
    print(len(ORDER), 'states')
