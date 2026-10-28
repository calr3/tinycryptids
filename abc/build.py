"""Generator for a 2-symbol Beeping Booping Turing machine for the abc conjecture.

The machine never halts.  It has two special transitions, a BEEP (state xe3 reading 0) and a
BOOP (state xq6 reading 0).  Its output is the sequence of beep counts between consecutive
boops.  Some value occurs infinitely often in that sequence iff the abc conjecture is FALSE,
in the form: for some n >= 1 there are infinitely many coprime a, b >= 1 with
c^n > rad(abc)^(n+1), c = a + b.

Search.  For c = 2, 3, ...; a = 1 .. c-1; b = c - a (each pair (a, b) once):
  * factor phase: R := rad(abc) and the coprimality test, by trial divisors d = 2 .. c:
      d hits if gcd(d, x) > 1 for x = a, b or c (tested in this order, stopping at the
      first hit); a hit with gcd(d, R) = 1 multiplies R by d.  Then R = rad(abc) (a prime
      d dividing abc hits and is coprime to R; a composite d that hits shares a smaller
      prime factor with abc, which already divides R).  At d = c a hit on a or b means
      gcd(c, a) = gcd(a, b) > 1: the pair is skipped.
  * pre-test: if c <= R the pair is skipped (then c^n <= R^n < R^(n+1) for every n).
  * power phase: P := 1, Q := 1; Q := Q*R; then repeat: compare P with Q; P <= Q: BEEP,
    P := P*c, Q := Q*R; P > Q: BOOP, next pair.  The compares are (1, R), (c, R^2), ...,
    (c^k, R^(k+1)): a pair boops after exactly v beeps, v = the least n with c^n > R^(n+1).
  A skipped pair beeps and boops nothing, so the gaps between boops are the values v of
  the pairs that pass (coprime, c > R), in order.

gcd(d, x) by lockstep holes (GCD(D, X)): D's hole (positions 1..d) and X's hole (positions
1..x) start on position 1; one round moves X's hole once around X and D's hole x times;
after round j, D's hole is on (j*x mod d) + 1.  Position 1 first (j*x = 0 mod d, j < d):
gcd > 1; position 2 first (j*x = 1 mod d): gcd = 1.

Numbers are in unary.  A block of v + 2 cells holds v; cells 1..v are the positions of a
hole (a single 0); cells 0 and v + 1 are guards.  Separators are '00'.  Tape:

    [P 00] K 00 D 00 A 00 B 00 C 00 M 00 R [00 Q]

  - K: c - d + 1 cells, no hole: a countdown for d.  d += 1 moves the K|D separator left.
  - D: the trial divisor d; its hole (at position 1 between tests) is GCD's counter.
  - A, B, C: a, b, c.  The block being tested has a marker (hole) on cell 1.
  - M: one cell (no other block has fewer than 3 cells).
  - R: rad so far; in the factor phase its hole is on cell 1 (GCD's cycled hole and the
    copy cursor of R := R*d).
  - P (power phase): c^k, grown to the left (mirrored multiplication, base C);
    Q (power phase): R^(k+1), grown to the right (base R).
"""
import sys
ST = {}          # name -> [t0, t1]
ORDER = []
BEEP = ('xe3', 0)
BOOP = ('xq6', 0)

def S(name, t0, t1):
    assert name not in ST, name
    ST[name] = [t0, t1]; ORDER.append(name)
def T(w, d, n): return (w, d, n)
def opp(d): return 'L' if d == 'R' else 'R'

def parser(prefix, found, d):
    """Move in direction d to the next hole (a single 0; '00' pairs are crossed).  Must
    start on a 1 or on the first 0 of a pair.  Lands on the cell past the hole (a 1) and
    performs `found` there."""
    S(prefix+'1', T(0,d,prefix+'2'), T(1,d,prefix+'1'))
    S(prefix+'2', T(0,d,prefix+'1'), found)
def parser_right(prefix, found): parser(prefix, found, 'R')
def parser_left(prefix, found): parser(prefix, found, 'L')

def adv(p, nonwrap, wrap, f='R'):
    """Advance the cyclic hole the head is on, one position in direction f.
    nonwrap = (dir, next): the new hole is written, the head moves dir;
    wrap = (dir, next): the hole was on the last position, it is written on the first."""
    b = opp(f)
    S(p+'1', T(1,f,p+'2'), None)
    S(p+'2', None, T(1,f,p+'3'))
    S(p+'3', T(0,b,p+'5'), T(1,b,p+'4'))         # 0: the hole was on the last position
    S(p+'4', None, (0,)+nonwrap)
    S(p+'5', T(0,f,p+'6'), T(1,b,p+'5'))
    S(p+'6', None, T(1,f,p+'7'))
    S(p+'7', None, (0,)+wrap)

def copy_loop(c, done, f='R'):
    """Copy Z (the block the head is in; its hole is the copy cursor) onto the far end of
    the scratch block after Z's '00' (direction f).  Entered at c1 inside Z right of the
    cursor (or on the separator).  When the cursor has passed Z's last position, the head
    walks back to Z's cell 0 and does `done`."""
    b = opp(f)
    S(c+'c1', T(0,f,c+'c2'), T(1,f,c+'c1'))
    S(c+'c2', T(0,f,c+'c3'), None)
    S(c+'c3', T(1,b,c+'c4'), T(1,f,c+'c3'))
    S(c+'c4', T(0,b,c+'c5'), T(1,b,c+'c4'))
    S(c+'c5', T(0,b,c+'c6'), None)
    S(c+'c6', T(1,f,c+'a2'), T(1,b,c+'c6'))
    S(c+'a2', None, T(1,f,c+'a3'))
    S(c+'a3', T(0,b,c+'d1'), T(1,b,c+'a4'))
    S(c+'a4', None, T(0,f,c+'c1'))
    S(c+'d1', T(0,f,c+'d2'), T(1,b,c+'d1'))
    S(c+'d2', None, done)

def multiply(p, f, after_merge):
    """Z := Z * base, one round.  Entered at p+'ba1' on the base hole (position 1, or the
    last position for f = 'L').  Each non-wrapping advance of the base hole appends a
    copy of Z after Z's separator; the wrap merges the copies into Z (fill the separator,
    erase two cells).  The base hole ends on its first position, Z's cursor on cell 1."""
    b = opp(f)
    adv(p+'ba', (f,p+'MC1'), (f,p+'MM1'), f)
    parser(p+'MC', T(1,f,p+'c1'), f)             # Z's cursor: copy
    copy_loop(p, T(1,f,p+'d3'), f)
    S(p+'d3', None, T(0,b,p+'NB1'))              # Z's cursor back to cell 1
    parser(p+'NB', T(1,f,p+'ba1'), b)            # back to the base hole
    parser(p+'MM', T(1,f,p+'mR'), f)             # Z's cursor: merge
    S(p+'mR', T(1,f,p+'m2'), T(1,f,p+'mR'))
    S(p+'m2', T(1,f,p+'m3'), None)
    S(p+'m3', T(0,b,p+'m4'), T(1,f,p+'m3'))
    S(p+'m4', None, T(0,b,p+'m5'))
    S(p+'m5', None, after_merge)

def gcd_routine():
    """GCD(D, X).  Entered at ca1 on D's hole (position 1), X's hole on its cell 1."""
    adv('ca', ('R','PC1'), ('R','PC1'))          # counter (D) advance
    parser_right('PC', T(1,'L','cy1'))           # to X's hole
    adv('cy', ('L','PN1'), ('L','PK1'))          # cycled (X) advance
    parser_left('PN', T(1,'R','ca1'))            # next tick
    parser_left('PK', T(1,'R','g1'))             # round done: check D
    S('g1', T(0,'L','g2'), None)
    S('g2', None, T(1,'L','g3'))
    S('g3', T(0,'R','H1'), T(1,'L','g4'))        # 0: D on position 1: gcd > 1
    S('g4', T(0,'R','E1'), T(1,'R','gS'))        # 0: D on position 2: gcd = 1
    S('gS', T(1,'R','ca2'), T(1,'R','gS'))       # otherwise: next round (as ca1)
    # gcd = 1: D's hole back to position 1, then to X's marker
    S('E1', None, T(1,'R','E2'))
    S('E2', None, T(0,'R','E3'))
    S('E3', T(1,'R','EX1'), None)
    parser_right('EX', T(1,'R','en1'))
    S('en1', T(0,'R','en2'), T(1,'R','en1'))     # to X's end
    S('en2', T(0,'R','en3'), None)
    S('en3', T(0,'L','enR1'), T(1,'R','en4'))    # 0: X is R (the last block)
    S('en4', T(0,'L','enC1'), T(0,'L','enF1'))   # 0: the next block is M: X is C
    parser_left('enF', T(1,'R','enF3'))          # X = A, B: marker moved on; fill X's
    S('enF3', T(1,'L','GD1'), None)
    parser_left('GD', T(1,'R','ca1'))            # to D's hole: next GCD
    parser_left('enC', T(1,'R','enC3'))          # X = C: no hit; fill C's marker
    S('enC3', T(1,'L','DH1'), None)
    parser_left('DH', T(1,'R','dp1'))            # to D's hole: d += 1
    S('enR1', T(0,'L','enR2'), None)             # X = R: gcd(d, R) = 1: R := R * d
    S('enR2', T(0,'L','ER1'), None)
    parser_left('ER', T(1,'L','EQ1'))            # past R's hole
    parser_left('EQ', T(1,'R','Rba1'))           # D's hole is the base
    # gcd > 1: to X's marker
    S('H1', None, T(1,'R','H2'))
    S('H2', T(0,'R','HX1'), None)
    parser_right('HX', T(1,'R','hn1'))
    S('hn1', T(0,'R','hn2'), T(1,'R','hn1'))
    S('hn2', T(0,'R','hn3'), None)
    S('hn3', T(0,'L','hR1'), T(1,'R','hn4'))     # 0: X is R: d is not new: d += 1
    S('hn4', T(0,'L','hC1'), T(1,'L','hF1'))     # 0: X is C: a hit
    parser_left('hF', T(1,'R','hF3'))            # X = A, B: fill the marker, check K
    S('hF3', T(1,'L','KC1'), None)
    parser_left('KC', T(1,'L','kc2'))
    S('kc2', T(0,'L','kc3'), None)
    S('kc3', T(0,'L','kc4'), None)
    S('kc4', None, T(1,'L','kc5'))
    S('kc5', T(0,'R','nc1'), T(1,'R','KR1'))     # 0: K has 1 cell (d = c): not coprime
    parser_right('KR', T(1,'L','ca1'))           # a hit: GCD(D, R)
    parser_left('hC', T(1,'R','hC3'))            # X = C: fill the marker: GCD(D, R)
    S('hC3', T(1,'L','GD1'), None)
    S('hR1', T(0,'L','hR2'), None)
    S('hR2', T(0,'L','HR1'), None)
    parser_left('HR', T(1,'L','DH1'))            # past R's hole, to D's

def next_d():
    """d += 1, entered at dp1 on D's hole (position 1).  If K has one cell (d = c), the
    factor phase is over: the pre-test."""
    S('dp1', T(1,'L','dp2'), None)
    S('dp2', None, T(1,'L','dp3'))
    S('dp3', T(0,'L','dp4'), None)
    S('dp4', T(0,'L','dp5'), None)
    S('dp5', None, T(1,'L','dp6'))
    S('dp6', T(0,'R','PT1'), T(1,'R','dp7'))     # 0: K has one cell: done
    S('dp7', None, T(0,'R','dp8'))               # K's last cell joins the separator
    S('dp8', T(0,'R','dp9'), None)
    S('dp9', T(1,'R','dp10'), None)              # the new guard
    S('dp10', None, T(0,'R','dpA'))              # the old guard: D's hole, position 1
    S('dpA', T(0,'R','dpB'), T(1,'R','dpA'))
    S('dpB', T(0,'R','dpC'), None)
    S('dpC', None, T(1,'R','dpD'))
    S('dpD', None, T(0,'L','GD1'))               # A's marker; to D's hole: GCD(D, A)

def pretest():
    """Compare C with R: C's cursor on its last position, R's hole (cell 1) is R's."""
    parser_right('PT', T(1,'L','pt1'))           # to R's hole
    S('pt1', T(0,'L','pt2'), None)
    S('pt2', None, T(1,'L','pt3'))
    S('pt3', T(0,'L','pt4'), None)
    S('pt4', T(0,'L','pt5'), None)
    S('pt5', None, T(1,'L','pt6'))               # M
    S('pt6', T(0,'L','pt7'), None)
    S('pt7', T(0,'L','pt8'), None)
    S('pt8', None, T(1,'L','pt9'))               # C's guard
    S('pt9', None, T(1,'L','x2'))                # C's last position: as if its cursor

def compare():
    """X (left) against Y (right): X's cursor moves left from X's last position, Y's
    right from Y's position 1, in turn.  Y runs out first iff x > y."""
    S('x1', T(1,'L','x2'), None)
    S('x2', None, T(1,'L','x3'))
    S('x3', T(0,'L','xe2'), T(1,'R','x4'))       # 0: X has run out: x <= y
    S('x4', None, T(0,'R','YP1'))
    parser_right('YP', T(1,'L','y1'))
    S('y1', T(1,'R','y2'), None)
    S('y2', None, T(1,'R','y3'))
    S('y3', T(0,'L','ye1'), T(1,'L','y4'))       # 0: Y has run out: x > y
    S('y4', None, T(0,'L','XP1'))
    parser_left('XP', T(1,'R','x1'))
    # x <= y: is X C (the pre-test) or P?
    S('xe2', T(0,'L','xe3'), None)
    S('xe3', T(0,'R','bp1'), T(1,'R','SK1'))     # 0: BEEP (P <= Q); 1: c <= R: skip
    # x > y: fill X's cursor, then C or P?
    S('ye1', None, T(1,'L','XQ1'))
    parser_left('XQ', T(1,'R','xq3'))
    S('xq3', T(1,'L','xq4'), None)
    S('xq4', T(0,'L','xq5'), T(1,'L','xq4'))
    S('xq5', T(0,'L','xq6'), None)
    S('xq6', T(0,'R','bo1'), T(1,'L','fl1'))     # 0: BOOP (P > Q); 1: c > R: powers
    # c <= R: fill R's cursor, to M: the pair is done
    parser_right('SK', T(1,'L','sk2'))
    S('sk2', T(1,'L','sk3'), None)
    S('sk3', T(0,'L','sk4'), T(1,'L','sk3'))
    S('sk4', T(0,'L','pe0'), None)

def power_init():
    """c > R: P := 1 at the left end, Q := 1 at the right end, then Q := Q * R."""
    S('fl1', T(0,'L','fl2'), T(1,'L','fl1'))
    S('fl2', T(0,'L','fl3'), T(1,'L','fl1'))
    S('fl3', T(1,'L','pw2'), T(1,'L','fl1'))     # the third 0: P = 101
    S('pw2', T(0,'L','pw3'), None)
    S('pw3', T(1,'R','pw4'), None)
    S('pw4', T(0,'R','fr1'), None)
    S('fr1', T(0,'R','fr2'), T(1,'R','fr1'))
    S('fr2', T(0,'R','fr3'), T(1,'R','fr1'))
    S('fr3', T(1,'R','qw2'), T(1,'R','fr1'))     # the third 0: Q = 101
    S('qw2', T(0,'R','qw3'), None)
    S('qw3', T(1,'L','qw4'), None)
    S('qw4', T(0,'L','qw5'), None)
    S('qw5', None, T(1,'L','qw6'))
    S('qw6', T(0,'L','qw7'), None)
    S('qw7', T(0,'L','qw8'), None)
    S('qw8', T(0,'R','qw9'), T(1,'L','qw8'))     # across R
    S('qw9', None, T(1,'R','qwA'))
    S('qwA', None, T(1,'R','Rba2'))              # R's base hole on cell 1, advanced

def right_mult():
    """Z := Z * base for Z = R (base D) and Z = Q (base R)."""
    multiply('R', 'R', T(0,'L','ZD1'))
    parser_left('ZD', T(1,'L','zd2'))            # to Z's cursor: Z's cell 0
    S('zd2', T(0,'L','zd3'), None)
    S('zd3', T(0,'L','zd4'), None)
    S('zd4', None, T(1,'L','zd5'))
    S('zd5', T(0,'L','zd6'), T(1,'L','RB1'))     # 0: Z's left neighbour is M: Z = R
    S('zd6', T(0,'L','DH1'), None)               # to D's hole: d += 1
    parser_left('RB', T(1,'R','rb3'))            # Z = Q: R's base hole
    S('rb3', T(1,'L','PX1'), None)
    parser_left('PX', T(1,'R','x1'))             # to P's cursor: compare P with Q

def beep_step():
    """After the BEEP: P's cursor on its last position, Q's back on cell 1, C's base hole
    on its last position, then P := P * c."""
    S('bp1', T(0,'R','bp2'), None)
    S('bp2', T(0,'R','bp3'), None)
    S('bp3', T(0,'L','bp4'), T(1,'R','bp3'))
    S('bp4', None, T(1,'L','bp5'))
    S('bp5', None, T(0,'R','QC1'))               # P's cursor
    parser_right('QC', T(1,'L','qc2'))           # Q's cursor
    S('qc2', T(1,'L','qc3'), None)
    S('qc3', T(0,'R','qc4'), T(1,'L','qc3'))
    S('qc4', None, T(1,'R','qc5'))
    S('qc5', None, T(0,'L','qc6'))               # Q's cursor on cell 1
    S('qc6', None, T(1,'L','qc7'))
    S('qc7', T(0,'L','qc8'), None)
    S('qc8', T(0,'L','qc9'), None)
    S('qc9', T(0,'L','qcA'), T(1,'L','qc9'))     # across R
    S('qcA', T(0,'L','qcB'), None)
    S('qcB', None, T(1,'L','qcC'))               # M
    S('qcC', T(0,'L','qcD'), None)
    S('qcD', T(0,'L','qcE'), None)
    S('qcE', None, T(1,'L','qcF'))               # C's guard
    S('qcF', None, T(1,'L','Lba2'))              # C's base hole, advanced

def left_mult():
    """P := P * c (mirrored), then Q := Q * R."""
    multiply('L', 'L', T(0,'R','LZ1'))
    parser_right('LZ', T(1,'R','LY1'))           # past P's cursor
    parser_right('LY', T(1,'L','ly1'))           # C's base hole
    S('ly1', T(1,'R','ly2'), None)
    S('ly2', None, T(1,'R','ly3'))
    S('ly3', T(0,'R','ly4'), None)
    S('ly4', T(0,'R','ly5'), None)
    S('ly5', None, T(1,'R','ly6'))               # M
    S('ly6', T(0,'R','ly7'), None)
    S('ly7', T(0,'R','ly8'), None)
    S('ly8', None, T(1,'R','ly9'))
    S('ly9', None, T(1,'R','Rba2'))              # R's base hole on cell 1, advanced

def pair_end():
    # not coprime (at kc5): fill D's hole, to M
    S('nc1', None, T(1,'R','nc2'))
    S('nc2', T(0,'R','nc3'), None)
    S('nc3', T(0,'R','nc4'), None)
    S('nc4', None, T(1,'R','nc5'))
    S('nc5', T(1,'R','MF1'), None)
    finder('MF', T(0,'L','pe0'))
    # BOOP: erase P, to M
    S('bo1', T(0,'R','bo2'), None)
    S('bo2', T(0,'R','bo3'), None)
    S('bo3', T(0,'R','bo4'), T(0,'R','bo3'))
    S('bo4', T(0,'R','bo5'), None)
    S('bo5', None, T(1,'R','bo6'))               # K (one cell)
    S('bo6', T(0,'R','bo7'), None)
    S('bo7', T(0,'R','bo8'), None)
    S('bo8', None, T(1,'R','MF1'))
    # at M: erase R and Q
    S('pe0', None, T(1,'R','pe1'))
    S('pe1', T(0,'R','pe2'), T(0,'R','pe1'))
    S('pe2', T(0,'R','pe3'), T(0,'R','pe1'))
    S('pe3', T(0,'L','pe4'), T(0,'R','pe1'))
    S('pe4', T(0,'L','pe4'), T(1,'L','eb1'))     # back to M
    # next pair: b = 1?
    S('eb1', T(0,'L','eb2'), None)
    S('eb2', T(0,'L','eb3'), None)
    S('eb3', T(0,'L','eb4'), T(1,'L','eb3'))     # across C
    S('eb4', T(0,'L','eb5'), None)
    S('eb5', None, T(1,'L','eb6'))
    S('eb6', None, T(1,'L','eb7'))
    S('eb7', None, T(1,'L','eb8'))
    S('eb8', T(0,'L','cab'), T(1,'L','ea1'))     # 0: B has 3 cells: b = 1: c += 1
    # a += 1, b -= 1: the A|B separator one cell right
    S('ea1', T(0,'L','ea2'), T(1,'L','ea1'))
    S('ea2', T(1,'R','ea3'), None)
    S('ea3', T(0,'R','ea4'), None)
    S('ea4', None, T(0,'R','MW1'))
    finder('MW', T(0,'R','wr1'))
    # c += 1: A := 1 (the A|B separator left until A has 3 cells) ...
    S('cab', T(0,'L','cac'), None)
    S('cac', None, T(1,'L','cad'))
    S('cad', None, T(1,'L','cae'))
    S('cae', None, T(1,'L','caf'))
    S('caf', T(0,'L','fk2'), T(1,'R','cag'))     # 0: A has 3 cells
    S('cag', None, T(1,'R','cah'))
    S('cah', None, T(1,'R','cai'))
    S('cai', None, T(0,'R','caj'))
    S('caj', T(0,'R','cak'), None)
    S('cak', T(1,'L','cab2'), None)
    S('cab2', T(0,'L','cab'), None)
    # ... K += 1 at the left end ...
    S('fk1', T(0,'L','fk2'), T(1,'L','fk1'))
    S('fk2', T(0,'L','fk3'), T(1,'L','fk1'))
    S('fk3', T(0,'R','fk4'), T(1,'L','fk1'))
    S('fk4', T(0,'R','fk5'), None)
    S('fk5', T(1,'R','MK1'), None)
    # ... C += 2 at its right end, M two cells right, then the B|C separator one right
    finder('MK', T(0,'R','cm1'))
    S('cm1', T(1,'L','cm2'), None)               # the new M
    S('cm2', T(0,'L','cm3'), None)
    S('cm3', None, T(0,'L','cm4'))
    S('cm4', T(1,'L','cm5'), None)
    S('cm5', T(1,'L','cm6'), None)
    S('cm6', T(0,'L','cm7'), T(1,'L','cm6'))     # across C
    S('cm7', T(1,'R','cm8'), None)
    S('cm8', T(0,'R','cm9'), None)
    S('cm9', None, T(0,'R','MW1'))
    # R := 1 after M, then to the left end
    S('wr0', T(0,'R','wr1'), None)
    S('wr1', T(0,'R','wr2'), None)
    S('wr2', T(1,'R','wr3'), None)
    S('wr3', T(0,'R','wr4'), None)
    S('wr4', T(1,'L','fla'), None)
    S('fla', T(0,'L','flb'), T(1,'L','fla'))
    S('flb', T(0,'L','flc'), T(1,'L','fla'))
    S('flc', T(0,'R','fld'), T(1,'L','fla'))
    S('fld', T(0,'R','fle'), None)
    S('fle', T(0,'R','dr1'), None)
    # d := 2: the K|D separator right until D has 4 cells
    S('dr1', T(0,'R','dr2'), T(1,'R','dr1'))
    S('dr2', T(0,'R','dr3'), None)
    S('dr3', None, T(1,'R','dr4'))
    S('dr4', None, T(1,'R','dr5'))
    S('dr5', None, T(1,'R','dr6'))
    S('dr6', None, T(1,'R','dr7'))
    S('dr7', T(0,'L','dq1'), T(1,'L','drL'))     # 0: d = 2
    S('drL', T(0,'L','drM'), T(1,'L','drL'))
    S('drM', T(1,'R','drD'), None)
    S('drD', T(0,'R','drE'), None)
    S('drE', None, T(0,'R','dr3'))
    S('dq1', None, T(1,'L','dq2'))
    S('dq2', None, T(1,'L','dq3'))
    S('dq3', None, T(0,'R','dpA'))               # D's hole; A's marker; GCD(D, A)

def finder(p, found):
    """Move right to the first one-cell block (M); perform `found` on the 0 after it."""
    S(p+'1', T(0,'R',p+'2'), T(1,'R',p+'1'))
    S(p+'2', T(0,'R',p+'3'), T(1,'R',p+'1'))
    S(p+'3', None, T(1,'R',p+'4'))
    S(p+'4', found, T(1,'R',p+'1'))

def seed():
    # K = 1, D = 2, A = B = 1, C = 2, M; then R := 1 (wr0) and the pair (1, 1)
    pat = '1' + '00' + '1111' + '00' + '111' + '00' + '111' + '00' + '1111' + '00' + '1'
    for i, ch in enumerate(pat):
        nxt = f'seed{i+1}' if i + 1 < len(pat) else 'wr0'
        S(f'seed{i}', T(int(ch), 'R', nxt), None)

def build(variant=None):
    """variant='halt': the BOOP halts instead (test: halts at the first boop, (1, 8, 9))."""
    ST.clear(); ORDER.clear()
    seed(); gcd_routine(); next_d(); pretest(); compare(); power_init(); right_mult()
    beep_step(); left_mult(); pair_end()
    if variant == 'halt':
        ST['xq6'][0] = T(0, 'R', 'halt')
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {'halt'}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]} - ({'bo1'} if variant == 'halt' else set())
    assert not unused, unused
    lines = ['; Beeping Booping machine for the abc conjecture: BEEP = xe3 reading 0,',
             '; BOOP = xq6 reading 0.  Some beep count between consecutive boops repeats',
             '; infinitely often iff abc fails (c^n > rad(abc)^(n+1) for infinitely many',
             '; coprime a + b = c, for some n >= 1).',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            mark = '   ; BEEP' if (n, r) == BEEP else '   ; BOOP' if (n, r) == BOOP else ''
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}{mark}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'abc.txt', 'w').write(out)
    print(len(ORDER), 'states')
