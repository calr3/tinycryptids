"""Generator for a 2-symbol Turing machine that halts iff the Feit-Thompson conjecture
fails: iff there are distinct primes p, q with rep p q | rep q p, where
rep b n = 1 + b + ... + b^(n-1) = (b^n - 1)/(b - 1).

For p < q, rep p q > rep q p > 0, so a counterexample has p > q.  The machine tests the
candidates m = 3, 4, 5, ...; for each prime m it tests rep m p | rep p m for every prime
p < m.

Numbers are in unary.  A block of v + 2 cells holds v; its cells 1..v are the positions
of a cyclic hole (a single 0).  Advancing the hole moves it one cell right, from the last
position back to cell 1 (a "wrap").  Tape (blocks separated by '00'):

    L 00 P0 00 P1 00 ... 00 Pk 00 M [00 work]

  - L and M hold the candidate m, each with a permanent cyclic hole (at cell 1 at rest).
  - P0 = 111 holds 1; P1 < ... < Pk are the primes < m.  These blocks have no hole
    except the marker (a hole at cell 1) of the block being visited.
Trial pass (left to right, the marker on P1, ..., Pk): Pi | m is tested by the cycle
CYC(counter Pi, cycled L): L's hole goes round once (m advances), Pi's hole advances once
before each; then Pi's hole is back at cell 1 iff Pi | m.
  - Pi | m: m is composite: M += 1 (on the right), L += 1 (on the left), marker on P1.
  - else the marker moves to the next block; if that is M (its cell 1 is a hole), m is
    prime: the pair pass starts.
Pair pass (right to left, the marker on Pk, ..., P1, P0).  For p = Pi > 0, at the right
end:
  - H1 (Horner): A = rep p m, pushed right of M;
  - H2: B = rep m p, pushed right of A;
  - CYC(counter B, cycled A): B | A: HALT.  Else A and B are erased, the marker moves
    one block left.
Horner pushes R = 101 (holds 1) and finds its three holes from the right: a skipped
one, the base, the exponent; with the exponent's hole e - 1 rounds R := R * b + 1
(b - 1 copies of R appended after '00', then the separator filled and one cell erased).
For H1 these are M (skipped), Pi (base), L (exponent); for H2: A, M, Pi.
For P0 (the end of the pair pass), H1 makes rep 1 m = m: this block becomes the next M,
the old M joins the list as P(k+1), and as for a composite M += 1, L += 1.
The seed writes the tape of m = 2 (no primes, the marker on P0) and starts its pair
pass: its P0 step gives m = 3 with the list 2.
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

def walk_end(prefix, found):
    """Move right to the first run of three 0s; perform `found` on its third 0."""
    S(prefix+'1', T(0,'R',prefix+'2'), T(1,'R',prefix+'1'))
    S(prefix+'2', T(0,'R',prefix+'3'), T(1,'R',prefix+'1'))
    S(prefix+'3', found, T(1,'R',prefix+'1'))

def adv(p, nonwrap, wrap):
    """Advance the cyclic hole the head is on.  nonwrap = (dir, next): the new hole is
    written and the head moves dir; wrap = (dir, next): the hole was at the last position,
    it is written at cell 1 and the head moves dir."""
    S(p+'1', T(1,'R',p+'2'), None)
    S(p+'2', None, T(1,'R',p+'3'))
    S(p+'3', T(0,'L',p+'5'), T(1,'L',p+'4'))     # 0: the hole was at the last position
    S(p+'4', None, (0,)+nonwrap)
    S(p+'5', T(0,'R',p+'6'), T(1,'L',p+'5'))
    S(p+'6', None, T(1,'R',p+'7'))
    S(p+'7', None, (0,)+wrap)

def seed(variant):
    # m = 2: L 00 P0 00 M with the marker on P0 (the pair pass of m = 2: only P0)
    pat = '1011' + '00' + '101' + '00' + '1011'
    for i, ch in enumerate(pat):
        last = i + 1 == len(pat)
        S(f'seed{i}', T(int(ch), 'R', 'pw1' if last else f'seed{i+1}'), None)

def cyc(halt_state):
    """CYC(counter, cycled): the counter is right of the cycled block."""
    adv('ca', ('L','PC1'), ('L','PC1'))          # counter
    parser_left('PC', T(1,'R','cy1'))
    adv('cy', ('R','PN1'), ('R','PK1'))           # cycled
    parser_right('PN', T(1,'L','ca1'))
    parser_right('PK', T(1,'L','k1'))
    # is the counter's hole at cell 1?  (fill it on the way)
    S('k1', T(1,'L','k2'), None)
    S('k2', None, T(1,'L','k3'))
    S('k3', T(0,'R','kd3'), T(1,'R','kn3'))       # 0: at cell 1: the counter divides
    # divides: a block right of the counter: trial, m composite; else HALT
    S('kd3', T(0,'R','kd4'), T(1,'R','kd3'))
    S('kd4', T(0,'R','kd5'), None)
    S('kd5', T(0,'R',halt_state), T(1,'R','PM1'))
    # does not divide: a block right of the counter: trial, the marker moves there;
    # else the test: clean up
    S('kn3', T(0,'R','kn4'), T(1,'R','kn3'))
    S('kn4', T(0,'R','kn5'), None)
    S('kn5', T(0,'L','cl1'), T(1,'R','kn6'))
    S('kn6', T(0,'L','rt1'), T(1,'R','ca2'))      # 0: the next block is M: m is prime

def next_candidate():
    """M += 1 (M is the last block), L += 1, marker on P1, trial pass."""
    parser_right('PM', T(1,'R','ms'))             # to M's hole
    S('ms', T(1,'L','PX1'), T(1,'R','ms'))        # M += 1
    parser_left('PX', T(1,'L','PY1'))             # past M's hole
    parser_left('PY', T(1,'R','lp1'))             # to L's hole
    S('lp1', T(1,'L','lp2'), None)                # L grows on its left, hole at cell 1
    S('lp2', None, T(0,'L','lp3'))
    S('lp3', T(1,'R','lp4'), None)
    S('lp4', T(0,'R','u1'), None)
    S('u1', T(0,'R','u2'), T(1,'R','u1'))
    S('u2', T(0,'R','kn3'), None)                 # across P0 to P1's cell 1 (as kn3..kn6)

def pairs():
    # RETREAT: from a block's cell 0 or 1 going left, to the previous block's cell 1
    S('rt1', T(0,'L','rt2'), T(1,'L','rt1'))
    S('rt2', T(0,'L','rt3'), None)
    S('rt3', T(0,'R','rt4'), T(1,'L','rt3'))
    S('rt4', None, T(1,'R','rt5'))
    S('rt5', None, T(0,'R','pw1'))                # the marker
    # PAIR / Horner entry: push R = 101 at the right end
    walk_end('pw', T(1,'R','pp2'))
    S('pp2', T(0,'R','pp3'), None)
    S('pp3', T(1,'L','HE1'), None)
    # Horner: from R's cursor going left: skipped hole, base, exponent
    parser_left('HE', T(1,'L','HF1'))
    parser_left('HF', T(1,'L','HG1'))
    parser_left('HG', T(1,'L','HH1'))
    parser_left('HH', T(1,'R','ea1'))
    adv('ea', ('R','MB1'), ('R','hd1'))           # exponent
    parser_right('MB', T(1,'L','ba1'))
    adv('ba', ('R','MC1'), ('R','MM1'))           # base
    parser_right('MC', T(1,'R','MD1'))
    parser_right('MD', T(1,'R','c1'))             # R's cursor: copy
    parser_right('MM', T(1,'R','MN1'))
    parser_right('MN', T(1,'R','mR'))             # R's cursor: merge
    # copy R (cursor = R's hole) onto the end of Q
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
    parser_left('NB', T(1,'L','NC1'))
    parser_left('NC', T(1,'R','ba1'))             # back to the base
    # merge: R 00 Q -> R + 1 + Q
    S('mR', T(1,'R','m2'), T(1,'R','mR'))
    S('m2', T(1,'R','m3'), None)
    S('m3', T(0,'L','m4'), T(1,'R','m3'))
    S('m4', None, T(0,'L','HE1'))
    # Horner done (exponent at cell 1): which block follows the exponent?
    S('hd1', T(0,'R','hd2'), T(1,'R','hd1'))
    S('hd2', T(0,'R','hd3'), None)
    S('hd3', None, T(1,'R','hd4'))
    S('hd4', T(0,'R','hz5'), T(1,'R','hn5'))
    S('hn5', None, T(1,'R','hn6'))
    S('hz5', None, T(1,'R','hz6'))
    S('hn6', T(0,'R','pw2'), T(1,'R','tw1'))      # 0: P0 (exponent L): H1 done, H2
    S('hz6', T(0,'L','pz1'), T(1,'R','tw1'))      # 0: P0 marked: H1 for P0 done
    # H2 done: CYC(B, A)
    walk_end('tw', T(0,'L','t1'))
    S('t1', T(0,'L','t1'), T(1,'L','t2'))         # left over the two 0s, onto B
    S('t2', T(1,'R','ca2'), T(1,'L','t2'))        # to B's hole: advance it (as ca1)
    # test failed: erase B and A, back to the marker, RETREAT
    S('cl1', T(0,'L','cl1'), T(0,'L','cl3'))
    S('cl3', T(0,'L','cl4'), T(0,'L','cl3'))      # B
    S('cl4', T(0,'L','cl5'), None)
    S('cl5', T(0,'L','cl6'), T(0,'L','cl5'))      # A (its cursor at cell 1)
    S('cl6', None, T(0,'L','cl7'))
    S('cl7', T(0,'L','cl7'), T(1,'L','RA1'))
    parser_left('RA', T(1,'L','RB1'))             # past M's hole
    parser_left('RB', T(1,'R','rf'))              # the marker
    S('rf', T(1,'L','rt1'), None)
    # P0 done: the new block is the next M; fill P0's and the old M's holes
    S('pz1', None, T(1,'L','pz2'))
    S('pz2', T(1,'R','PO1'), None)
    parser_right('PO', T(1,'L','pz3'))
    S('pz3', T(1,'R','PM1'), None)

def build(halt_state='halt', variant=0):
    """variant 1: the test checks B | A - 1 (the first counter advance is skipped):
    halts at the pair (2, 5)."""
    ST.clear(); ORDER.clear()
    seed(variant); cyc(halt_state); next_candidate(); pairs()
    if variant == 1:
        ST['t2'][0] = T(0,'L','PC1')
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    what = ('the Feit-Thompson conjecture is false' if variant == 0 else
            'some primes p < m have rep m p | rep p m - 1 (test variant)')
    lines = [f'; Halts iff {what}.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'feitthompson.txt', 'w').write(out)
    print(len(ORDER), 'states')
