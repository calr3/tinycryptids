"""Generator for a 2-symbol Turing machine that halts iff Firoozbakht's conjecture fails:
iff there are consecutive primes p < q with p^(n+1) <= q^n, where n = pi(p) (p is the
n-th prime).

The machine tests the candidates m = 3, 4, 5, ...; for each prime m = q it compares
B = p^(n+1) with A = q^n, where p is the previous prime.

Numbers are in unary.  A block of v + 2 cells holds v; its cells 1..v are the positions
of a cyclic hole (a single 0).  Tape (blocks separated by '00'):

    N 00 P1 00 P2 00 ... 00 Pk 00 M [00 work]

  - N holds k + 2 (k = the number of primes < m); its hole is at cell 1 at rest.
  - P1 < ... < Pk are the primes < m.  These blocks have no hole except the marker
    (a hole at cell 1) of the block being visited.
  - M holds the candidate m, with a cyclic hole (at cell 1 at rest).
Trial pass (left to right, the marker on P1, ..., Pk): Pi | m is tested by the cycle
CYC(counter Pi, cycled M): M's hole goes round once (m advances), Pi's hole advances once
before each; then Pi's hole is back at cell 1 iff Pi | m.
  - Pi | m: m is composite: M += 1, back to N, the trial pass of m + 1.
  - else the marker moves to the next block; if that is M (its cell 1 is a hole), m is
    prime.
Prime m = q (p = Pk, n = k):
  - the marker goes back to Pk; M is copied to a new block M' right of it (M' holds q,
    hole at cell 1) and M joins the list (its hole is filled): P(k+1) = q.
  - Horner run H_B: R = 101 (holds 1) is pushed at the right end; its holes going left:
    a skipped one (M'), the base (Pk's marker), the exponent (N).  Each advance of the
    exponent hole is a round R := R * base (base - 1 copies of R appended after '00',
    then the separator filled and two cells erased).  N's hole starts at cell 1: k + 1
    rounds, B = p^(k+1).
  - which run ended: the first hole right of N is followed by a block whose cell 1 is a
    1 (P(k+1): after H_B) or a hole (B: after H_A).
  - after H_B: Pk's marker is filled; N grows by a cell on its left and its hole moves to
    (new) cell 3; H_A: skipped B, base M', exponent N: k rounds, A = q^k.
  - after H_A (N is back at rest, holding k + 3): compare by erasing a cell of B, then
    one of A, in turn: B empty first: HALT (B <= A); A empty first: erase B and A,
    M' += 1 (it is the next M), the trial pass of q + 1.
The seed writes N = 3, P1 = 2, M = 2 and enters "M += 1": the trial pass of m = 3.
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

def copy_loop(c, done):
    """Copy the block left of the head (cursor = its hole) onto the end of the block
    after the '00'.  Entered at c1 on the separator's first cell.  When the cursor has
    passed the last cell, the head walks back to the block's cell 0 and does `done`."""
    S(c+'c1', T(0,'R',c+'c2'), T(1,'R',c+'c1'))
    S(c+'c2', T(0,'R',c+'c3'), None)
    S(c+'c3', T(1,'L',c+'c4'), T(1,'R',c+'c3'))
    S(c+'c4', T(0,'L',c+'c5'), T(1,'L',c+'c4'))
    S(c+'c5', T(0,'L',c+'c6'), None)
    S(c+'c6', T(1,'R',c+'a2'), T(1,'L',c+'c6'))
    S(c+'a2', None, T(1,'R',c+'a3'))
    S(c+'a3', T(0,'L',c+'d1'), T(1,'L',c+'a4'))
    S(c+'a4', None, T(0,'R',c+'c1'))
    S(c+'d1', T(0,'R',c+'d2'), T(1,'L',c+'d1'))
    S(c+'d2', None, done)

def seed(variant):
    # N = 3, P1 = 2, M = 2 (hole at cell 1); then ms makes M = 3
    nN = 3 + (1 if variant == 1 else 0)
    pat = '10' + '1' * nN + '00' + '1111' + '00' + '1011'
    for i, ch in enumerate(pat):
        last = i + 1 == len(pat)
        S(f'seed{i}', T(int(ch), 'R', 'ms' if last else f'seed{i+1}'), None)

def trial():
    """CYC(counter, cycled): the counter Pi is left of the cycled block M."""
    adv('ca', ('R','PC1'), ('R','PC1'))          # counter
    parser_right('PC', T(1,'L','cy1'))
    adv('cy', ('L','PN1'), ('L','PK1'))           # cycled
    parser_left('PN', T(1,'R','ca1'))
    parser_left('PK', T(1,'R','k1'))
    # is the counter's hole at cell 1?  (fill it on the way)
    S('k1', T(1,'L','k2'), None)
    S('k2', None, T(1,'L','k3'))
    S('k3', T(0,'R','PM1'), T(1,'R','kn3'))       # 0: at cell 1: the counter divides m
    # does not divide: the marker moves to the next block; if that is M, m is prime
    S('kn3', T(0,'R','kn4'), T(1,'R','kn3'))
    S('kn4', T(0,'R','kn5'), None)
    S('kn5', None, T(1,'R','kn6'))
    S('kn6', T(0,'L','rt1'), T(1,'R','ca2'))      # 0: the next block is M: m is prime

def next_candidate():
    """M += 1 (M is the last block), back to N, marker on P1, trial pass."""
    parser_right('PM', T(1,'R','ms'))             # to M's hole
    S('ms', T(1,'L','PX1'), T(1,'R','ms'))        # M += 1
    parser_left('PX', T(1,'L','PY1'))             # past M's hole
    parser_left('PY', T(1,'R','v1'))              # to N's hole
    S('v1', T(0,'R','kn3'), None)                 # across N to P1's cell 1 (as kn3..kn6)

def prime():
    # RETREAT: from M's cell 1 going left, to Pk's cell 1: the marker
    S('rt1', T(0,'L','rt2'), T(1,'L','rt1'))
    S('rt2', T(0,'L','rt3'), None)
    S('rt3', T(0,'R','rt4'), T(1,'L','rt3'))
    S('rt4', None, T(1,'R','rt5'))
    S('rt5', None, T(0,'R','cw1'))
    # copy M onto a new block M' = 11 + copy (then a hole at its cell 1)
    walk_end('cw', T(1,'R','s2'))
    S('s2', T(1,'L','sY'), None)
    S('sY', T(0,'L','Cc1'), T(1,'L','sY'))
    copy_loop('C', T(1,'R','cn3'))                # M's cursor stays filled: M joins the list
    S('cn3', T(0,'R','cn4'), T(1,'R','cn3'))
    S('cn4', T(0,'R','cn5'), None)
    S('cn5', None, T(1,'R','cn6'))
    S('cn6', None, T(0,'R','pw1'))                # M' 's hole
    # push R = 101 at the right end
    walk_end('pw', T(1,'R','pp2'))
    S('pp2', T(0,'R','pp3'), None)
    S('pp3', T(1,'L','HE1'), None)

def horner():
    """From R's cursor going left: skipped hole, base, exponent; with the exponent's hole
    one round R := R * base per non-wrapping advance."""
    parser_left('HE', T(1,'L','HF1'))
    parser_left('HF', T(1,'L','HG1'))
    parser_left('HG', T(1,'L','HH1'))
    parser_left('HH', T(1,'R','ea1'))
    adv('ea', ('R','MB1'), ('R','PD1'))           # exponent
    parser_right('MB', T(1,'L','ba1'))
    adv('ba', ('R','MC1'), ('R','MM1'))           # base
    parser_right('MC', T(1,'R','MD1'))
    parser_right('MD', T(1,'R','c1'))             # R's cursor: copy
    parser_right('MM', T(1,'R','MN1'))
    parser_right('MN', T(1,'R','mR'))             # R's cursor: merge
    copy_loop('', T(1,'R','d3'))                  # copy R onto the end of Q
    S('d3', None, T(0,'L','NB1'))                 # reset R's cursor to cell 1
    parser_left('NB', T(1,'L','NC1'))
    parser_left('NC', T(1,'R','ba1'))             # back to the base
    # merge: R 00 Q -> R + Q
    S('mR', T(1,'R','m2'), T(1,'R','mR'))
    S('m2', T(1,'R','m3'), None)
    S('m3', T(0,'L','m4'), T(1,'R','m3'))
    S('m4', None, T(0,'L','m5'))
    S('m5', None, T(0,'L','HE1'))

def after(halt_state):
    # which run ended?  the block after the first hole right of N: P(k+1) or B
    parser_right('PD', T(1,'R','dk1'))
    S('dk1', T(0,'R','dk2'), T(1,'R','dk1'))
    S('dk2', T(0,'R','dk3'), None)
    S('dk3', None, T(1,'R','dk4'))
    S('dk4', T(0,'R','z0'), T(1,'L','QA1'))       # 0: B's cursor: H_A done: compare
    # H_B done: fill Pk's marker, N grows on its left, its hole to (new) cell 3, push
    parser_left('QA', T(1,'R','qf'))
    S('qf', T(1,'L','QB1'), None)
    parser_left('QB', T(1,'L','n1'))
    S('n1', T(1,'R','n2'), None)
    S('n2', None, T(1,'R','n3'))
    S('n3', T(1,'R','n4'), None)
    S('n4', None, T(0,'R','pw1'))
    # compare: erase the last cell of B, then of A, ...
    S('z0', T(0,'L','z11'), T(1,'R','z0'))        # to B's last cell
    S('z11', T(0,'L','z11'), T(0,'L','z2'))       # (left over 0s) erase B's last cell
    S('z2', T(0,'R',halt_state), T(1,'R','z3'))   # 0: B is used up: B <= A
    S('z3', T(0,'R','z3'), T(1,'R','z4'))         # right over 0s to A
    S('z4', T(0,'R','z5'), T(1,'R','z4'))
    S('z5', T(0,'L','z6'), T(1,'R','z4'))         # 00: past A's end
    S('z6', T(0,'L','z7'), None)
    S('z7', None, T(0,'L','z8'))                  # erase A's last cell
    S('z8', T(0,'L','e1'), T(1,'L','z9'))         # 0: A is used up: B > A
    S('z9', T(0,'L','z10'), T(1,'L','z9'))        # left across A
    S('z10', T(0,'L','z11'), T(1,'L','z9'))
    # B > A: erase the rest of A and B; M' += 1 (fill the separator's first cell)
    S('e1', None, T(0,'L','e2'))
    S('e2', T(0,'L','e2'), T(0,'L','e3'))
    S('e3', T(0,'L','e4'), T(0,'L','e3'))
    S('e4', None, T(0,'L','e5'))
    S('e5', T(0,'L','ms'), None)

def build(halt_state='halt', variant=0):
    """variant 1: N starts one larger (both exponents one larger): the test is
    p^(n+2) <= q^(n+1), which holds for (2, 3)."""
    ST.clear(); ORDER.clear()
    seed(variant); trial(); next_candidate(); prime(); horner(); after(halt_state)
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    what = ("Firoozbakht's conjecture is false" if variant == 0 else
            'some consecutive primes p < q have p^(n+2) <= q^(n+1) (test variant)')
    lines = [f'; Halts iff {what}.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'firoozbakht.txt', 'w').write(out)
    print(len(ORDER), 'states')
