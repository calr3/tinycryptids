"""Generator for a 2-symbol Turing machine that halts iff Gilbreath's conjecture fails:
iff for some k >= 1 the first entry of row k of the triangle of absolute differences
of 2, 3, 5, 7, ... is not 1.

The machine keeps the last diagonal of the triangle on the primes found so far,
D = [D0, D1, ..., D(n-1)] with D0 the last prime p.  A new prime m gives the new
diagonal [m, |m - D0|, ||m - D0| - D1|, ...]; its last entry is the first entry of
the new bottom row.  D0 itself is not stored: with g = m - p, the stored list
S = [D1, ..., D(n-1)] becomes ext S g = [g, |g - D1|, ...] and the check is on its
last entry.

Numbers are in unary.  Tape (blocks of 1s; '00', '000' separators; a hole is one 0):
    G 00 M 00 S(n-1) 000 ... 000 S1 000 [zeros] 00 D 00 R
  - G = H(g): 1 0 1^(g+1), the gap m - p, with a hole at cell 1.
  - M: one cell, marks the start of the stored list.  P(v) = 1^(v+2) is a stored value.
  - D 00 R: the trial division of the candidate m = d + r, as in ../legendre:
    D (d + 2 cells, hole at cell c + 1), R (r + 2 cells, with a hole during the walk).
A composite m: G += 1 (its hole moves one cell left, a cell is added on its left).
A prime m: the list is rebuilt as a queue: values are taken from its right end (B)
and the new values are made at the left end.  L is the newest value (first G), with a
cursor hole; Z is made left of it as H(0).  One step, Z := |L - B|:
    the cursor of L advances x = L times; each time B -= 1, or Z += 1 if B = 0;
    then while B > 0: B -= 1, Z += 1; then B is erased and L loses its hole (P(x)).
    Z is the next L.  When the next block on the right is M, the update is over:
    M is erased, Z must be H(1) (else HALT), Z becomes P(1) (losing its hole and
    its last cell, like every L), and a new M and G = H(1) are written on its left.
Then D := 2, R := m - 1 for the next candidate.
The seed writes the tape after the primes 2, 3 (S = [1], g = 1), with the D/R
region of m = 3 in the middle of the rebuild for m = 4.
"""
import sys
ST = {}
ORDER = []
def S(name, t0, t1):
    assert name not in ST, name
    ST[name] = [t0, t1]; ORDER.append(name)
def T(w, d, n): return (w, d, n)

def hole_left(prefix, found):
    """Move left to the next hole (a single 0), crossing runs of >= 2 zeros.
    Lands on the cell left of the hole (a 1) and performs `found` there."""
    S(prefix + 'P', T(0, 'L', prefix + 'Z1'), T(1, 'L', prefix + 'P'))
    S(prefix + 'Z1', T(0, 'L', prefix + 'Z2'), found)
    S(prefix + 'Z2', T(0, 'L', prefix + 'Z2'), T(1, 'L', prefix + 'P'))

def hole_right(prefix, found):
    """Move right to the next hole, crossing runs of >= 2 zeros. Lands on the
    cell right of the hole (a 1) and performs `found` there."""
    S(prefix + 'P', T(0, 'R', prefix + 'Z1'), T(1, 'R', prefix + 'P'))
    S(prefix + 'Z1', T(0, 'R', prefix + 'Z2'), found)
    S(prefix + 'Z2', T(0, 'R', prefix + 'Z2'), T(1, 'R', prefix + 'P'))

def parser_right(prefix, found):
    """(../legendre) Move right to the next hole across '00' separators. Lands at
    hole+1 (a 1) and performs `found` there."""
    S(prefix + '1', T(0, 'R', prefix + '2'), T(1, 'R', prefix + '1'))
    S(prefix + '2', T(0, 'R', prefix + '1'), found)

def parser_left(prefix, found):
    S(prefix + '1', T(0, 'L', prefix + '2'), T(1, 'L', prefix + '1'))
    S(prefix + '2', T(0, 'L', prefix + '1'), found)

def walk_right(prefix, found):
    """Move right across holes and separators of 2 or 3 zeros until a run of 4
    zeros; then back left to the last 1 before it, and perform `found` there."""
    S(prefix + '1', T(0, 'R', prefix + '2'), T(1, 'R', prefix + '1'))
    S(prefix + '2', T(0, 'R', prefix + '3'), T(1, 'R', prefix + '1'))
    S(prefix + '3', T(0, 'R', prefix + '4'), T(1, 'R', prefix + '1'))
    S(prefix + '4', T(0, 'L', prefix + 'z'), T(1, 'R', prefix + '1'))
    S(prefix + 'z', T(0, 'L', prefix + 'z'), found)

SEED_S = [1]      # stored list S1, ..., S(n-1) (on the tape S(n-1) is leftmost)
SEED_G = 1
SEED_M = 3        # the D/R region holds m = 3 (rebuilt for m = 4 by the seed's exit)
def seed_cells():
    out = '10' + '1' * (SEED_G + 1) + '00' + '1'
    for i, v in enumerate(reversed(SEED_S)):
        out += ('00' if i == 0 else '000') + '1' * (v + 2)
    out += '00000'
    # D (d = SEED_M, hole at 1), the separator filled, R (r = 0): as c3 sees it
    out += '10' + '1' * SEED_M + '11' + '11'
    return out

def seed():
    pat = seed_cells()
    for i, ch in enumerate(pat):
        last = i + 1 == len(pat)
        S(f'seed{i}', T(int(ch), 'R', 'c3' if last else f'seed{i+1}'), None)

def trial():
    """../legendre: the mod walk, the shift d += 1, r -= 1, and the rebuild."""
    S('ma1', T(1, 'R', 'ma2'), None)
    S('ma2', None, T(1, 'R', 'ma3'))
    S('ma3', T(0, 'L', 'maw1'), T(1, 'L', 'ma4'))     # 0: the hole was at the last cell
    S('ma4', None, T(0, 'R', 'PR1'))
    S('maw1', T(0, 'R', 'maw2'), T(1, 'L', 'maw1'))
    S('maw2', None, T(1, 'R', 'maw3'))
    S('maw3', None, T(0, 'R', 'PR1'))
    parser_right('PR', T(1, 'L', 'ra1'))
    S('ra1', T(1, 'R', 'ra2'), None)
    S('ra2', None, T(1, 'R', 'ra3'))
    S('ra3', T(0, 'L', 'PK1'), T(1, 'L', 'ra4'))      # 0: R exhausted (hole gone)
    S('ra4', None, T(0, 'L', 'PM1'))
    parser_left('PM', T(1, 'R', 'ma1'))
    parser_left('PK', T(1, 'L', 'k1'))
    S('k1', T(0, 'L', 'gZ1'), T(1, 'R', 'k2'))        # 0: d | m: composite
    S('k2', None, T(1, 'R', 'k3'))
    S('k3', T(1, 'L', 'rs1'), None)                   # fill hole, reset it to cell 1
    S('rs1', T(0, 'R', 'rs2'), T(1, 'L', 'rs1'))
    S('rs2', None, T(1, 'R', 'rs3'))
    S('rs3', None, T(0, 'R', 'sh1'))
    S('sh1', T(1, 'R', 'sh2'), T(1, 'R', 'sh1'))
    S('sh2', T(0, 'R', 'sh3'), None)
    S('sh3', None, T(0, 'R', 'sh4'))
    S('sh4', None, T(1, 'R', 'sh5'))
    S('sh5', None, T(1, 'R', 'sh6'))
    S('sh6', T(0, 'L', 'PC1'), T(1, 'L', 'sh7'))      # 0: r = 0: m is prime
    S('sh7', None, T(0, 'L', 'PM1'))                  # R hole at cell 1, mod walk
    parser_left('PC', T(1, 'L', 'nP'))                # prime: past D's hole, to G
    hole_right('rb', T(1, 'R', 'c1'))                 # to D's hole, rebuild
    S('c1', T(1, 'R', 'c2'), T(1, 'R', 'c1'))
    S('c2', T(1, 'R', 'c3'), None)
    S('c3', T(1, 'L', 'c4'), T(1, 'R', 'c3'))
    S('c4', T(0, 'R', 'c5'), T(1, 'L', 'c4'))
    S('c5', None, T(1, 'R', 'c6'))
    S('c6', None, T(1, 'R', 'c7'))
    S('c7', None, T(0, 'R', 'c8'))
    S('c8', None, T(0, 'R', 'sh4'))

def composite():
    # G += 1: on G's cell 0, the hole moves one cell left, a cell is added
    hole_left('g', T(0, 'R', 'gi1'))
    S('gi1', T(1, 'L', 'gi2'), None)
    S('gi2', T(0, 'L', 'gi3'), None)
    S('gi3', T(1, 'R', 'rbZ2'), None)

def update(halt_state, target):
    # make Z = H(0) two cells left of L, then to L's hole
    hole_left('n', T(1, 'L', 'z1'))
    S('z1', T(0, 'L', 'z2'), None)
    S('z2', T(0, 'L', 'z3'), None)
    S('z3', T(1, 'L', 'z4'), None)
    S('z4', T(0, 'L', 'z5'), None)
    S('z5', T(1, 'R', 'aZ2'), None)
    # advance L's cursor: fill the hole; the next cell is the new hole unless it is
    # L's last cell (then the hole stays: L is exhausted)
    hole_right('a', T(1, 'L', 'a1'))
    S('a1', T(1, 'R', 'a2'), None)
    S('a2', None, T(1, 'R', 'a3'))
    S('a3', T(0, 'L', 'a5'), T(1, 'L', 'a4'))
    S('a4', None, T(0, 'R', 'w1'))
    S('a5', None, T(1, 'L', 'a6'))
    S('a6', None, T(0, 'R', 'v1'))
    # cursor advanced: to B's last cell; B -= 1, or (B = 0) Z += 1
    walk_right('w', T(0, 'L', 'e1'))
    S('e1', None, T(1, 'L', 'e2'))
    S('e2', T(0, 'R', 'r1'), T(1, 'L', 'AP'))         # 0: B was 0: put the cell back
    S('r1', None, T(1, 'R', 'r2'))
    S('r2', T(1, 'L', 'XP'), None)
    hole_left('A', T(1, 'R', 'a1'))                   # back to L's hole, advance
    hole_left('X', T(1, 'L', 'ZP'))                   # past L's hole to Z's
    hole_left('Z', T(0, 'R', 'i1'))                   # Z += 1, then to L's hole
    S('i1', T(1, 'L', 'i2'), None)
    S('i2', T(0, 'L', 'i3'), None)
    S('i3', T(1, 'R', 'aZ2'), None)
    # L exhausted: B -= 1 and Z += 1 while B > 0; then B is erased
    walk_right('v', T(0, 'L', 'u1'))
    S('u1', None, T(1, 'L', 'u2'))
    S('u2', T(0, 'R', 's1'), T(1, 'L', 'XP'))
    S('s1', None, T(0, 'L', 's2'))
    S('s2', T(0, 'L', 's2'), T(1, 'L', 's3'))         # to the next block on the left
    S('s3', T(0, 'R', 's4'), T(1, 'L', 'EP'))         # 0: it is M: the update is over
    S('s4', None, T(0, 'L', 'YZ1'))
    # end of a step: L loses its hole and its last cell (P(x)); make the next Z
    hole_left('E', T(1, 'R', 't1'))
    S('t1', T(1, 'R', 't2'), None)
    S('t2', None, T(0, 'L', 'nP'))
    # end of the update: the same for L, then check Z = 1, write M and G = H(1)
    hole_left('Y', T(1, 'R', 'y1'))
    S('y1', T(1, 'R', 'y2'), None)
    S('y2', None, T(0, 'L', 'FP'))
    hole_left('F', T(1, 'R', 'f1'))
    S('f1', T(1, 'R', 'f2'), None)
    S('f2', None, T(1, 'R', 'f3'))
    S('f3', T(0, 'R', halt_state), T(1, 'R', 'f4'))    # 0: Z = 0
    if target == 1:
        S('f4', T(0, 'L', 'f5'), T(1, 'R', halt_state))  # 1: Z >= 2
    else:   # test variant: halt iff the entry is not `target` (>= 2)
        S('f4', T(0, 'R', halt_state), T(1, 'R', 'q2'))
        for j in range(2, target):
            S(f'q{j}', T(0, 'R', halt_state), T(1, 'R', f'q{j+1}'))
        S(f'q{target}', T(0, 'L', 'f5'), T(1, 'R', halt_state))
    S('f5', None, T(0, 'L', 'f6'))                    # Z's last cell: Z = P(1)
    S('f6', T(0, 'L', 'f7'), T(1, 'L', 'f6'))
    S('f7', T(0, 'L', 'f8'), None)
    S('f8', T(1, 'L', 'f9'), None)                    # M
    S('f9', T(0, 'L', 'f10'), None)
    S('f10', T(0, 'L', 'f11'), None)
    S('f11', T(1, 'L', 'f12'), None)                  # G = H(1)
    S('f12', T(1, 'L', 'f13'), None)
    S('f13', T(0, 'L', 'f14'), None)
    S('f14', T(1, 'R', 'rbZ2'), None)

def build(halt_state='halt', seed_s=(1,), seed_g=1, seed_m=3, target=1):
    """Test variants: another seed list S and gap g (the primes stay the same:
    the machine then follows ext from that list), or another target value."""
    global SEED_S, SEED_G, SEED_M
    SEED_S, SEED_G, SEED_M = list(seed_s), seed_g, seed_m
    ST.clear(); ORDER.clear()
    seed(); trial(); composite(); update(halt_state, target)
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    real = (list(seed_s), seed_g, seed_m, target) == ([1], 1, 3, 1)
    lines = ["; Halts iff Gilbreath's conjecture is false." if real
             else f'; Test variant: seed S={list(seed_s)}, g={seed_g}, m={seed_m}, target {target}.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'gilbreath.txt', 'w').write(out)
    print(len(ORDER), 'states')
