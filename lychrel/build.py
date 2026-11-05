"""Generator for a 2-symbol Turing machine that halts iff reverse-and-add from 196
reaches a palindrome:  exists k, rev10 (F^k 196) = F^k 196,  F x = x + rev10 x.

Numbers are kept in unary.  One round, for the current x:
    T := x, A := 0
    while T > 0:  A := 10 A + T mod 10,  T := T div 10      (so A = rev10 x)
    if A = x: HALT
    x := x + A

Tape (blocks of 1s; separators are runs of at least two 0s; a hole is a single 0):
    D 00 X G T 00 A 00 Q 00 P
  - D: 12 cells d0..d11 with one hole at d(p+1): a counter p mod 10.
  - X: x + 3 cells.  G: at least two 0s.
  - T: t + 3 cells with a hole (a cursor walking right), or T is X itself (the
    first iteration of a round).  A: a + 1 cells.
  - Q and P are made at the right end by their first cell (Q with 3 cells).
Division (p = 9 at the start; the hole of T at cell 1):  repeat { p += 1; if p
  wrapped to 0: append a cell to Q; move T's hole one cell right } until the
  hole reaches T's last cell.  That is t + 1 steps: Q ends with t div 10 + 3
  cells (T's code for t div 10), and p = t mod 10.  T is then erased (unless
  it is X: two 0s and D on its left).
Multiplication: repeat { append a cell to P; p -= 1; if p wrapped to 9:
  { if A has 1 cell: stop; erase A's first cell } }.  P ends with
  (t mod 10) + 10 a + 1 cells (A's code), and p = 9 again.  A's last cell is
  erased: Q and P become T and A.  If T has 3 cells (t = 0), A = rev10 x.
Compare: T is erased; a hole walks X from cell x + 1 down to 1; for each
  position one cell of A is consumed and appended to X.  If A has its last cell
  left at position c: c = 1 means A = x, HALT; otherwise the walk stops.  If
  the walk ends first, the rest of A is moved to X.  A's last cell stays (A = 0)
  and X's hole goes to cell 1: the next round starts with T = X.
The seed writes the tape of the multiplication for T = 59, A = 1 with x = 1:
the run then computes A = 195 and x = 1 + 195 = 196, and goes on from there.
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

def skip_right(names, last):
    """A chain moving right across alternating runs: names[0] skips 1s, names[1]
    skips 0s, ... ; `last` is the transition taken when the final run ends."""
    for i, n in enumerate(names):
        nxt = names[i + 1] if i + 1 < len(names) else None
        if i % 2 == 0:   # on 1s
            S(n, T(0, 'R', nxt) if nxt else last, T(1, 'R', n))
        else:            # on 0s
            S(n, T(0, 'R', n), T(1, 'R', nxt) if nxt else last)

SEED_X = 1
SEED_T = 59
SEED_A = 1
def seed_cells():
    q, d = divmod(SEED_T, 10)
    p = d
    D = ['1'] * 12; D[p + 1] = '0'
    return ''.join(D) + '00' + '1' * (SEED_X + 3) + '00' + '1' * (SEED_A + 1) + '00' + \
        '1' * (q + 3) + '00' + '1'

def seed():
    pat = seed_cells()
    for i, ch in enumerate(pat):
        last = i + 1 == len(pat)
        S(f'seed{i}', T(int(ch), 'L' if last else 'R', 'hBP' if last else f'seed{i+1}'), None)

def rev_loop():
    # to D's hole, then p += 1
    hole_left('hF', T(1, 'R', 'fA'))
    S('fA', T(1, 'R', 'fC'), None)
    S('fC', None, T(1, 'R', 'fD'))
    S('fD', T(0, 'L', 'fw1'), T(1, 'L', 'fE'))
    S('fE', None, T(0, 'R', 'nP'))
    S('fw1', T(0, 'R', 'fw2'), T(1, 'L', 'fw1'))
    S('fw2', None, T(1, 'R', 'fw3'))
    S('fw3', None, T(0, 'R', 'wP'))
    # no wrap: to T's hole and advance it
    hole_right('n', T(1, 'L', 'a1'))
    # wrapped: past T's hole, append to Q (made with 3 cells), back to the hole
    hole_right('w', T(1, 'R', 'e1'))
    S('e1', T(0, 'R', 'e2'), T(1, 'R', 'e1'))
    S('e2', T(0, 'R', 'e2'), T(1, 'R', 'e3'))
    S('e3', T(0, 'R', 'e4'), T(1, 'R', 'e3'))
    S('e4', T(0, 'R', 'e5'), None)
    S('e5', T(1, 'R', 'c1'), T(1, 'R', 'e6'))    # 0: no Q yet
    S('e6', T(1, 'L', 'bkP'), T(1, 'R', 'e6'))
    S('c1', T(1, 'R', 'c2'), None)
    S('c2', T(1, 'L', 'bkP'), None)
    hole_left('bk', T(1, 'R', 'a1'))
    # advance T's hole; at T's last cell the walk is over
    S('a1', T(1, 'R', 'a2'), None)
    S('a2', None, T(1, 'R', 'a3'))
    S('a3', T(0, 'L', 'wd1'), T(1, 'L', 'a4'))
    S('a4', None, T(0, 'L', 'hFP'))
    # walk over: T is X (two 0s then D on its left): keep it; else erase T
    S('wd1', T(0, 'L', 'wd2'), T(1, 'L', 'wd1'))
    S('wd2', T(0, 'L', 'wd3'), None)
    S('wd3', T(0, 'R', 'wd5'), T(1, 'R', 'rP2'))
    S('wd5', T(0, 'R', 'wd6'), None)
    S('wd6', T(0, 'R', 'er'), None)
    S('er', T(0, 'R', 'rP4'), T(0, 'R', 'er'))
    # to D's hole, then p -= 1
    hole_left('hB', T(1, 'R', 'bA'))
    S('bA', T(1, 'L', 'bC'), None)
    S('bC', None, T(1, 'L', 'bD'))
    S('bD', T(0, 'R', 'bw1'), T(1, 'R', 'bE'))
    S('bE', None, T(0, 'R', 'rP1'))
    S('bw1', T(0, 'L', 'bw2'), T(1, 'R', 'bw1'))
    S('bw2', None, T(1, 'L', 'bw3'))
    S('bw3', None, T(0, 'R', 'rA1'))
    # append a cell to P (the first one makes P)
    skip_right(['rP1', 'rP2', 'rP3', 'rP4', 'rP5'], None)
    ST['rP5'][0] = T(0, 'R', 'rP6')
    S('rP6', T(0, 'R', 'rP7'), None)
    S('rP7', T(0, 'R', 'rP8'), T(1, 'R', 'rP7'))
    S('rP8', T(0, 'R', 'rP9'), None)
    S('rP9', T(1, 'L', 'hBP'), T(1, 'R', 'rP9'))
    # wrapped: consume A's first cell (or end the iteration), then append to P
    skip_right(['rA1', 'rA2', 'rA3', 'rA4'], None)
    ST['rA4'][1] = T(1, 'R', 'cA1')
    S('cA1', T(0, 'L', 'iE'), T(1, 'L', 'cA2'))
    S('cA2', None, T(0, 'R', 'rP5'))
    # iteration end: erase A; Q and P are the new T and A
    S('iE', None, T(0, 'R', 'it1'))
    S('it1', T(0, 'R', 'it1'), T(1, 'R', 'it2'))
    S('it2', None, T(1, 'R', 'it3'))
    S('it3', None, T(1, 'R', 'it4'))
    S('it4', T(0, 'L', 'tz1'), T(1, 'L', 'it5'))   # 0: t = 0
    S('it5', None, T(1, 'L', 'it6'))
    S('it6', None, T(0, 'L', 'hFP'))              # hole at T's cell 1
    S('tz1', None, T(0, 'L', 'tz2'))               # erase T, compare
    S('tz2', None, T(0, 'L', 'tz3'))
    S('tz3', None, T(0, 'L', 'cm0'))

def compare(halt_state):
    S('cm0', T(0, 'L', 'cm0'), T(1, 'L', 'cm1'))
    S('cm1', None, T(0, 'R', 'ka1'))             # hole at X's cell x + 1
    skip_right(['ka1', 'ka2'], None)
    ST['ka2'][1] = T(1, 'R', 'ka3')
    S('ka3', T(0, 'L', 'fl0'), T(1, 'L', 'ka4'))  # A has 1 cell: no more to move
    S('ka4', None, T(0, 'L', 'kd1'))
    S('kd1', T(0, 'L', 'kd1'), T(1, 'R', 'kd2'))
    S('kd2', T(1, 'L', 'kh1'), None)              # append to X
    S('kh1', T(0, 'L', 'kh2'), T(1, 'L', 'kh1'))
    S('kh2', T(0, 'R', 'kr1'), T(1, 'L', 'kv1'))  # 0: no hole (moving the rest)
    S('kr1', T(0, 'R', 'ka1'), None)
    S('kv1', T(0, 'R', 'kn1'), T(1, 'R', 'kv2'))  # 0: the hole was at cell 1
    S('kv2', None, T(0, 'R', 'kv3'))
    S('kv3', T(1, 'R', 'ka1'), None)
    S('kn1', None, T(1, 'R', 'kn2'))
    S('kn2', T(1, 'R', 'ka1'), None)
    # A has one cell left (it stays: A = 0 for the next round); X's hole at
    # cell 1: equal, HALT; else fill the hole and start the walk at cell 1
    S('fl0', None, T(1, 'L', 'fl1'))
    S('fl1', T(0, 'L', 'fl1'), T(1, 'L', 'fl2'))
    S('fl2', T(0, 'L', 'fl3'), T(1, 'L', 'fl2'))
    S('fl3', T(0, 'R', 'fl5'), T(1, 'L', 'fl6'))  # 0: no hole
    S('fl6', T(0, 'R', halt_state), T(1, 'R', 'fl7'))
    S('fl7', None, T(1, 'R', 'fl4'))
    S('fl4', T(1, 'L', 'ix1'), None)
    S('ix1', T(0, 'R', 'ix2'), T(1, 'L', 'ix1'))
    S('fl5', T(0, 'R', 'ix2'), None)
    S('ix2', None, T(1, 'R', 'ix3'))
    S('ix3', None, T(0, 'L', 'hFP'))

def build(halt_state='halt', seed_x=1, seed_t=59, seed_a=1):
    global SEED_X, SEED_T, SEED_A
    SEED_X, SEED_T, SEED_A = seed_x, seed_t, seed_a
    ST.clear(); ORDER.clear()
    seed(); rev_loop(); compare(halt_state)
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    lines = ['; Halts iff reverse-and-add from 196 reaches a palindrome.' if (seed_x, seed_t, seed_a) == (1, 59, 1)
             else f'; Test variant: seed x={seed_x}, T={seed_t}, A={seed_a}.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'lychrel.txt', 'w').write(out)
    print(len(ORDER), 'states')
