"""Generator for a 2-symbol Turing machine that halts iff Brocard's problem
has a solution beyond the three known ones: iff n! + 1 = m^2 for some n >= 8.

Tape layout (blocks of 1s separated by '00'):
  W 00 N 00 F 00 S      (during the square test)
  W 00 N 00 F 00 Q      (during the multiplication)
  - F (n!+4 cells) holds n!.  During the test its hole (a single 0) at cell
    u+1 counts the units u of n!+1 used so far; during the multiplication
    its hole (cells 3 .. n!+2) is the copy cursor.
  - S (d+2 cells, d = 2j+1 odd) with a cyclic hole: the odd number being
    subtracted.  When the hole wraps around, S grows by 2.
  - Q: the copies of F made by the multiplication.
  - N (n+2 cells) holds n; its hole counts the copies during the
    multiplication.  N grows to the left, into W.
  - W: a countdown of the rounds n < 8, which skip the square test.
Round for n:
  test (n >= 8): u = 0, d = 1; repeat: one more unit (advance the F hole),
    advance the S hole (wrap: d += 2).  When F has no unit left, u = n!+1,
    and it is a sum 1 + 3 + ... + (2j+1) = (j+1)^2 iff the S hole has just
    wrapped (it is at cell 1): then HALT.  Else erase S.
  multiply: n times copy the n! cells of F (cells 3 .. n!+2) onto Q, then
    merge Q into F: F := (n+1)!.
  grow N (n := n+1), erasing one cell of W; while W is not empty, skip the
    test of the next round; else write S = 101 and put the F hole at cell 1.
The seed writes W = 1^7, N = 1, F = 1! and starts the multiplication of round 1.
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

def seed():
    # W = 1^WARM, 00, N = 1 (hole at cell 1), 00, F = 1! (cursor at cell 3)
    pat = '1' * WARM + '00' + '101' + '00' + '11101'
    for i, ch in enumerate(pat):
        S(f'seed{i}', T(int(ch),'R', f'seed{i+1}' if i+1 < len(pat) else 'x1'), None)

def test(halt_state):
    # one unit: advance the F hole
    S('p1', T(1,'R','p2'), None)
    S('p2', None, T(1,'R','p3'))
    S('p3', T(0,'R','PK2'), T(1,'L','p4'))      # 0: no unit left: is it a square?
    S('p4', None, T(0,'R','PS1'))
    parser_right('PS', T(1,'L','s1'))
    # advance the S hole; on wrap-around S grows by 2
    S('s1', T(1,'R','s2'), None)
    S('s2', None, T(1,'R','s3'))
    S('s3', T(1,'R','s5'), T(1,'L','s4'))       # 0: wrap
    S('s4', None, T(0,'L','PP1'))
    S('s5', T(1,'L','s6'), None)
    S('s6', T(0,'R','s7'), T(1,'L','s6'))
    S('s7', None, T(1,'R','s8'))
    S('s8', None, T(0,'L','PP1'))
    parser_left('PP', T(1,'R','p1'))
    # u = n!+1: square iff the S hole is at cell 1
    parser_right('PK', T(1,'L','k1'))
    S('k1', T(0,'L','k2'), None)
    S('k2', None, T(1,'L','k3'))
    S('k3', T(0,'L',halt_state), T(1,'L','kz'))
    # not a square: erase S, put the N hole at cell 1
    S('kz', T(0,'R','r1'), T(1,'L','kz'))
    S('r1', T(0,'R','r2'), T(0,'R','r1'))
    S('r2', T(0,'L','z1'), T(0,'R','r1'))
    S('z1', T(0,'L','z1'), T(1,'L','z2'))
    S('z2', T(0,'L','z3'), T(1,'L','z2'))
    S('z3', T(0,'L','z4'), None)
    S('z4', T(0,'R','z5'), T(1,'L','z4'))
    S('z5', None, T(1,'R','z6'))
    S('z6', None, T(0,'R','g1'))

def multiply():
    # F cursor at cell 3
    S('g1', T(0,'R','g2'), T(1,'R','g1'))
    S('g2', T(0,'R','g3'), None)
    S('g3', None, T(1,'R','g4'))
    S('g4', None, T(1,'R','g5'))
    S('g5', None, T(1,'R','g6'))
    S('g6', None, T(0,'R','x1'))
    # copy one cell: append a 1 to Q, back to the cursor
    S('x1', T(0,'R','x2'), T(1,'R','x1'))
    S('x2', T(0,'R','x3'), None)
    S('x3', T(1,'L','PB1'), T(1,'R','x3'))
    parser_left('PB', T(1,'R','y1'))
    S('y1', T(1,'R','y2'), None)
    S('y2', None, T(1,'R','y3'))
    S('y3', T(0,'L','PN1'), T(1,'L','y4'))      # 0: one copy done
    S('y4', None, T(0,'R','x1'))
    parser_left('PN', T(1,'R','n1'))
    S('n1', T(1,'R','n2'), None)
    S('n2', None, T(1,'R','n3'))
    S('n3', T(0,'R','m1'), T(1,'L','n4'))       # 0: n copies done: merge
    S('n4', None, T(0,'R','g1'))
    # merge Q into F
    S('m1', T(0,'R','m2'), None)
    S('m2', T(1,'R','m3'), T(1,'R','m2'))
    S('m3', T(1,'R','m4'), None)
    S('m4', T(0,'L','m5'), T(1,'R','m4'))
    S('m5', None, T(0,'L','m6'))
    S('m6', None, T(0,'L','v0'))

def grow():
    # N := N+1 (into W), W loses a cell; W empty -> test next round
    S('v0', T(0,'L','v0b'), T(1,'L','v0'))
    S('v0b', T(0,'L','v1'), None)
    S('v1', T(1,'L','v2'), T(1,'L','v1'))
    S('v2', T(0,'L','v3'), None)
    S('v3', T(0,'L','v4'), T(0,'L','v4'))
    S('v4', T(0,'R','t1'), T(1,'R','w1'))
    # warm-up: N hole at cell 1, multiply
    S('w1', T(0,'R','w2'), None)
    S('w2', T(0,'R','w3'), None)
    S('w3', None, T(1,'R','w4'))
    S('w4', None, T(0,'R','g1'))
    # test setup: F hole at cell 1, S = 101
    S('t1', T(0,'R','t2'), None)
    S('t2', T(0,'R','t3'), None)
    S('t3', T(0,'R','t4'), T(1,'R','t3'))
    S('t4', T(0,'R','t5'), None)
    S('t5', None, T(1,'R','t6'))
    S('t6', None, T(0,'R','t7'))
    S('t7', T(0,'R','t8'), T(1,'R','t7'))
    S('t8', T(0,'R','t9'), None)
    S('t9', T(1,'R','t10'), None)
    S('t10', T(0,'R','t11'), None)
    S('t11', T(1,'L','t12'), None)
    S('t12', T(0,'L','PP1'), None)

WARM = 7
def build(halt_state='halt', warm=7):
    """warm < 7: test variant, the test starts at n = warm + 1."""
    global WARM
    WARM = warm
    ST.clear(); ORDER.clear()
    seed(); test(halt_state); multiply(); grow()
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    lines = [f"; Halts iff n! + 1 = m^2 for some n >= {warm + 1} (Brocard's problem"
             + (" beyond 4, 5, 7)." if warm == 7 else "; test variant)."),
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'brocard.txt', 'w').write(out)
    print(len(ORDER), 'states')
