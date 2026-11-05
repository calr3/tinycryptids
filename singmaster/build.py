"""Generator for a 2-symbol Turing machine that halts iff some N >= 2 occurs at least
9 times in Pascal's triangle (Singmaster's bound 8 fails).

Every occurrence of N >= 2 lies in a row n <= N, so for N = 2, 3, ... the machine counts
the entries equal to N in rows 0..N and halts when the count reaches 9.  The triangle is
kept on the tape and grows by one row per N.

Numbers are in unary; a block of v + 2 cells holds v; a hole is a single 0 inside a block.
Tape:
    C 0 N 000 row0 000 row1 000 ... 000 rowN
  - C: t + 2 cells (t = 9), a hole at cell 1 + (matches so far).  A match moves the hole
    one cell right; when the cell two to its right is the separator, the machine HALTS.
  - N: N + 2 cells, a hole (cursor) at cell N between comparisons.
  - row n: its entries C(n, 0), ..., C(n, n) as blocks, separated by 00.
Compare (one per entry E, in tape order): E's cursor starts at cell 1 and moves right, N's
cursor moves left from cell N, in lockstep (E first).  E = N iff E's cursor is exhausted
in the round where N's cursor is at cell 1.  Afterwards N's cursor goes back to cell N.
End of the triangle (four 0s): the next row is built at the end from the last row
(processed right to left; rows are palindromes): for each cell of a source block, the
last two blocks of the new row grow by 1 (append 2, move the separator one cell right);
a new source block starts a new block (written as 1 00 111).  Then N += 1 (a cell on the
left of N; C is moved one cell left), C's hole goes back to cell 1, and the compare
scan starts at row 0.
The seed writes C, N = 1, rows 0 and 1, and starts at the end of the scan for N = 1.
"""
import sys
ST = {}
ORDER = []
def S(name, t0, t1):
    assert name not in ST, name
    ST[name] = [t0, t1]; ORDER.append(name)
def T(w, d, n): return (w, d, n)

def hole_left(p, found):
    """Move left to the next hole (a single 0), crossing runs of >= 2 zeros. The found
    transition is taken on the 1 left of the hole."""
    S(p + 'P', T(0, 'L', p + 'Z1'), T(1, 'L', p + 'P'))
    S(p + 'Z1', T(0, 'L', p + 'Z2'), found)
    S(p + 'Z2', T(0, 'L', p + 'Z2'), T(1, 'L', p + 'P'))

def hole_right(p, found):
    S(p + 'P', T(0, 'R', p + 'Z1'), T(1, 'R', p + 'P'))
    S(p + 'Z1', T(0, 'R', p + 'Z2'), found)
    S(p + 'Z2', T(0, 'R', p + 'Z2'), T(1, 'R', p + 'P'))

def seed(t):
    # C for t - 2 matches (row N, which holds N twice, is not stored), N = 1, row 0
    pat = '10' + '1' * (t - 2) + '0' + '101' + '000' + '111' + '000'
    for i, ch in enumerate(pat):
        nxt = 'X4' if i + 1 == len(pat) else f'seed{i + 1}'
        S(f'seed{i}', T(int(ch), 'R', nxt), None)

def compare(halt):
    # round: advance E's cursor (right); E exhausted -> to N in "done" mode
    hole_right('e', T(1, 'R', 'I'))
    S('I', T(0, 'L', 'I2'), T(1, 'L', 'J'))
    S('J', None, T(0, 'L', 'K'))
    S('K', T(1, 'L', 'nP'), None)
    S('I2', None, T(1, 'L', 'I3'))
    S('I3', T(0, 'L', 'dP'), None)
    # advance N's cursor (left); exhausted first -> E > N
    hole_left('n', T(1, 'L', 'B'))
    S('B', T(0, 'R', 'Bd2'), T(1, 'R', 'B2'))
    S('B2', None, T(0, 'R', 'B3'))
    S('B3', T(1, 'R', 'eP'), None)
    # E done: N's cursor at cell 1 -> match: C += 1 (halt at t)
    hole_left('d', T(1, 'L', 'Bd'))
    S('Bd', T(0, 'L', 'CW'), T(1, 'R', 'Bd2'))
    S('Bd2', None, T(1, 'R', 'T0'))
    S('CW', T(1, 'R', 'CI1'), T(1, 'L', 'CW'))
    S('CI1', None, T(1, 'R', 'CI2'))
    S('CI2', T(0, 'R', halt), T(1, 'L', 'CI3'))
    S('CI3', None, T(0, 'R', 'CR'))
    S('CR', T(0, 'R', 'Bd2'), T(1, 'R', 'CR'))
    # N's cursor back to cell N, then finish E and go to the next entry
    S('T0', T(1, 'R', 'T1'), None)
    S('T1', T(0, 'L', 'T2'), T(1, 'R', 'T1'))
    S('T2', None, T(1, 'L', 'T3'))
    S('T3', None, T(0, 'R', 'fP'))
    hole_right('f', T(1, 'L', 'FE'))
    S('FE', T(1, 'R', 'FE2'), None)
    S('FE2', T(0, 'R', 'X2'), T(1, 'R', 'FE2'))
    S('X2', T(0, 'R', 'X3'), None)
    S('X3', T(0, 'R', 'X4'), T(1, 'R', 'X5'))
    S('X4', T(1, 'R', 'G1'), T(1, 'R', 'X5'))
    S('X5', None, T(0, 'R', 'eZ1'))

def generate():
    # start of the new row: 11 three cells after the last row; cursor at the last block
    S('G1', T(1, 'L', 'G2'), None)
    S('G2', None, T(1, 'L', 'G3'))
    S('G3', T(0, 'L', 'G3'), T(1, 'L', 'G7'))
    S('G7', None, T(0, 'R', 'WT1'))
    # first cell of a source block: append 1 00 111 after the last 1 (q): q+1 := 1,
    # q+4..q+6 := 1
    S('WT1', T(0, 'R', 'WT2'), T(1, 'R', 'WT1'))
    S('WT2', T(0, 'R', 'WT3'), T(1, 'R', 'WT1'))
    S('WT3', T(0, 'R', 'WT4'), T(1, 'R', 'WT1'))
    S('WT4', T(1, 'R', 'AT1'), T(1, 'R', 'WT1'))
    S('AT1', T(1, 'R', 'AT2'), None)
    S('AT2', T(1, 'L', 'AT3'), None)
    S('AT3', T(0, 'L', 'AT4'), T(1, 'L', 'AT3'))
    S('AT4', T(0, 'L', 'AT5'), None)
    S('AT5', T(1, 'L', 'sP'), None)
    # back to the source cursor; advance it left (exhausted -> next block)
    hole_left('s', T(1, 'R', 'U1'))
    S('U1', T(1, 'L', 'U2'), None)
    S('U2', None, T(1, 'L', 'U3'))
    S('U3', T(0, 'L', 'Y2'), T(1, 'R', 'U4'))
    S('U4', None, T(0, 'R', 'W1'))
    # other cells: last two blocks grow by 1
    S('W1', T(0, 'R', 'W2'), T(1, 'R', 'W1'))
    S('W2', T(0, 'R', 'W3'), T(1, 'R', 'W1'))
    S('W3', T(0, 'R', 'W4'), T(1, 'R', 'W1'))
    S('W4', T(0, 'L', 'R1'), T(1, 'R', 'W1'))
    S('R1', T(0, 'L', 'R2'), None)
    S('R2', T(1, 'L', 'R2'), T(1, 'L', 'R4'))
    S('R4', T(0, 'L', 'R5'), T(1, 'L', 'R4'))
    S('R5', T(1, 'R', 'R6'), None)
    S('R6', T(0, 'R', 'R7'), None)
    S('R7', None, T(0, 'L', 'R8'))
    S('R8', T(0, 'L', 'sP'), None)
    # source block done: next block on the left, or (three 0s) the row is done
    S('Y2', T(0, 'L', 'Y3'), None)
    S('Y3', T(0, 'L', 'gP'), T(1, 'L', 'G7'))
    # N += 1 (C moves one cell left), C's hole to cell 1, then E's cursor in row 0
    hole_left('g', T(1, 'L', 'GN1'))
    S('GN1', T(1, 'L', 'GN3'), T(1, 'L', 'GN1'))
    S('GN3', None, T(0, 'L', 'CW2'))
    S('CW2', T(1, 'L', 'CX'), T(1, 'L', 'CW2'))
    S('CX', T(0, 'R', 'CY'), T(1, 'L', 'CW2'))
    S('CY', None, T(1, 'R', 'CZ'))
    S('CZ', None, T(0, 'R', 'CQ'))
    S('CQ', T(0, 'R', 'rP'), T(1, 'R', 'CQ'))
    hole_right('r', T(1, 'R', 'FE2'))

def build(t=9, halt='halt'):
    """Test variants: another threshold t (halts at the first N occurring t times)."""
    ST.clear(); ORDER.clear()
    seed(t); compare(halt); generate()
    refs = {x[2] for v in ST.values() for x in v if x}
    missing = refs - set(ST) - {halt}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    lines = ["; Halts iff some N >= 2 occurs at least 9 times in Pascal's triangle." if t == 9
             else f'; Test variant: threshold {t}.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, x in enumerate(ST[n]):
            lines.append('    -' if x is None else f'    {r} {x[0]} {x[1]} {x[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'singmaster.txt', 'w').write(out)
    print(len(ORDER), 'states')
