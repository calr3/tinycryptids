"""Generator for a 2-symbol Turing machine that halts iff some power 2^n with
n > 86 has no decimal digit 0 (2^86 is conjectured to be the last such power).

Algorithm.  The tape holds 2^n in decimal.  Each round doubles it, then scans the new
number for a digit 0; a power without a 0 adds 1 to a counter, which overflows (and
the machine halts) at the 37th such power.  The powers 2^n with n <= 86 without a 0
are exactly 36, so the 37th is a counterexample.

Tape (left to right):

    v5 g5 v4 g4 ... v0 g0 | 0 0 | b x y z | b x y z | ... | blank
    counter                  sep   digit 0   digit 1        (least significant first)

Counter: bits v_i, each with a guard g_i = 1; it starts at 27 and overflows at 64
(the carry runs into the blank cell left of v5).  A digit d = 2a + b takes four cells:
the parity b, then three cells x y z for a in 0..4.

Two codes.  Between rounds the digits are in code A (A[a]).  Doubling gives the
parity cell the carry (the new digit is 2 (d mod 5) + carry, carry out [d >= 5]), and
writes x y z in code B as it reads them, one cell at a time: B[b, a] (BETA below) depends
on the old digit, and determines a' = (2a + b) mod 5 of the new one.  The scan, right to
left, rewrites each digit from B back into A (z, then y, then x, each cell determined by
what it has read so far) and looks for the digit 0.

Pass (C0/C1: carry, P*: reading x y z): a blank group ends the number (A is never 000):
with carry 1 it becomes the digit 1, with carry 0 the scan starts on the top digit.
Scan (S*): left, digit by digit; the separator (0 0 at y z, which no B word has) means no
digit 0: increment the counter (G, I), go back right after the separator (R1, R2) and
double again.  Found (F*): rewrite the remaining digits into A, then double.
"""
import sys

A = ['010', '001', '011', '111', '101']           # code A of a = 0..4 (x y z)
BETA = {'00': '010', '01': '001', '02': '011', '03': '111', '04': '101',
        '10': '111', '11': '101', '12': '110', '13': '001', '14': '011'}   # B[b, a]
START = 27                                        # counter start: 64 - 37

ST, ORDER = {}, []
def S(name, t0, t1):
    assert name not in ST, name
    ST[name] = [t0, t1]; ORDER.append(name)
def T(w, d, n): return (w, d, n)

def build(A=A, BETA=BETA, start=START, halt_state='halt'):
    ST.clear(); ORDER.clear()
    f = lambda b, a: ((2 * a + b) % 5, (2 * a + b) // 5)
    B = lambda b, a: BETA[f'{b}{a}']
    inv = {}                                       # B word -> a'
    for b in (0, 1):
        for a in range(5):
            assert inv.setdefault(B(b, a), f(b, a)[0]) == f(b, a)[0]
    assert all(w != '000' and not w.endswith('00') for w in A) and len(set(A)) == 5
    assert all(not w.endswith('00') and w[2] == A[a2][2] for w, a2 in inv.items())
    # ---- seed: the counter (cells g5 .. g0, and v5 if it is 1), the separator, then C1
    bits = [(start >> i) & 1 for i in range(6)]
    cells = [1, 1] if bits[5] else [1]
    for i in range(4, -1, -1): cells += [bits[i], 1]
    cells += [0, 0]
    for i, c in enumerate(cells):
        S(f'seed{i}', T(c, 'R', f'seed{i + 1}' if i + 1 < len(cells) else 'C1'), None)
    # ---- pass: A -> B, one cell at a time
    S('C0', T(0, 'R', 'P0_'), T(0, 'R', 'P1_'))
    S('C1', T(1, 'R', 'P0_'), T(1, 'R', 'P1_'))
    for b in (0, 1):
        for pre in ['', '0', '1', '00', '01', '10', '11']:
            i = len(pre)
            ts = []
            for s in '01':
                p2 = pre + s
                cons = [a for a in range(5) if A[a][:i + 1] == p2]
                if cons:
                    outs = {B(b, a)[i] for a in cons}
                    assert len(outs) == 1
                    w = int(outs.pop())
                    ts.append(T(w, 'R', f'P{b}_{p2}') if i < 2 else T(w, 'R', f'C{f(b, cons[0])[1]}'))
                elif b == 0 and p2 == '0' * (i + 1):          # blank group
                    ts.append(T(0, 'R', f'P0_{p2}') if i < 2 else T(0, 'L', 'Z1'))
                else:
                    ts.append(None)
            if any(ts): S(f'P{b}_{pre}', *ts)
    # blank group: clear x y, look at the parity cell
    S('Z1', T(0, 'L', 'Z2'), T(0, 'L', 'Z2'))
    S('Z2', T(0, 'L', 'Z3'), T(0, 'L', 'Z3'))
    S('Z3', T(0, 'L', 'Sz'), T(1, 'R', 'N0'))          # 0: the number has ended; 1: new digit 1
    one = B(0, 0)                                       # a B word for a' = 0
    S('N0', T(int(one[0]), 'R', 'N1'), None)
    S('N1', T(int(one[1]), 'R', 'N2'), None)
    S('N2', T(int(one[2]), 'R', 'C0'), None)
    # ---- scan (S*) and found (F*): rewrite B -> A, right to left
    for m in 'SF':
        S(f'{m}z', T(0, 'L', f'{m}y0'), T(1, 'L', f'{m}y1'))
        for z in '01':
            ts = []
            for y in '01':
                if z == '0' and y == '0':                  # the separator
                    ts.append(T(0, 'L', 'G') if m == 'S' else T(0, 'R', 'Fs'))
                    continue
                a2s = {a2 for w, a2 in inv.items() if w[1:] == y + z}
                outs = {A[a2][1] for a2 in a2s}
                ts.append(T(int(outs.pop()), 'L', f'{m}x{z}{y}') if outs else None)
            S(f'{m}y{z}', *ts)
        for z in '01':
            for y in '01':
                if z + y == '00' or f'{m}x{z}{y}' not in {t[2] for v in ST.values() for t in v if t}:
                    continue
                ts = []
                for x in '01':
                    w = x + y + z
                    if w not in inv: ts.append(None); continue
                    a2 = inv[w]
                    nxt = ('Sb1' if a2 == 0 else 'Sb0') if m == 'S' else 'Fb'
                    ts.append(T(int(A[a2][0]), 'L', nxt))
                S(f'{m}x{z}{y}', *ts)
    S('Sb1', T(0, 'L', 'Fz'), T(1, 'L', 'Sz'))           # parity 0, a' = 0: the digit 0
    S('Sb0', T(0, 'L', 'Sz'), T(1, 'L', 'Sz'))
    S('Fb', T(0, 'L', 'Fz'), T(1, 'L', 'Fz'))
    S('Fs', T(0, 'R', 'C0'), None)
    # ---- counter: G at a guard, I at a bit; then back right after the separator
    S('G', T(0, 'L', halt_state), T(1, 'L', 'I'))                   # blank guard: overflow, halt
    S('I', T(1, 'R', 'R1'), T(0, 'L', 'G'))
    S('R1', T(0, 'R', 'R2'), T(1, 'R', 'R1'))
    S('R2', T(0, 'R', 'C0'), T(1, 'R', 'R1'))
    refs = {t[2] for v in ST.values() for t in v if t}
    assert not (refs - set(ST) - {halt_state}), refs - set(ST)
    assert not (set(ST) - refs - {ORDER[0]}), set(ST) - refs
    lines = ['; Halts iff some 2^n with n > 86 has no decimal digit 0.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '',
             'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'zerofree.txt', 'w').write(out)
    print(len(ORDER), 'states')
