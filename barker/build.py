"""Generator for a 2-symbol Turing machine that halts iff a Barker sequence of length > 13
exists (see README.md for the tape layout and the algorithm).

Positions are cell pairs [p][a]: a is the element (1 = +1, 0 = -1), p = 1 unmarked,
p = 0 marked. X = dummy (p, a = 0) at -1, then a_0 .. a_{N-1}, a_0 = 1.
Right of X: the gap 0 0, then Z = 1^A 0 1^(D+1) (A agreements, D disagreements).
"""
import sys
ST, ORDER = {}, []
def S(name, t0, t1):
    assert name not in ST, name
    ST[name] = [t0, t1]; ORDER.append(name)
def T(w, d, n): return (w, d, n)
X = None

def build(n0=14, seed='counter'):
    ST.clear(); ORDER.clear()
    if seed == 'counter':
        # ---- seed: a 4-bit counter (positions [0 b], least significant next to the dummy,
        # a sentinel [1 1] beyond) counts up from 18 - n0 to 16; each count appends a zero
        # position by unmarking j (the blank position after the last is a marked 0)
        c0 = 18 - n0
        assert 3 <= n0 <= 18
        bits = [(c0 >> t) & 1 for t in range(4)]
        cells = [1, bits[3]] + [x for t in (2, 1, 0) for x in (0, bits[t])] + [1, 0, 1, 1]
        for t, c in enumerate(cells):
            last = t == len(cells) - 1
            S(f'z{t}', T(c, 'R', 'PRp' if last else f'z{t+1}'), X)
        S('PRa', T(0, 'R', 'PRp'), T(1, 'R', 'PRp'))
        S('PRp', T(1, 'L', 'PLa'), T(1, 'R', 'PRa'))
        S('PLa', T(0, 'L', 'PLp'), T(1, 'L', 'PLp'))
        S('PLp', T(0, 'R', 'Ca'), T(1, 'L', 'PLa'))
        S('Ca', T(1, 'R', 'Q0'), T(0, 'L', 'Cp'))
        S('Cp', T(0, 'L', 'Ca'), T(0, 'R', 'Q1'))
        S('Q0', T(0, 'R', 'Q0'), T(1, 'R', 'PRa'))
        S('Q1', T(0, 'R', 'Q1'), T(1, 'R', 'SMa'))
    else:
        # ---- seed: dummy, a_0 = 1, n0 - 1 zeros, i = N - 2 and j = N - 1 marked, gap, Z = 0 1
        pos = [(1, 0), (1, 1)] + [(1, 0)] * (n0 - 1)
        pos[-1] = (0, pos[-1][1]); pos[-2] = (0, pos[-2][1])
        cells = [c for p in pos for c in p]
        for t, c in enumerate(cells):
            last = t == len(cells) - 1
            S(f'z{t}', T(c, 'R', 'B2' if last else f'z{t+1}'), X)
    # ---- the pair loop. LQp = "I0": on p_i (marked)
    S('Ia', T(0, 'L', 'Ib'), T(1, 'L', 'Ib'))                 # a_{i-1}
    S('Ib', T(0, 'R', 'E1'), T(0, 'R', 'Ic'))                 # p_{i-1}: 0 = boundary: END
    S('Ic', T(0, 'R', 'Ie'), T(1, 'R', 'Ie'))                 # a_{i-1}
    S('Ie', X, T(1, 'R', 'I1'))                               # p_i
    S('I1', T(0, 'R', 'R0p'), T(1, 'R', 'R1p'))               # a_i
    for b in '01':
        S(f'R{b}a', T(0, 'R', f'R{b}p'), T(1, 'R', f'R{b}p'))
        S(f'R{b}p', T(0, 'R', f'J{b}'), T(1, 'R', f'R{b}a'))
    S('J1', T(0, 'L', 'UDa'), T(1, 'L', 'UAa'))
    S('J0', T(0, 'L', 'UAa'), T(1, 'L', 'UDa'))
    for x in 'AD':
        S(f'U{x}a', T(1, 'L', f'U{x}b'), X)                   # p_j: unmark
        S(f'U{x}b', T(0, 'L', f'U{x}c'), T(1, 'L', f'U{x}c'))
        S(f'U{x}c', X, T(0, 'R', f'S{x}a'))                   # p_{j-1}: mark
        S(f'S{x}a', T(0, 'R', f'S{x}p'), T(1, 'R', f'S{x}p'))
        S(f'S{x}p', T(0, 'R', f'G{x}'), T(1, 'R', f'S{x}a'))
        S(f'G{x}', T(0, 'R', f'Z{x}'), X)
    # Z (after g2): S <= 0: 1^(-S);  S > 0: 0 1^S.  Then blank.
    S('ZA', T(0, 'R', 'SAR'), T(1, 'R', 'SER'))     # agree, Z0
    S('ZD', T(0, 'R', 'ZD1'), T(1, 'R', 'SAB'))     # disagree, Z0
    S('ZD1', T(0, 'L', 'ZD2'), T(1, 'R', 'SEA'))
    S('ZD2', T(1, 'L', 'B1'), X)
    S('SER', T(0, 'L', 'ERB'), T(1, 'R', 'SER'))
    S('SEA', T(0, 'L', 'ERA'), T(1, 'R', 'SEA'))
    S('SAR', T(1, 'L', 'A1'), T(1, 'R', 'SAR'))
    S('SAB', T(1, 'L', 'B1'), T(1, 'R', 'SAB'))
    S('ERB', X, T(0, 'L', 'B1'))
    S('ERA', X, T(0, 'L', 'A1'))
    S('A1', T(0, 'L', 'B1'), T(1, 'L', 'A1'))
    S('B1', T(0, 'L', 'B2'), T(1, 'L', 'B1'))
    S('B2', T(0, 'L', 'LPa'), X)
    S('LPa', T(0, 'L', 'LPp'), T(1, 'L', 'LPp'))
    S('LPp', T(0, 'L', 'LQa'), T(1, 'L', 'LPa'))
    S('LQa', T(0, 'L', 'LQp'), T(1, 'L', 'LQp'))
    S('LQp', T(1, 'L', 'Ia'), T(1, 'L', 'LQa'))
    # ---- end of a pass (i was the dummy): re-mark the dummy; rewind:
    # repeat { j += 1 (halt if j was N - 1); if j = N - 1: check; i += 1 }
    S('E1', T(0, 'R', 'E2'), X)
    S('E2', X, T(0, 'R', 'RJa'))
    S('RJa', T(0, 'R', 'RJp'), T(1, 'R', 'RJp'))
    S('RJp', T(1, 'R', 'W1'), T(1, 'R', 'RJa'))
    S('W1', T(0, 'R', 'W2'), T(1, 'R', 'W2'))
    S('W2', T(0, 'R', 'halt'), T(0, 'R', 'W3'))
    S('W3', T(0, 'R', 'W4'), T(1, 'R', 'W4'))
    S('W4', T(0, 'R', 'CG'), T(1, 'L', 'W5'))
    S('W5', T(0, 'L', 'W6'), T(1, 'L', 'W6'))
    S('W6', T(0, 'L', 'LIa'), X)
    S('LIa', T(0, 'L', 'LIp'), T(1, 'L', 'LIp'))
    S('LIp', T(1, 'R', 'V1'), T(1, 'L', 'LIa'))
    S('V1', T(0, 'R', 'V2'), T(1, 'R', 'V2'))
    S('V2', X, T(0, 'R', 'RJa'))
    S('CG', T(0, 'R', 'K0'), X)
    # ---- check |S| <= 1, leaving Z empty; PASS returns by A1/B1
    S('K0', T(0, 'R', 'K1'), T(1, 'R', 'K4'))
    S('K1', T(0, 'L', 'A1'), T(1, 'R', 'K2'))
    S('K2', T(0, 'L', 'K3'), T(1, 'R', 'F1v'))
    S('K3', X, T(0, 'L', 'A1'))
    S('K4', T(0, 'L', 'K5'), T(1, 'R', 'F1u'))
    S('K5', X, T(0, 'L', 'B1'))
    # ---- fail: erase Z, unmark i, increment, i := N - 2 (j = N - 1 already)
    S('F1v', T(0, 'L', 'F2v'), T(1, 'R', 'F1v'))
    S('F2v', T(0, 'L', 'F3'), T(0, 'L', 'F2v'))
    S('F1u', T(0, 'L', 'F2u'), T(1, 'R', 'F1u'))
    S('F2u', T(0, 'L', 'F4'), T(0, 'L', 'F2u'))
    S('F3', T(0, 'L', 'F4'), X)
    S('F4', T(0, 'L', 'FCa'), X)
    S('FCa', T(0, 'L', 'FCp'), T(1, 'L', 'FCp'))
    S('FCp', T(0, 'L', 'FDa'), T(1, 'L', 'FCa'))
    S('FDa', T(0, 'L', 'FDp'), T(1, 'L', 'FDp'))
    S('FDp', T(1, 'R', 'ITa'), T(1, 'L', 'FDa'))
    S('ITa', T(0, 'R', 'ITp'), T(1, 'R', 'ITp'))
    S('ITp', T(0, 'R', 'INC'), T(1, 'R', 'ITa'))
    S('INC', T(1, 'L', 'INQ'), T(0, 'L', 'INCp'))
    S('INCp', T(0, 'L', 'INC'), T(1, 'L', 'INC'))
    S('INQ', T(0, 'L', 'INQ2'), T(1, 'L', 'INQ2'))
    S('INQ2', T(0, 'L', 'INQ3'), T(1, 'L', 'INQ3'))
    S('INQ3', T(1, 'R', 'SMa'), T(1, 'R', 'SMa'))
    S('SMa', T(0, 'R', 'SMp'), T(1, 'R', 'SMp'))
    S('SMp', T(0, 'L', 'M2b'), T(1, 'R', 'SMa'))
    S('M2b', T(0, 'L', 'M3'), T(1, 'L', 'M3'))
    S('M3', X, T(1, 'L', 'Ia'))
    return ORDER, ST

def text(order, st):
    out = ['blank_symbol: 0']
    for s in order:
        out.append(s)
        for r, t in enumerate(st[s]):
            out.append('-' if t is None else f'{r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(out) + '\n'

if __name__ == '__main__':
    n0 = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    o, s = build(n0)
    open(sys.argv[2] if len(sys.argv) > 2 else 'barker.txt', 'w').write(text(o, s))
    print(len(o), 'states,', len([x for x in o if not x.startswith('z')]), 'without the seed')
