"""Generator for a 2-symbol Turing machine that halts iff Lehmer's totient problem has a
counterexample: a composite n with phi(n) | n - 1.

For n = 3, 4, 5, ...: count phi(n) into a pair, then one mod walk tests phi(n) | n - 1.

phi(n) is the number of k in [1, n - 1] with gcd(k, n - k) = 1 (../carmichael's count); k = 1
always counts, so the count starts at 1 and the pairs k = 2, ..., n - 1 are tested by
../carmichael's coprimality walk.

Tape (left to right):

    1 K 00 1 R 00 [D 00 P]
    K: k slots (hole H_K), R: r slots (hole H_R), k + r = n (../carmichael's sweep blocks)
    D: 1 0 1^d  (../legendre's divisor block: d + 2 cells, its hole on cell 1)
    P: p + 2 cells;  d + p = n - 1;  d counts the coprime pairs so far

Round n: the walk tests (k, n - k) for k = 2, ..., n - 1; coprime: the pair's separator moves
  one cell right (d += 1, p -= 1: ../legendre's shift sh1..sh3), back to R.  Then r = 1 ends the
  round, else the sweep's separator moves right ((k, r) -> (k + 1, r - 1)).
Round end ((k, r) = (n - 1, 1), d = phi(n), p = n - 1 - phi(n)):
  K/R -> (1, n) (../carmichael's reset), then to the pair: ../legendre's test start with
  p = 0 (n prime: next n) or one mod walk: phi(n) | p (so phi(n) | n - 1, n composite since
  p >= 1): HALT; else next n.
Next n: a cell is appended to P (m = d + p = n), D := 1 (all of D and the separator filled,
  then 1 0 1 00 written from D's left end), back to R with the coprime path's parsers, and the
  sweep's separator moves right: (1, n) -> (2, n - 1), the first test of round n + 1.
The seed writes round 3: K/R (2, 1), the pair (1, 1).
Variants (tests): 'nodiv' halts at the first composite n with phi(n) not dividing n - 1
(n = 4), 'prime' at the first prime (n = 3), 'plus1' has one more cell in P (the test is
phi(n) | n: halts at n = 4).
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
    """Move left to the next hole. Lands at hole-1 (a 1), performs `found`."""
    S(prefix+'1', T(0,'L',prefix+'2'), T(1,'L',prefix+'1'))
    S(prefix+'2', T(0,'L',prefix+'1'), found)

def seed(variant):
    # round 3, right to left: P (p = 1), D = 101, R (1 slot, the hole), K (2 slots, hole on a1)
    pat = '1' + '0' + '1' + '00' + '1' + '0' + '00' + '101' + '00' + '111' + ('1' if variant == 'plus1' else '')
    for i, ch in enumerate(reversed(pat)):
        last = i == len(pat) - 1
        S(f'seed{i}', T(int(ch), 'R' if last else 'L', 'KA' if last else f'seed{i+1}'), None)

def walk():
    # ../carmichael's coprimality test of (k, r), verbatim
    S('KA', T(1, 'R', 'KN'), T(1, 'L', 'KA'))            # find H_K (going left), advance it
    S('KN', T(0, 'L', 'KW'), T(0, 'R', 'TR1'))           # 0: off K's end, wrap
    S('KW', T(0, 'R', 'KW1'), T(1, 'L', 'KW'))
    S('KW1', None, T(1, 'R', 'KW2'))                     # K's start cell
    S('KW2', None, T(0, 'R', 'TC1'))                     # H_K on a1; a stride ends: check
    for m in 'RC':
        S(f'T{m}1', T(0, 'R', f'T{m}2'), T(1, 'R', f'T{m}1'))
        S(f'T{m}2', T(0, 'R', f'T{m}3'), None)
        S(f'T{m}3', None, T(1, 'R', f'T{m}4'))           # R's start cell
    S('TR4', T(1, 'R', 'RN'), T(1, 'R', 'TR4'))          # find H_R, advance it
    S('RN', T(0, 'L', 'RW'), T(0, 'L', 'GK1'))
    S('TC4', T(0, 'R', 'CV1'), T(1, 'R', 'TC5'))         # H_R on b1: coprime
    S('TC5', T(1, 'R', 'CN'), T(1, 'R', 'TC5'))
    S('CN', T(0, 'L', 'CW'), T(0, 'L', 'GK1'))           # 0: H_R wraps: not coprime
    for m in 'RC':
        S(f'{m}W', T(0, 'R', f'{m}W1'), T(1, 'L', f'{m}W'))
        S(f'{m}W1', None, T(1, 'R', f'{m}W2'))
        S(f'{m}W2', None, T(0, 'L', 'GK1') if m == 'R' else T(0, 'R', 'EC1'))
    S('GK1', T(0, 'L', 'GK2'), T(1, 'L', 'GK1'))
    S('GK2', T(0, 'L', 'KA'), None)

def sweep():
    # r = 1: round end; else the separator one cell right (../carmichael)
    S('EC1', T(0, 'L', 'RS1'), T(0, 'L', 'SH2'))
    S('SH2', T(1, 'L', 'SH3'), None)
    S('SH3', None, T(0, 'L', 'SH4'))
    S('SH4', T(0, 'L', 'SH5'), None)
    S('SH5', T(1, 'L', 'KA'), None)

def coprime():
    # CV1 (on b2): to D's hole, shift the pair's separator (d += 1), back to R
    parser_right('CV', T(1, 'R', 'sh1'))
    S('sh1', T(1, 'R', 'sh2'), T(1, 'R', 'sh1'))
    S('sh2', T(0, 'R', 'sh3'), None)
    S('sh3', None, T(0, 'L', 'PD2'))
    parser_left('PD', T(1, 'L', 'PB1'))                  # D's hole: found on D's cell 0
    parser_left('PB', T(1, 'R', 'Y'))                    # H_R: found on R's start
    S('Y', T(0, 'R', 'EC1'), None)

def reset():
    # (n - 1, 1) -> (1, n) (../carmichael's RS), then to the pair
    S('RS1', T(1, 'L', 'RS2'), None)
    S('RS2', None, T(1, 'L', 'RS3'))
    S('RS3', T(1, 'L', 'RS4'), None)
    S('RS4', T(1, 'L', 'RS5'), None)
    S('RS5', T(0, 'L', 'RS6'), T(1, 'L', 'RS5'))         # to a1
    S('RS6', None, T(0, 'L', 'RS7'))
    S('RS7', T(1, 'R', 'RS8'), None)
    S('RS8', T(0, 'R', 'RS9'), None)
    S('RS9', T(0, 'R', 'RS10'), None)
    S('RS10', None, T(0, 'R', 'RS11'))
    S('RS11', None, T(1, 'R', 'RS12'))
    S('RS12', None, T(0, 'R', 'PU1'))                    # H_R on b1
    parser_right('PU', T(1, 'R', 'U5'))                  # D's hole
    S('U5', T(0, 'R', 'U6'), T(1, 'R', 'U5'))
    S('U6', T(0, 'R', 'sh4'), None)

def test(variant):
    # ../legendre's test start and one mod walk
    S('sh4', None, T(1, 'R', 'sh5'))
    S('sh5', None, T(1, 'R', 'sh6'))
    S('sh6', T(0, 'R', 'halt') if variant == 'prime' else T(1, 'L', 'r1'),
      T(1, 'L', 'sh7'))                                  # 0: p = 0, n prime: next n
    S('sh7', None, T(0, 'L', 'PM1'))                     # P's hole at cell 1, mod walk
    S('ma1', T(1, 'R', 'ma2'), None)
    S('ma2', None, T(1, 'R', 'ma3'))
    S('ma3', T(0, 'L', 'maw1'), T(1, 'L', 'ma4'))        # 0: the hole was at the last cell
    S('ma4', None, T(0, 'R', 'PR1'))
    S('maw1', T(0, 'R', 'maw2'), T(1, 'L', 'maw1'))
    S('maw2', None, T(1, 'R', 'maw3'))
    S('maw3', None, T(0, 'R', 'PR1'))
    parser_right('PR', T(1, 'L', 'ra1'))
    S('ra1', T(1, 'R', 'ra2'), None)
    S('ra2', None, T(1, 'R', 'ra3'))
    S('ra3', T(0, 'L', 'PK1'), T(1, 'L', 'ra4'))         # 0: P exhausted (hole gone)
    S('ra4', None, T(0, 'L', 'PM1'))
    parser_left('PM', T(1, 'R', 'ma1'))
    parser_left('PK', T(1, 'L', 'k1'))                   # is the D hole at cell 1?
    S('k1', T(0, 'L', 'halt') if variant != 'nodiv' else T(0, 'L', 'A'),
      T(1, 'R', 'halt') if variant == 'nodiv' else T(1, 'R', 'A'))   # 0: phi | p: HALT

def nextn():
    # to P's end (over D's hole and the separator), append a cell
    S('A', T(0, 'R', 'B'), T(1, 'R', 'A'))
    S('B', T(0, 'R', 'C'), T(1, 'R', 'A'))
    S('C', T(1, 'L', 'r1'), T(1, 'R', 'C'))
    # fill the separator and D's hole, then D := 1 from D's left end
    S('r1', T(1, 'L', 'r2'), T(1, 'L', 'r1'))
    S('r2', T(1, 'L', 'r3'), None)
    S('r3', T(1, 'L', 'r3b'), T(1, 'L', 'r3'))
    S('r3b', T(0, 'R', 'c4'), T(1, 'L', 'r3b'))
    S('c4', None, T(1, 'R', 'c5'))
    S('c5', None, T(0, 'R', 'c6'))
    S('c6', None, T(1, 'R', 'c7'))
    S('c7', None, T(0, 'R', 'c8'))
    S('c8', None, T(0, 'L', 'PD2'))                      # back to R as after a coprime pair

def build(halt_state='halt', variant=None):
    ST.clear(); ORDER.clear()
    seed(variant); walk(); sweep(); coprime(); reset(); test(variant); nextn()
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert variant or not unused, unused
    what = "Lehmer's totient problem has a counterexample" if variant is None else f'variant {variant}'
    lines = [f'; Halts iff {what}.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'lehmertotient.txt', 'w').write(out)
    print(len(ORDER), 'states')
