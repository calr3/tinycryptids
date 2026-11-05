"""Check the tape invariant the Lean proof uses, on the real machine.

At every round start (state E entered from D) the tape must be
    x y 0 0 | d0 d1 ... dk        (digit 0 = 01, 1 = 10, 2 = 11; d0 = least significant)
with d0..dk the base-3 digits of 2^n and c = 2x + y the number of k < n whose power 2^k
has no digit 2. Usage: python3 test_tape.py [rounds]   (default 300)
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm

order, ST, _ = tm.parse(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                          'machines', 'erdos_15.txt')).read())
ENC = {0: (0, 1), 1: (1, 0), 2: (1, 1)}

def digits3(n):
    out = []
    while n: out.append(n % 3); n //= 3
    return out

def main(rounds):
    tape, h, q, n, c = {}, 0, order[0], 0, 0
    while n < rounds:
        b = tape.get(h, 0)
        t = ST[q][b]
        assert t is not None, f'halted in round {n}'
        if q == 'D' and b == 0:              # round n's pass is done: check the round start
            ds = digits3(2 ** n)
            want = {-4: c >> 1, -3: c & 1, -2: 0, -1: 0}
            for i, d in enumerate(ds):
                want[2 * i], want[2 * i + 1] = ENC[d]
            got = {i: v for i, v in tape.items() if v}
            assert got == {i: v for i, v in want.items() if v}, f'round {n}: tape mismatch'
            assert h == 2 * len(ds) + 1, f'round {n}: head at {h}'
            if 2 not in ds: c += 1
            n += 1
        w, d, q = t
        tape[h] = w; h += 1 if d == 'R' else -1
    print(f'OK: {rounds} rounds, tape = counter {c} + digits of 2^n in base 3')

if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 300)
