"""End to end: threshold variants halt at the first N occurring t times (N read off the
tape at the halt), and the real machine runs 10^8 steps without halting."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm
from build import build
from math import comb

def first_n(t):
    N = 2
    while True:
        if sum(comb(n, k) == N for n in range(N + 1) for k in range(n + 1)) >= t:
            return N
        N += 1

def run(text, steps):
    order, states, _ = tm.parse(text)
    return tm.run(order, states, maxsteps=steps)

if __name__ == '__main__':
    for t in (3, 4):
        st, steps, q, h, tape = run(build(t), 10**9)
        s = tape.strip('0')
        Nblock = s[t + 1:].split('000')[0]       # N with its hole
        N = len(Nblock) - 2
        print(f't={t}: {st} after {steps} steps, N={N}, expected {first_n(t)}')
        assert st == 'halt' and N == first_n(t)
    st, steps, q, h, tape = run(build(), 10**8)
    print('real:', st, steps)
    assert st != 'halt'
