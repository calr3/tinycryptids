"""Every variant n0 = 2..13 halts with the reference's first Barker sequence on the tape."""
import sys
from sim import run
from ref import first_barker
def decode(s):
    t = s.index('1'); seq = []        # p_0 (the dummy is marked: 0 0); no other marker
    while s[t] == '1':
        seq.append(int(s[t + 1])); t += 2
    return seq
for n0 in range(3, int(sys.argv[1]) if len(sys.argv) > 1 else 14):
    q, steps, s = run(n0)
    seq = decode(s)
    assert q == 'halt' and seq == first_barker(n0), (n0, seq, s)
    print(n0, 'ok', steps, seq)
