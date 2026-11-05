"""End-to-end tests of the zero-free machine (pure Python stepping).
* Each time a scan ends (C0 entered from R2 or Fs) the tape must hold the counter
  27 + #{k <= n : 2^k has no digit 0}, the separator, and the digits of 2^n in code A,
  for the n just scanned.
* With the counter starting at 28 (one event fewer) the machine must halt in the scan
  of 2^86, and with 63 in the scan of 2^0 = 1.
* The real machine runs past 10^8 steps (C simulator).
Usage: python3 test_e2e.py [file]   (default: build.py's design)"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm, build

def zero_free(n): return '0' not in str(2 ** n)

def tape_for(ctr, n):
    """Expected tape as {cell: 1}, cell 0 = the first parity cell."""
    want = {}
    for i in range(6):                       # v_i at -2i-4, g_i at -2i-3
        if (ctr >> i) & 1: want[-2 * i - 4] = 1
        want[-2 * i - 3] = 1
    for k, ch in enumerate(reversed(str(2 ** n))):
        d = int(ch)
        for j, c in enumerate(str(d % 2) + build.A[d // 2]):
            if c == '1': want[4 * k + j] = 1
    return want

def simulate(text, start, rounds, maxsteps=10 ** 9):
    order, ST, _ = tm.parse(text)
    tape, h, q, n, ctr, steps, origin = {}, 0, order[0], 0, start, 0, None
    while steps < maxsteps:
        b = tape.get(h, 0)
        t = ST[q][b] if q in ST else None
        if t is None:
            return ('halt', n, steps)                  # halted in the scan of 2^n
        if q == 'C1' and origin is None: origin = h    # the first parity cell is cell 0
        w, d, q2 = t
        if q in ('R2', 'Fs') and q2 == 'C0':          # the scan of 2^n is over
            if zero_free(n): ctr += 1
            got = {i - origin: 1 for i, v in tape.items() if v}
            assert got == tape_for(ctr, n), f'round {n}: tape mismatch'
            if n == rounds: return ('ok', n, steps)
            n += 1
        tape[h] = w; h += 1 if d == 'R' else -1; q = q2; steps += 1
    return ('steps', n, steps)

if __name__ == '__main__':
    text = open(sys.argv[1]).read() if len(sys.argv) > 1 else build.build()
    r = simulate(text, build.START, 120)
    print('real machine, 120 rounds:', r); assert r[0] == 'ok'
    for start, rnd in ((28, 86), (63, 0)):
        r = simulate(build.build(start=start), start, 200)
        print(f'counter starting at {start}:', r); assert r[:2] == ('halt', rnd)
    order, states, _ = tm.parse(text)
    res = tm.run(order, states, maxsteps=10 ** 8)
    print('C simulator, 10^8 steps:', res[0]); assert res[0] != 'halt'
    print('ALL OK')
