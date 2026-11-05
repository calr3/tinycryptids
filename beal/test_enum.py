"""The real machine from a blank tape: the tuples reaching the coprimality test (state gA0)
are the NEXCOM successors of the seed (4, 3, 3, 1, 1, 1), in order, each once.
Usage: python3 test_enum.py [count]"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

def nexcom(r):
    """The next composition (same total, or total + 1 after the last one)."""
    r = list(r); k = len(r)
    h = next(i for i, v in enumerate(r) if v > 0)
    if h == k - 1:
        return [r[h] + 1] + [0] * (k - 1)
    t = r[h]; r[h] = 0; r[0] = t - 1; r[h + 1] += 1
    return r

def decode(t):
    bl = [len(b) for b in t.strip('0').replace('0', ' 0 ').replace(' 0  0 ', '|').replace(' 0 ', '0').split('|')]
    return bl[:6]

if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    build.build()
    r = tm.run(build.ORDER, build.ST, maxsteps=10 ** 10, trace='gA0', maxtrace=n)
    seen = [tuple(L - 4 for L in decode(t)) for t in r[5]]
    cur, want = [1, 0, 0, 0, 0, 0], []
    for _ in range(len(seen)):
        cur = nexcom(cur); want.append(tuple(cur))
    print(len(seen), 'tuples, last', seen[-1], 'steps', r[1])
    assert seen == want, next((i, a, b) for i, (a, b) in enumerate(zip(seen, want)) if a != b)
    print('ALL OK')
