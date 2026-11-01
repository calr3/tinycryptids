"""The real machine from a blank tape: the tuples reaching the setup (state su0) are the NEXCOM
successors of the seed (3, 2, 2, 2), in order (`ref.tuples`), each once.
Usage: python3 test_enum.py [count]"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm, ref

def decode(t):
    """the four block lengths minus 2 (x, y, a, b) from a tape at su0"""
    bl = [len(b) for b in t.strip('0').replace('0', ' 0 ').replace(' 0  0 ', '|').replace(' 0 ', '0').split('|')]
    return tuple(L - 2 for L in bl[:4])

if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 120
    build.build()
    r = tm.run(build.ORDER, build.ST, maxsteps=10 ** 11, trace='su0', maxtrace=n)
    seen = [decode(t) for t in r[5]]
    g = ref.tuples()
    want = [next(g) for _ in seen]
    print(len(seen), 'tuples, last', seen[-1], 'steps', r[1])
    assert seen == want, next((i, a, b) for i, (a, b) in enumerate(zip(seen, want)) if a != b)
    assert len(set(seen)) == len(seen)
    print('ALL OK')
