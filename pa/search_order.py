"""Simulated annealing over the order of the axiom candidates (before B6a, GEN, DET): the order
decides which subsequences the builder can share.  Prints each new best order.

    python3 search_order.py SEED ITERATIONS [b8] [key=value ...]
        b8: the B8a/b/c conjunction as one axiom; key=value: program switches
"""
import os, sys, random, math
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import program

KW = {}

def size(order):
    return program.build(order=order, **KW).state_count()

if __name__ == '__main__':
    seed, iters = int(sys.argv[1]), int(sys.argv[2])
    b8 = 'b8' in sys.argv[3:]
    for a in sys.argv[3:]:
        if '=' in a:
            k, v = a.split('=', 1)
            KW[k] = v if k == 'vchain' else eval(v)
    rnd = random.Random(seed)
    keys = ['B1', 'B2', 'B3', 'B4', 'B6b', 'B6c', 'B7', 'E'] + (['B8'] if b8 else ['B8a', 'B8b', 'B8c'])
    cur = keys[:]; rnd.shuffle(cur)
    curv = size(cur); best = (curv, cur[:])
    T = 2.0
    for it in range(iters):
        c = cur[:]
        if rnd.random() < 0.5:
            i, j = rnd.sample(range(len(c)), 2); c[i], c[j] = c[j], c[i]
        else:
            i = rnd.randrange(len(c)); x = c.pop(i); c.insert(rnd.randrange(len(c) + 1), x)
        v = size(c)
        if v <= curv or rnd.random() < math.exp((curv - v) / T):
            cur, curv = c, v
            if v < best[0]:
                best = (v, c[:]); print(it, best[0], ','.join(best[1]), flush=True)
        T = max(0.05, T * 0.997)
    print('best', best[0], ','.join(best[1]))
