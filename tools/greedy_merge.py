"""Randomised greedy state merging (fast estimate; minimize.py is exact).

Repeatedly merge two random classes, closing under the implied merges (two
merged states must send each defined symbol to merged states); undo on a
conflict. Restarts many times and keeps the smallest partition.
Usage: python3 greedy_merge.py in.txt out.txt [restarts] [seed]
"""
import sys, random
import tm
from minimize_dimacs import build, write

def run(order, ST, rng):
    n = len(order); idx = {s: i for i, s in enumerate(order)}
    tr = [[None if t is None else (t[0], t[1], idx.get(t[2], 'H:' + t[2])) for t in ST[s]] for s in order]
    parent = list(range(n))
    rep = [[tr[i][0], tr[i][1]] for i in range(n)]      # merged transition per class root
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    def try_merge(a, b):
        saved = (parent[:], [r[:] for r in rep])
        todo = [(a, b)]
        while todo:
            x, y = todo.pop(); x, y = find(x), find(y)
            if x == y: continue
            for s in range(2):
                tx, ty = rep[x][s], rep[y][s]
                if tx is None or ty is None: continue
                if tx[:2] != ty[:2]: break
                if isinstance(tx[2], str) or isinstance(ty[2], str):
                    if tx[2] != ty[2]: break
                else:
                    todo.append((tx[2], ty[2]))
            else:
                parent[y] = x
                rep[x] = [rep[x][s] if rep[x][s] is not None else rep[y][s] for s in range(2)]
                continue
            parent[:], rep[:] = saved[0], saved[1]
            return False
        return True
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    rng.shuffle(pairs)
    for i, j in pairs:
        if find(i) != find(j): try_merge(i, j)
    return [find(i) for i in range(n)]

if __name__ == '__main__':
    order, ST, _ = tm.parse(open(sys.argv[1]).read())
    R = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
    rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
    best = None
    for r in range(R):
        cls = run(order, ST, rng)
        k = len(set(cls))
        if best is None or k < best[0]:
            best = (k, cls); print(r, k, flush=True)
    # start state's class first
    cls = best[1]; root0 = cls[0]
    cls = [0 if c == root0 else c + 1 for c in cls]
    o2, s2 = build(order, ST, cls)
    write(o2, s2, sys.argv[2], f'Greedy merge of {sys.argv[1]} by greedy_merge.py')
    print('best', len(o2))
