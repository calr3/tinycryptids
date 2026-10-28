"""Parallel randomised greedy state merging with exclusive special transitions.

Like greedy_merge.py, on many processes, until a target size is reached. `special`
(e.g. `xe3:0,xq6:0`) names beep/boop transitions: the class of such a state may contain no
other state with a defined transition on that symbol (what leangen's `excl_*` checks).
Each new best is written to out.txt at once (and out.txt.<k>).
Usage: python3 greedy_merge_par.py in.txt out.txt target workers special [seed0]
"""
import sys, random, multiprocessing as mp
import tm
from minimize_dimacs import build, write

def run(order, ST, rng, specials):
    n = len(order); idx = {s: i for i, s in enumerate(order)}
    tr = [[None if t is None else (t[0], t[1], idx.get(t[2], 'H:' + t[2])) for t in ST[s]] for s in order]
    parent = list(range(n))
    rep = [[tr[i][0], tr[i][1]] for i in range(n)]
    cnt = [[int(tr[i][b] is not None) for b in range(2)] for i in range(n)]   # members defined on b
    spc = [set() for _ in range(n)]                                             # special symbols
    for s, b in specials: spc[idx[s]].add(b)
    def find(x):
        while parent[x] != x: x = parent[x]     # no path compression: try_merge undoes by log
        return x
    def try_merge(a, b):
        log = []   # (y, x, old rep[x], old cnt[x], old spc[x]) for undo
        todo = [(a, b)]
        ok = True
        while todo:
            x, y = todo.pop(); x, y = find(x), find(y)
            if x == y: continue
            c = [cnt[x][s] + cnt[y][s] for s in range(2)]
            sp = spc[x] | spc[y]
            if any(c[s] > 1 for s in sp): ok = False; break
            for s in range(2):
                tx, ty = rep[x][s], rep[y][s]
                if tx is None or ty is None: continue
                if tx[:2] != ty[:2]: ok = False; break
                if isinstance(tx[2], str) or isinstance(ty[2], str):
                    if tx[2] != ty[2]: ok = False; break
                else:
                    todo.append((tx[2], ty[2]))
            if not ok: break
            log.append((y, x, rep[x], cnt[x], spc[x]))
            parent[y] = x
            rep[x] = [rep[x][s] if rep[x][s] is not None else rep[y][s] for s in range(2)]
            cnt[x] = c; spc[x] = sp
        if not ok:
            for y, x, r, c, sp in reversed(log):
                parent[y] = y; rep[x] = r; cnt[x] = c; spc[x] = sp
        return ok
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    rng.shuffle(pairs)
    for i, j in pairs:
        if find(i) != find(j): try_merge(i, j)
    return [find(i) for i in range(n)]

def worker(args):
    path, seed, specials, best, lock, out, target = args
    order, ST, _ = tm.parse(open(path).read())
    rng = random.Random(seed)
    r = 0
    while best.value > target:
        cls = run(order, ST, rng, specials); r += 1
        k = len(set(cls))
        if k < best.value:
            with lock:
                if k < best.value:
                    best.value = k
                    root0 = cls[0]
                    cls = [0 if c == root0 else c + 1 for c in cls]
                    o2, s2 = build(order, ST, cls)
                    for p in (out, f'{out}.{k}'):
                        write(o2, s2, p, f'Greedy merge of {path} by greedy_merge_par.py (seed {seed}, restart {r})')
                    print(f'seed {seed} restart {r}: {k}', flush=True)

if __name__ == '__main__':
    path, out, target, W = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    specials = [(s, int(b)) for s, b in (x.split(':') for x in sys.argv[5].split(','))]
    seed0 = int(sys.argv[6]) if len(sys.argv) > 6 else 1000
    mgr = mp.Manager(); best = mgr.Value('i', 10**9); lock = mgr.Lock()
    with mp.Pool(W) as pool:
        pool.map(worker, [(path, seed0 + i, specials, best, lock, out, target) for i in range(W)])
    print('reached', best.value)
