"""Exact minimisation of a TM with unused (undefined) transitions.

Two states may share a class if, on every symbol where both are defined, they
write the same symbol, move the same way, and go to states in a common class
(halting targets must match exactly). The run of the original machine never
uses an undefined transition, so the merged machine performs the same run.

Same encoding as minimize.py, but the CNF is written as DIMACS and
solved by an external binary (no python-sat needed):
  MIN_SOLVER=/path/to/kissat (or cadical)   MIN_TIMEOUT=seconds per solve
Usage: python3 minimize.py in.txt out.txt [K]
"""
import sys, itertools, os, subprocess, tempfile
import tm

def solve(order, ST, K):
    n = len(order); idx = {s: i for i, s in enumerate(order)}
    nsym = len(ST[order[0]])
    def tr(s, b):
        t = ST[s][b]
        if t is None: return None
        w, d, q = t
        return (w, d, idx.get(q, 'H'))
    incompat, implies = set(), {}
    for i, j in itertools.combinations(range(n), 2):
        bad, imp = False, []
        for b in range(nsym):
            a, c = tr(order[i], b), tr(order[j], b)
            if a is None or c is None: continue
            if a[:2] != c[:2] or (a[2] == 'H') != (c[2] == 'H'): bad = True; break
            if a[2] != 'H' and a[2] != c[2]: imp.append(tuple(sorted((a[2], c[2]))))
        if bad: incompat.add((i, j))
        else: implies[(i, j)] = imp
    top = [0]
    def nv(): top[0] += 1; return top[0]
    x = [[nv() for c in range(min(K, i + 1))] for i in range(n)]   # state i in class c (c <= i)
    clauses = []
    for i in range(n):                      # exactly one class (sequential counter for at-most-one)
        lits = x[i]; clauses.append(list(lits))
        s = [nv() for _ in lits]
        for k, l in enumerate(lits):
            clauses.append([-l, s[k]])
            if k: clauses += [[-s[k-1], s[k]], [-l, -s[k-1]]]
    for i, j in incompat:
        for c in range(min(len(x[i]), len(x[j]))):
            clauses.append([-x[i][c], -x[j][c]])
    yv = {}
    def y(p):                               # y(a,b): states a and b are in the same class
        if p not in yv:
            v = nv(); yv[p] = v; a, b = p
            if p in incompat: clauses.append([-v])
            for c in range(K):
                xa = x[a][c] if c < len(x[a]) else None
                xb = x[b][c] if c < len(x[b]) else None
                if xa and xb: clauses.append([-v, -xa, xb])
                elif xa: clauses.append([-v, -xa])
        return yv[p]
    for (i, j), imp in implies.items():
        for p in imp:
            v = y(p)
            for c in range(min(len(x[i]), len(x[j]))):
                clauses.append([-x[i][c], -x[j][c], v])
    fd, path = tempfile.mkstemp(suffix='.cnf')
    with os.fdopen(fd, 'w') as f:
        f.write(f'p cnf {top[0]} {len(clauses)}\n')
        for c in clauses: f.write(' '.join(map(str, c)) + ' 0\n')
    try:
        out = subprocess.run([SOLVER, path], capture_output=True, text=True, timeout=TIMEOUT).stdout
    except subprocess.TimeoutExpired:
        return 'timeout'
    finally:
        os.unlink(path)
    if 's UNSATISFIABLE' in out: return None
    assert 's SATISFIABLE' in out, out[-500:]
    m = set()
    for line in out.splitlines():
        if line.startswith('v '): m |= {int(l) for l in line[2:].split() if int(l) > 0}
    return [next(c for c in range(len(x[i])) if x[i][c] in m) for i in range(n)]

def build(order, ST, cls):
    ren = {}
    for c in cls: ren.setdefault(c, len(ren))     # compact class numbers, start state first
    cls = [ren[c] for c in cls]
    idx = {s: i for i, s in enumerate(order)}
    K = max(cls) + 1
    names = {}
    for i, s in enumerate(order):
        names.setdefault(cls[i], s)
    nsym = len(ST[order[0]])
    out = {names[c]: [None] * nsym for c in range(K)}
    for i, s in enumerate(order):
        for b, t in enumerate(ST[s]):
            if t is None: continue
            w, d, q = t
            q2 = names[cls[idx[q]]] if q in idx else q
            old = out[names[cls[i]]][b]
            assert old is None or old == (w, d, q2)
            out[names[cls[i]]][b] = (w, d, q2)
    new_order = [names[c] for c in range(K)]
    return new_order, out

def write(order, ST, path, note):
    L = [f'; {note}', f'; {len(order)} states, 2 symbols', '', 'blank_symbol: 0', '']
    for s in order:
        L.append(s)
        for b, t in enumerate(ST[s]):
            L.append('    -' if t is None else f'    {b} {t[0]} {t[1]} {t[2]}')
    open(path, 'w').write('\n'.join(L) + '\n')

TIMEOUT = int(os.environ.get("MIN_TIMEOUT", "600"))   # seconds per solve
SOLVER = os.environ.get("MIN_SOLVER", "kissat")
if __name__ == '__main__':
    order, ST, _ = tm.parse(open(sys.argv[1]).read())
    K = int(sys.argv[3]) if len(sys.argv) > 3 else len(order)
    while True:                           # descend: each solution gives a smaller target
        cls = solve(order, ST, K)
        print(K, {None: 'UNSAT', 'timeout': 'timeout'}.get(cls if not isinstance(cls, list) else 0, 'SAT'), flush=True)
        if not isinstance(cls, list): break
        o2, s2 = build(order, ST, cls)
        write(o2, s2, sys.argv[2], f'Minimised from {sys.argv[1]} by minimize.py')
        print('  found', len(o2), 'states', flush=True)
        K = len(o2) - 1
