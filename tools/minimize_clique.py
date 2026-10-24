"""Exact minimisation of a TM with unused (undefined) transitions, with symmetry breaking.

Same merge rule as minimize.py: two states may share a class if, on every symbol where
both are defined, they write the same symbol, move the same way, and go to states in a
common class (halting targets must match exactly).  Differences:

* incompatibility is propagated first (a pair whose merge forces an incompatible pair is
  incompatible);
* a maximum clique of pairwise incompatible states is a lower bound on the number of
  classes, and its states are pinned to classes 0, 1, ... (classes are interchangeable),
  which removes most of the symmetry the SAT solver would otherwise explore;
* the search goes UP from the lower bound: K = LB, LB + 1, ... until satisfiable, so the
  first solution found is optimal (every smaller K was proven unsatisfiable).

On the odd perfect designs this proves optimality in seconds where minimize.py (which
descends from K) ran for hours without an answer.
Usage: python3 minimize_clique.py in.txt out.txt [timeout_per_K_seconds] [solver]
Needs python-sat and networkx (pip install python-sat networkx).
"""
import sys, itertools, threading
import tm
from minimize import build, write
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
import networkx as nx

def analyse(order, ST):
    n = len(order); idx = {s: i for i, s in enumerate(order)}
    nsym = len(ST[order[0]])
    def tr(s, b):
        t = ST[s][b]
        if t is None: return None
        w, d, q = t
        return (w, d, idx.get(q, 'H:' + q))
    incompat, implies = set(), {}
    for i, j in itertools.combinations(range(n), 2):
        bad, imp = False, []
        for b in range(nsym):
            a, c = tr(order[i], b), tr(order[j], b)
            if a is None or c is None: continue
            if a[:2] != c[:2]: bad = True; break
            ha, hc = isinstance(a[2], str), isinstance(c[2], str)
            if ha or hc:
                if a[2] != c[2]: bad = True; break
            elif a[2] != c[2]: imp.append(tuple(sorted((a[2], c[2]))))
        if bad: incompat.add((i, j))
        else: implies[(i, j)] = imp
    changed = True
    while changed:
        changed = False
        for p, imp in list(implies.items()):
            if any(q in incompat for q in imp):
                incompat.add(p); del implies[p]; changed = True
    return n, incompat, implies

def lower_bound(order, ST):
    n, incompat, _ = analyse(order, ST)
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(incompat)
    return nx.max_weight_clique(G, weight=None)[0]

def solve(order, ST, K, solver='cadical195', timeout=3600, clique=None):
    n, incompat, implies = analyse(order, ST)
    if clique is None: clique = lower_bound(order, ST)
    if len(clique) > K: return None
    pin = {v: c for c, v in enumerate(clique)}
    top = [0]
    def nv(): top[0] += 1; return top[0]
    x = [[nv() for c in range(K)] for i in range(n)]
    cl = []
    for i in range(n):
        enc = CardEnc.equals(lits=x[i], bound=1, top_id=top[0], encoding=EncType.seqcounter)
        top[0] = max(top[0], enc.nv); cl += enc.clauses
        if i in pin: cl.append([x[i][pin[i]]])
    for i, j in incompat:
        for c in range(K): cl.append([-x[i][c], -x[j][c]])
    yv = {}
    def y(p):
        if p not in yv:
            v = nv(); yv[p] = v; a, b = p
            if p in incompat: cl.append([-v])
            for c in range(K):
                cl.append([-v, -x[a][c], x[b][c]]); cl.append([-v, -x[b][c], x[a][c]])
        return yv[p]
    for (i, j), imp in implies.items():
        for p in imp:
            v = y(p)
            for c in range(K): cl.append([-x[i][c], -x[j][c], v])
    s = Solver(name=solver, bootstrap_with=cl)
    timer = threading.Timer(timeout, s.interrupt); timer.start()
    r = s.solve_limited(expect_interrupt=True); timer.cancel()
    if r is None: return 'timeout'
    if not r: return None
    m = set(l for l in s.get_model() if l > 0)
    cls = [next(c for c in range(K) if x[i][c] in m) for i in range(n)]
    c0 = cls[0]                               # the start state's class first
    return [0 if c == c0 else (c0 if c == 0 else c) for c in cls]

if __name__ == '__main__':
    order, ST, _ = tm.parse(open(sys.argv[1]).read())
    timeout = int(sys.argv[3]) if len(sys.argv) > 3 else 3600
    solver = sys.argv[4] if len(sys.argv) > 4 else 'cadical195'
    clique = lower_bound(order, ST)
    print('design', len(order), 'states; clique lower bound', len(clique), flush=True)
    K = len(clique)
    while True:
        cls = solve(order, ST, K, solver, timeout, clique)
        if isinstance(cls, list):
            o2, s2 = build(order, ST, cls)
            write(o2, s2, sys.argv[2], f'Minimised from {sys.argv[1]} by minimize_clique.py')
            print(K, 'SAT: optimum', len(o2), 'states', flush=True)
            break
        print(K, 'UNSAT' if cls is None else 'timeout (optimality not proven)', flush=True)
        K += 1
