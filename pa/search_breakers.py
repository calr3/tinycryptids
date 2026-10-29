"""Greedy search for breaker nodes (tmbuilder.insert_breakers): repeatedly add the DAG node
whose breaker lowers the state count most.   python3 search_breakers.py [key=value ...]"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import program

KW = {}
for a in sys.argv[1:]:
    k, v = a.split('=', 1)
    KW[k] = v if k in ('vchain', 'order') else eval(v)

def size(br):
    return program.build(breakers=tuple(br), **KW).state_count()

b = program.build(**KW)
names = sorted({b.sequences[i].name for i in b.reachable() if b.sequences[i].name})
cur, curv = [], size([])
print('start', curv, 'run', b.max_zero_run(), len(names), 'candidates', flush=True)
while True:
    best = None
    for n in names:
        if n in cur:
            continue
        v = size(cur + [n])
        if best is None or v < best[0]:
            best = (v, n)
    if best is None or best[0] >= curv:
        break
    cur.append(best[1]); curv = best[0]
    print(curv, cur, flush=True)
print('best', curv, cur)
