"""Search merge sets (which single-parent DAG nodes are merged into their parent) minimising the
instruction count, by randomised local search.  usage: search.py D 1T SEEDS  -> configs/<D>.json
(the best found; carry set {1, T}).  Compare with the existing config before overwriting."""
import sys, random, time
import compiler as kz3
from compiler import *
def cost(dag,D,M,ctxs):
    try:
        m=Machine(dag,D,M,None,None,ctxs)
    except Machine.Bad:
        return None,None
    bd=m.breakdown()
    return m.count()-bd.get('boot',0)+(0 if m.pc_depth<=39 else 100), m
def optimize(dag,D,seed=0,passes=4,start=None,verbose=True):
    ctxs=contexts(dag)
    rc=Counter()
    for (a,b) in dag.nodes:
        for c in (a,b):
            if isinstance(c,int): rc[c]+=1
    cand=[n for n in range(len(dag.nodes)) if rc[n]==1]
    rnd=random.Random(seed)
    M=set(start or [])
    cur,_=cost(dag,D,M,ctxs)
    assert cur is not None
    for p in range(passes):
        order=list(cand); 
        if seed or p: rnd.shuffle(order)
        improved=False
        for n in order:
            M2=set(M); M2.symmetric_difference_update({n})
            c,_=cost(dag,D,M2,ctxs)
            if c is not None and c<cur or (c is not None and c==cur and rnd.random()<0.3):
                if c<cur: improved=True
                M,cur=M2,c
        if verbose: print(f'  D={D} seed={seed} pass {p}: {cur}', flush=True)
        if not improved and p>1: break
    return cur,M
if __name__=='__main__':
    D=int(sys.argv[1]); C=sys.argv[2]; seeds=int(sys.argv[3])
    kz3.CARRY={'T':{D-1},'1T':{1,D-1}}[C]
    dag=DAG(prologue=4)
    best=None
    for s in range(seeds):
        c,M=optimize(dag,D,seed=s)
        if best is None or c<best[0]:
            best=(c,sorted(M)); print('BEST',D,C,c,'seed',s,flush=True)
            import json; json.dump({'D':D,'C':C,'M':best[1],'cost':c},open(f'configs/{D}.json','w'))
