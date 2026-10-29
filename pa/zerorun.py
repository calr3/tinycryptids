"""Longest runs of 0 bits (car descents) on decision-DAG paths: these set the dispatch size."""
import os, sys, functools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import program

def runs(b, top=5):
    seqs = b.sequences
    out = []
    def name(v):
        return seqs[v].name or f'#{v}' if isinstance(v, int) else str(v)
    @functools.lru_cache(None)
    def longest(v):
        # longest chain of car descents starting at v: (length, names)
        if not isinstance(v, int):
            return (0, (name(v),))
        n, p = longest(seqs[v].seq[0])
        return (n + 1, (name(v),) + p)
    for i in b.reachable():
        n, p = longest(i)
        out.append((n, p))
    out.sort(key=lambda x: -x[0])
    seen, res = set(), []
    for n, p in out:
        if p[1:] and any(p[k:] == q[1][-len(p[k:]):] for q in res for k in range(1)):
            pass
        if p in seen: continue
        seen.add(p); res.append((n, p))
    return res[:top]

if __name__ == '__main__':
    kw = dict(a.split('=') for a in sys.argv[1:])
    b = program.build(**kw)
    print(b.state_count(), 'max run', b.max_zero_run())
    for n, p in runs(b, 6):
        print(n, ' > '.join(p))
