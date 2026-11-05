import sys; sys.path.insert(0,'../tools'); import build
def run(steps, show=None, start=None, tape=None, head=0):
    build.build() if not build.ST else None
    t = dict(enumerate(tape or '')) ; t = {i:int(c) for i,c in t.items()}
    q = start or build.ORDER[0]; h = head
    for s in range(steps):
        b = t.get(h,0); tr = build.ST[q][b]
        if tr is None: print('HALT', q, b, s); return q,h,t
        if show and (q in show):
            lo, hi = min(k for k in t if t[k] or k==h), max(max(k for k in t if t[k]),h)
            print(s, q, ''.join(('[%d]'%t.get(i,0)) if i==h else str(t.get(i,0)) for i in range(lo-1,hi+2)))
        t[h] = tr[0]; h += 1 if tr[1]=='R' else -1; q = tr[2]
    return q,h,t
if __name__ == '__main__':
    build.build()
    run(int(sys.argv[1]), set(sys.argv[2].split(',')))
