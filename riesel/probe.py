"""Probe the design's checkpoint tapes: t1 (step to a new k) and a6 (before the mod walk)."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm

def runs(t, h):
    """run-length encoding of the tape around the head: returns list and head cell index"""
    s = t
    i = 0
    out = []
    idx = 0
    while i < len(s):
        j = i
        while j < len(s) and s[j] == s[i]: j += 1
        if h < i:
            out.append((s[i], j - i, 'L', i))
        elif i <= h < j:
            out.append((s[i], j - i, 'H', h - i))
        else:
            out.append((s[i], j - i, 'R', i))
        i = j
    return out

def show(tag, order, ST, maxsteps, maxtrace=200):
    for st in ('t1', 'a6'):
        r = tm.run(order, ST, maxsteps=maxsteps, trace=st, maxtrace=maxtrace)
        print('==', tag, st, r[0], r[1])
        prev = None
        for t in r[5][:12]:
            if t == prev: continue
            prev = t
            s = t.strip('0')
            print('   ', runs(s, max(0, min(len(s) - 1, 0))))

if __name__ == '__main__':
    order, ST, _ = tm.parse(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'riesel.txt')).read())
    # trace gives the tape at entry to the state, with the head inside; recompute head from sim? tape only.
    r = tm.run(order, ST, maxsteps=2 * 10**4, trace='t1', maxtrace=200)
    print('status', r[0], r[1], 'state', r[2], 'head', r[3])
    prev = None
    for t in r[5][:6]:
        if t == prev: continue
        prev = t
        print(repr(t))
