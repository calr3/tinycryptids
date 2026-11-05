"""Compare every square check (state k3: pass on 0, fail on 1) and every tuple end with an
abstract model of the search, from the blank tape."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm, build

def v(L): return L // 2 - 1
def issq(n): r = int(n ** 0.5); return any(x * x == n for x in range(max(r - 2, 0), r + 3))

def nxt(t):  # NEXCOM on (A, B, C) lengths, A free; m = 4
    a, b, c = t
    if a > 4: return (a - 1, b + 1, c)
    if b > 4: return (b - 1, 4, c + 1)
    return (c + 1, 4, 4)

def model(t, events):
    q = [t[0], t[1], t[2], 3]; S = 0; W = 0; pos = 0
    events.append(True)   # the check at the tuple start (S fresh), W 2 -> 0
    while True:
        S += v(q[pos]) ** 2
        ok = issq(S); events.append(ok)
        if not ok: return False
        W = (W + 1) % 3
        if W == 0: S = 0
        pos += 1
        if pos == 4:
            pos = 0
            if W == 0: return True

def machine_events(nsteps):
    order, states, _ = tm.parse(build.build())
    idx = {s: i for i, s in enumerate(order)}
    tab = [states[s] for s in order]
    T = {}; hd = 0; q = order[0]; ev = []; tuples = 0
    for _ in range(nsteps):
        sym = T.get(hd, 0)
        if q == 'k3': ev.append(sym == 0)
        if q == 'ea0': tuples += 1
        t = states[q][sym]
        if t is None: raise SystemExit(f'undefined {q} {sym}')
        T[hd] = t[0]; hd += 1 if t[1] == 'R' else -1; q = t[2]
        if q not in states: raise SystemExit('halted!')
    return ev, tuples

if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3 * 10**6
    ev, tuples = machine_events(n)
    mev = []; t = (4, 4, 4); seen = 0
    while len(mev) < len(ev) + 50:
        assert not model(t, mev), t
        t = nxt(t); seen += 1
    assert mev[:len(ev)] == ev, next(i for i in range(len(ev)) if mev[i] != ev[i])
    print('ok:', len(ev), 'checks agree,', tuples, 'tuples done by the machine')
