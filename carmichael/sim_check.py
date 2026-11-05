import sys, os, math
sys.path.insert(0, '../tools')
import tm, build

def phi(n): return sum(1 for k in range(n) if math.gcd(k, n) == 1)

def run(text, maxsteps=10**8, maxv=6, log=False):
    order, ST, _ = tm.parse(text)
    tape, h, q, steps = {}, 0, order[0], 0
    events = []
    while steps < maxsteps:
        b = tape.get(h, 0)
        if q not in ST: return 'halt', events, steps
        t = ST[q][b]
        assert t is not None, (q, b, steps)
        if q == 'RE2':
            # decode: V from h
            i = h; vs = []
            while not (tape.get(i, 0) == 1 and tape.get(i + 1, 0) == 0 and tape.get(i + 2, 0) == 0): vs.append(tape.get(i, 0)); i += 1
            v = len(vs) - 1
            # f at i+3, B from i+5
            f = tape.get(i + 3, 0)
            j = i + 5; bs = []
            while not (tape.get(j, 0) == 1 and tape.get(j + 1, 0) == 0 and tape.get(j + 2, 0) == 0): bs.append(tape.get(j, 0)); j += 1
            s = len(bs)
            # K/R to the left: h-1, h-2 sep; R slots; R start; sep; K
            j = h - 3; r = 0
            while not (tape.get(j, 0) == 1 and tape.get(j - 1, 0) == 0 and tape.get(j - 2, 0) == 0): r += 1; j -= 1
            j -= 3; k = 0
            while not (tape.get(j, 0) == 1 and tape.get(j - 1, 0) == 0 and tape.get(j - 2, 0) == 0): k += 1; j -= 1
            M = k + r
            c = phi(M)
            want = [1] * (v + 1)
            if c <= v: want[v - c] = 0
            assert vs == want, (steps, v, M, vs, want)
            assert r == 1, (k, r)
            events.append((v, M, s, f, bs.count(0), bs.index(0) if 0 in bs else None))
            if v > maxv: return 'ok', events, steps
        tape[h] = t[0]; h += 1 if t[1] == 'R' else -1; q = t[2]; steps += 1
    return 'steps', events, steps

if __name__ == '__main__':
    st, ev, steps = run(build.build(), maxv=int(sys.argv[1]) if len(sys.argv) > 1 else 4)
    print(st, steps, len(ev))
    cur = None
    for e in ev:
        if e[0] != cur:
            cur = e[0]; print('v', e[0], 's', e[2], 'first M', e[1])
    print(ev[-3:])

def summary(ev):
    out = {}
    for v, M, s, f, nh, pos in ev:
        out.setdefault(v, []).append((M, f))
    return out

def check_events(ev):
    """the rounds of each v: M = 2, 3, ... up to the second match or s + 1"""
    by = {}
    for v, M, s, f, nh, pos in ev: by.setdefault(v, []).append((M, s, f))
    vs = sorted(by)
    for v in vs[:-1]:
        Ms = [m for m, _, _ in by[v]]; s = by[v][0][1]
        assert Ms == list(range(2, Ms[-1] + 1)), v
        matches = [m for m in Ms if phi(m) == v]
        if len(matches) >= 2: assert Ms[-1] == matches[1], (v, Ms[-1], matches)
        else: assert Ms[-1] == s + 1 and len(matches) == 0, (v, Ms[-1], s)
        assert s + 1 >= 2 * v * v
    return True
