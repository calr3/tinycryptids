"""SAT synthesis of the non-loop part of a machine (brute-force design search).

A design's run alternates between a fixed loop (e.g. a mod walk) and the rest (the round
end: checks, shifts, rebuilds). This keeps the loop's states and transitions, replaces
everything else by k free states with unknown transitions, and asks a SAT solver for a
table that reproduces every round of the design: for each round, starting from the
design's configuration when it leaves the loop, the new machine must reach the design's
configuration when it re-enters the loop, within a step bound, taking the beep
transition (if any) exactly as often as the design does in that round.

  python3 synth_round.py design.txt out.txt --fixed B2,Y1,Y2,A2,W1,Z1,Z2 \
      --leave B2:0 --enter B2:1 --k 7 --rounds 33 [--beep G0:0] [--slack 4|-1]
      [--merge W2:A2] [--solver kissat404] [--timeout 3600]

* `--fixed`: the loop's states (their rows are kept, except the `--leave` row, which is
  free: where the loop hands over).
* `--leave S:b`: a round starts when the design is in state S reading b.
* `--enter S:b`: it ends when the design enters S, from a state outside the loop, reading b.
* `--merge X:Y`: before fixing, fold design state X into Y (X's defined rows must agree
  with Y's; a merged pair of the loop, e.g. the wrap's last state into the D step).
* `--beep S:b`: the beep transition of a beeping design; the synthesized beep is free
  state N0 reading b, taken exactly as often per round as the design's.
* `--slack`: extra steps per round over the design's own length; -1 allows 2 n + 10.

Free states N1.. are first visited in index order (symmetry breaking), so UNSAT for k is
a proof that no k-state round end fits within the step bounds. A SAT answer only fits the
rounds given: simulate the result before trusting it. Needs python-sat.
"""
import sys, argparse, threading, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tm
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType

class Enc:
    def __init__(self): self.top = 0; self.cl = []
    def v(self): self.top += 1; return self.top
    def card(self, lits, k, eq):
        f = CardEnc.equals if eq else CardEnc.atmost
        e = f(lits=lits, bound=k, top_id=self.top, encoding=EncType.seqcounter)
        self.top = max(self.top, e.nv); self.cl += e.clauses

def rounds(order, ST, leave, enter, fixed, beep, nmax, maxsteps=10**8):
    """Rounds of the design's run from a blank tape: (tape, head, end tape, end head,
    length, beeps); tapes as dicts restricted to the visited window."""
    tape, head, q, prev = {}, 0, order[0], None
    out, cur, nb = [], None, 0
    for step in range(maxsteps):
        b = tape.get(head, 0)
        if cur is not None and q == enter[0] and b == enter[1] and prev not in fixed:
            out.append(dict(cur, out={k: v for k, v in tape.items() if v}, out_head=head,
                            len=step - cur['step'], nbeep=nb))
            cur = None
            if len(out) >= nmax: break
        if cur is None and (q, b) == leave:
            cur = dict(inp={k: v for k, v in tape.items() if v}, head=head, step=step); nb = 0
        if beep and (q, b) == beep: nb += 1
        t = ST[q][b]
        assert t is not None, ('the design halts', q, b)
        w, d, q2 = t
        tape[head] = w; head += 1 if d == 'R' else -1; prev, q = q, q2
    return out

def synth(ST, fixed, leave, rs, k, beep, slack=4, solver='kissat404', timeout=3600):
    names = list(fixed) + [f'N{i}' for i in range(k)]
    nq = len(names); idx = {s: i for i, s in enumerate(names)}
    E = Enc()
    frows = [(idx[n], b) for n in names for b in range(2)
             if n not in fixed or (n, b) == leave]
    FW = {r: E.v() for r in frows}; FM = {r: E.v() for r in frows}
    FN = {r: [E.v() for _ in range(nq)] for r in frows}
    for r in frows: E.card(FN[r], 1, True)
    bq = idx['N0'] if beep else None
    allS = []
    for R in rs:
        cells = set(R['inp']) | set(R['out']) | {R['head'], R['out_head']}
        lo, hi = min(cells) - 2, max(cells) + 3   # the nonzero cells, the heads, and a margin
        Wn = hi - lo
        T = R['len'] + slack if slack >= 0 else 2 * R['len'] + 10
        S = [[E.v() for _ in range(nq)] for _ in range(T + 1)]; allS.append(S)
        H = [[E.v() for _ in range(Wn)] for _ in range(T + 1)]
        Tp = [[E.v() for _ in range(Wn)] for _ in range(T + 1)]
        sym = [E.v() for _ in range(T)]; wr = [E.v() for _ in range(T)]; mv = [E.v() for _ in range(T)]
        q0 = idx[leave[0]]
        for q in range(nq): E.cl.append([S[0][q]] if q == q0 else [-S[0][q]])
        for h in range(Wn):
            E.cl.append([H[0][h]] if h == R['head'] - lo else [-H[0][h]])
            E.cl.append([Tp[0][h]] if R['inp'].get(h + lo, 0) else [-Tp[0][h]])
        for t in range(T + 1): E.card(S[t], 1, True); E.card(H[t], 1, True)
        beeps = []
        for t in range(T):
            for h in range(Wn):
                E.cl += [[-H[t][h], -Tp[t][h], sym[t]], [-H[t][h], Tp[t][h], -sym[t]],
                         [-H[t][h], -wr[t], Tp[t + 1][h]], [-H[t][h], wr[t], -Tp[t + 1][h]],
                         [H[t][h], -Tp[t][h], Tp[t + 1][h]], [H[t][h], Tp[t][h], -Tp[t + 1][h]]]
                E.cl.append([-H[t][h], -mv[t], H[t + 1][h + 1]] if h + 1 < Wn else [-H[t][h], -mv[t]])
                E.cl.append([-H[t][h], mv[t], H[t + 1][h - 1]] if h >= 1 else [-H[t][h], mv[t]])
            for q in range(nq):
                for b in range(2):
                    sl = sym[t] if b else -sym[t]
                    if (q, b) in FW:
                        fw, fm, fn = FW[(q, b)], FM[(q, b)], FN[(q, b)]
                        E.cl += [[-S[t][q], -sl, -fw, wr[t]], [-S[t][q], -sl, fw, -wr[t]],
                                 [-S[t][q], -sl, -fm, mv[t]], [-S[t][q], -sl, fm, -mv[t]]]
                        for j in range(nq): E.cl.append([-S[t][q], -sl, -fn[j], S[t + 1][j]])
                    else:
                        tr = ST[names[q]][b]
                        if tr is None: E.cl.append([-S[t][q], -sl]); continue
                        w, d, n = tr
                        E.cl += [[-S[t][q], -sl, wr[t] if w else -wr[t]],
                                 [-S[t][q], -sl, mv[t] if d == 'R' else -mv[t]],
                                 [-S[t][q], -sl, S[t + 1][idx[n]]]]
            if beep:
                v = E.v(); beeps.append(v)
                bl = sym[t] if beep[1] else -sym[t]
                E.cl += [[-v, S[t][bq]], [-v, bl], [v, -S[t][bq], -bl]]
        # reach the end configuration at some step; count beeps before it
        oq = idx[R['enter']]
        reach = []
        for t in range(T + 1):
            r = E.v(); reach.append(r)
            E.cl += [[-r, S[t][oq]], [-r, H[t][R['out_head'] - lo]]]
            for h in range(Wn): E.cl.append([-r, Tp[t][h] if R['out'].get(h + lo, 0) else -Tp[t][h]])
        E.cl.append(reach)
        if beep:
            done = [E.v() for _ in range(T + 1)]
            E.cl += [[-done[0], reach[0]], [done[0], -reach[0]]]
            for t in range(1, T + 1):
                E.cl += [[-done[t], done[t - 1], reach[t]], [done[t], -done[t - 1]], [done[t], -reach[t]]]
            pre = []
            for t in range(T):
                p = E.v(); pre.append(p)
                E.cl += [[-p, beeps[t]], [-p, -done[t]], [p, -beeps[t], done[t]]]
            if R['nbeep'] == 0:
                for p in pre: E.cl.append([-p])
            else:
                E.card(pre, R['nbeep'], False)
                E.cl.append(pre[:])       # (nbeep <= 1 in practice)
    # symmetry breaking: free states N1.. first visited in index order
    free = [idx[f'N{i}'] for i in range(1 if beep else 0, k)]
    seen = {q: None for q in free}
    for S in allS:
        for row in S:
            new = {}
            for q in free:
                v = E.v(); new[q] = v; p = seen[q]
                E.cl += [[-v, row[q]], [v, -row[q]]] if p is None else [[-v, p, row[q]], [v, -p], [v, -row[q]]]
            for a, b in zip(free, free[1:]):
                c = [-row[b]] + ([seen[b]] if seen[b] is not None else []) + ([seen[a]] if seen[a] is not None else [])
                E.cl.append(c)
            seen = new
    s = Solver(name=solver, bootstrap_with=E.cl)
    timer = threading.Timer(timeout, s.interrupt); timer.start()
    res = s.solve_limited(expect_interrupt=True); timer.cancel()
    if res is None: return 'timeout'
    if not res: return None
    m = set(l for l in s.get_model() if l > 0)
    table = {n: list(ST[n]) if n in fixed else [None, None] for n in names}
    for (q, b) in frows:
        j = next(j for j in range(nq) if FN[(q, b)][j] in m)
        table[names[q]][b] = (1 if FW[(q, b)] in m else 0, 'R' if FM[(q, b)] in m else 'L', names[j])
    return names, table

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('design'); ap.add_argument('out')
    ap.add_argument('--fixed', required=True); ap.add_argument('--leave', required=True)
    ap.add_argument('--enter', required=True); ap.add_argument('--k', type=int, required=True)
    ap.add_argument('--rounds', type=int, default=33); ap.add_argument('--beep')
    ap.add_argument('--merge', default=''); ap.add_argument('--slack', type=int, default=4)
    ap.add_argument('--solver', default='kissat404'); ap.add_argument('--timeout', type=int, default=3600)
    a = ap.parse_args()
    order, ST, _ = tm.parse(open(a.design).read())
    sb = lambda x: (x.split(':')[0], int(x.split(':')[1]))
    leave, enter = sb(a.leave), sb(a.enter)
    beep = sb(a.beep) if a.beep else None
    fixed = a.fixed.split(',')
    rs = rounds(order, ST, leave, enter, set(fixed), beep, a.rounds)
    for R in rs: R['enter'] = enter[0]
    ST2 = {n: list(ST[n]) for n in ST}
    for pair in filter(None, a.merge.split(',')):
        x, y = pair.split(':')
        for b in range(2):
            if ST2[x][b] is not None:
                assert ST2[y][b] in (None, ST2[x][b]), (x, y, b)
                ST2[y][b] = ST2[x][b]
        for n in ST2:
            ST2[n] = [None if t is None else (t[0], t[1], y if t[2] == x else t[2]) for t in ST2[n]]
    print(f'{len(rs)} rounds (longest {max(R["len"] for R in rs)} steps), k = {a.k}', flush=True)
    r = synth(ST2, fixed, leave, rs, a.k, beep, a.slack, a.solver, a.timeout)
    if not isinstance(r, tuple):
        print('UNSAT' if r is None else 'timeout'); return
    names, table = r
    L = [f'; Synthesized by synth_round.py from {a.design}: {len(fixed)} fixed + {a.k} free states',
         '; (the start state is not synthesized: try each state on a blank tape)', '', 'blank_symbol: 0', '']
    for n in names:
        L.append(n)
        for b, t in enumerate(table[n]):
            L.append('    -' if t is None else f'    {b} {t[0]} {t[1]} {t[2]}')
    open(a.out, 'w').write('\n'.join(L) + '\n')
    print('SAT: written', a.out)

if __name__ == '__main__':
    main()
