"""D-ary compiler for k215P with relative control (second version).

Uses kzf.DAG (binary DAG of the program, relative hash-consing).  A merge set M (DAG nodes
merged into their single parent) defines the D-ary nodes.  Control leaves may target merged
nodes: a continue then rewrites the holding node's cell to the target's first slot, a break
to the slot after the target (or finishes the holding node when the target ends it).

C(pc, regs): state = root node, head on cell 0,
    ... 0 [digits of pc's slot path] 1^(G - len) [SEP 1^r] ... (registers in reg_order)
"""
import sys, random, collections
from collections import defaultdict, Counter
from program import DAG, P, NP, FRESH, first_use_order, is_op, is_dec

sys.setrecursionlimit(100000)


def is_ctl(s):
    return isinstance(s, tuple) and s[0] in ('brk', 'cnt', 'halt')


class Layout:
    def __init__(self, dag, D, merged):
        self.dag, self.D, self.T, self.M = dag, D, D - 1, set(merged)
        self._sz = {}

    def size(self, c):
        """number of slots c takes in its holder"""
        if isinstance(c, int) and c in self.M:
            if c not in self._sz:
                a, b = self.dag.nodes[c]
                self._sz[c] = self.size(a) + self.size(b)
            return self._sz[c]
        return 1

    def slots(self, n):
        out = []
        for c in self.dag.nodes[n]:
            if isinstance(c, int) and c in self.M:
                out += self.slots(c)
            else:
                out.append(c)
        return out

    def resolve(self, bits):
        """kp = [[K, j]], the leaf, and for every DAG node on the path (n -> (kp index, start))"""
        path, leaf = self.dag.walk(bits)
        kp, where = [], {}
        cur, off = None, 0
        for n, b in path:
            if n not in self.M:
                kp.append([n, None])
                cur, off = len(kp) - 1, 0
            where[n] = (cur, off)
            car = self.dag.nodes[n][0]
            if b == 1:
                off += self.size(car)
            ch = self.dag.nodes[n][b]
            if not (isinstance(ch, int) and ch in self.M):
                kp[cur][1] = off
        return kp, leaf, path, where


CARRY = None     # set of carry values (None: {T})
_amemo = {}


def assign(sl, D, C):
    """Optimal slot values for a node.  Returns (e, wr, cost) or None: e[j] the value slot j is
    entered at, wr[j] what its transition writes (the inside value of a child slot, the marker
    of an op), cost = transitions.  adv/retok: a value in C carries (the node is done), any
    other value v becomes v + 1."""
    T = D - 1
    kinds = tuple('n' if isinstance(c, int) else 'o' if is_op(c) else 'c' for c in sl)
    key = (kinds, D, tuple(sorted(C)))
    if key in _amemo:
        return _amemo[key]
    m = len(kinds)
    best = [None]
    if m > D:
        _amemo[key] = None
        return None
    from functools import lru_cache

    @lru_cache(maxsize=None)
    def go(j, e, used):
        # used: bitmask of values read by the node so far (e included)
        k = kinds[j]
        last = j == m - 1
        opts = []
        if k == 'n':
            for i in range(0, T + 1):
                if last != (i in C):
                    continue
                if i != e and (used >> i) & 1:
                    continue
                u = used | (1 << i)
                extra = 0 if i == e else 1
                if last:
                    opts.append((1 + extra, (i,), None))
                else:
                    ne = i + 1
                    if ne > T or (u >> ne) & 1:
                        continue
                    r = go(j + 1, ne, u | (1 << ne))
                    if r is not None:
                        opts.append((1 + extra + r[0], (i,) , r))
        elif k == 'o':
            if last:
                for w in range(1, T + 1):
                    if (used >> w) & 1:
                        continue
                    opts.append((2, (w,), None))
                    break
            else:
                for w in range(1, T + 1):
                    if (used >> w) & 1:
                        continue
                    r = go(j + 1, w, used | (1 << w))
                    if r is not None:
                        opts.append((1 + r[0], (w,), r))
        else:
            if last:
                opts.append((1, (None,), None))
            else:
                for ne in range(0, T + 1):
                    if (used >> ne) & 1:
                        continue
                    r = go(j + 1, ne, used | (1 << ne))
                    if r is not None:
                        opts.append((1 + r[0], (None,), r))
                        break
        if not opts:
            return None
        return min(opts, key=lambda x: x[0])
    r = go(0, 0, 1)
    if r is None:
        _amemo[key] = None
        return None
    cost = r[0]
    e, wr = [], []
    v, node = 0, r
    j = 0
    while node is not None:
        e.append(v)
        wr.append(node[1][0])
        nxt = node[2]
        if nxt is None:
            break
        # recover the next entry value
        k = kinds[j]
        if k == 'n':
            v = node[1][0] + 1
        elif k == 'o':
            v = node[1][0]
        else:
            # the first unused value (as chosen)
            used = set(e) | {w for w, kk in zip(wr, kinds) if kk == 'n' and w is not None}
            v = next(x for x in range(T + 1) if x not in used)
        node = nxt
        j += 1
    out = (e, wr, cost)
    _amemo[key] = out
    return out


def values(sl, D):
    """pa_nsymbols/kary.py's slot values: (vals, writes, skip) or None"""
    T, m = D - 1, len(sl)
    if m > D:
        return None
    completes = not is_ctl(sl[-1])
    ops = [j for j, c in enumerate(sl) if is_op(c)]
    jstar = ops[-1] if ops and completes else None

    def run(low):
        vals, writes, v = [], [], 0
        for j, c in enumerate(sl):
            vals.append(v)
            if is_op(c):
                w = max(v, 1)
                if j == jstar and low is not None:
                    if low < w:
                        return None
                    w = low
                writes.append(w)
            else:
                writes.append(v)
            v = writes[-1] + 1
        return vals, writes
    if jstar is not None:
        r = run(T - (m - 1 - jstar))
        if r and max(r[0]) <= T and max(r[1]) <= T:
            return r[0], r[1], None
    r = run(None)
    if r is None:
        return None
    vals, writes = r
    if not completes or (vals[-1] == T and writes[-1] == T):
        return (vals, writes, None) if max(vals + writes) <= T else None
    if is_op(sl[-1]):
        writes[-1] = T
        return (vals, writes, None) if max(vals) <= T else None
    if vals[-1] >= T:
        return None
    skip = vals[-1]
    vals[-1] = writes[-1] = T
    return vals, writes, skip


def contexts(dag):
    out = list(dag.synth)
    for pc in range(NP):
        bits = dag.pc_ir[pc]
        out.append(bits)
        if dag.leaf_kind[pc][0] == 'decX':
            out.append(bits[:-1] + (1,))
            out.append(bits[:-2] + (1,))
    return out


class Machine:
    """Build the TM for a merge set; raises Bad(node) when the merge set is inconsistent."""
    class Bad(Exception):
        pass

    def __init__(self, dag, D, merged, reg_order=None, boot=None, ctxs=None):
        self.dag, self.D, self.T, self.SEP = dag, D, D - 1, D + 1
        L = self.L = Layout(dag, D, merged)
        M = L.M
        # kary nodes reachable from the root
        reach, st = [], [dag.root]
        seen = set()
        while st:
            n = st.pop()
            if n in seen:
                continue
            seen.add(n)
            reach.append(n)
            for c in L.slots(n):
                if isinstance(c, int):
                    st.append(c)
        self.knodes = sorted(reach)
        self.slots = {n: L.slots(n) for n in self.knodes}
        self.val = {}
        C = CARRY if CARRY is not None else {D - 1}
        self.C = C
        for n in self.knodes:
            v = assign(self.slots[n], D, C)
            if v is None:
                raise Machine.Bad(('fit', n))
            self.val[n] = v
        # controls, per context
        self.ctl = {}                  # (K, j) -> (kind, mode, h); mode None or jump value t
        self.levels = defaultdict(set)  # (kind, mode, e) -> values read at that level
        self.pc_tape = {}
        ctxs = ctxs or contexts(dag)
        ctlpath = {}
        for bits in ctxs:
            kp, leaf, path, where = L.resolve(bits)
            if isinstance(leaf, tuple) and leaf[0] in ('brk', 'cnt'):
                kind, k = leaf
                chain = [n for n, _ in path]
                A = chain[len(chain) - k]
                ti, start = where[A]
                Kt = kp[ti][0]
                if A not in M:
                    mode = None
                else:
                    if kind == 'cnt':
                        mode = self.val[Kt][0][start] if start > 0 else None
                    else:
                        e = start + L.size(A)
                        mode = None if e == len(self.slots[Kt]) else self.val[Kt][0][e]
                h = len(kp) - 1 - ti
                key = (kp[-1][0], kp[-1][1])
                v = (kind, mode, h)
                if key in self.ctl and self.ctl[key] != v:
                    for n, _ in list(reversed(path)) + list(reversed(ctlpath[key])):
                        if n in M:
                            raise Machine.Bad(('ctl', n))
                    raise AssertionError('control clash with nothing merged')
                self.ctl[key] = v
                ctlpath.setdefault(key, path)
                for e in range(h, 0, -1):
                    K, j = kp[len(kp) - 2 - h + e]
                    self.levels[(kind, mode, e)].add(self.val[K][1][j])
            if is_dec(leaf):
                # a failed decnz finishes its kary node: its trie parent must end that node
                for idx in range(len(path) - 1, 0, -1):
                    n, b = path[idx]
                    if n not in M:
                        break
                    if path[idx - 1][1] != 1:
                        raise Machine.Bad(('dec', n))
        for pc in range(NP):
            kp, leaf, _, _ = L.resolve(dag.pc_ir[pc])
            self.pc_tape[pc] = [self.val[K][1][j] for K, j in kp[:-1]] + [self.val[kp[-1][0]][0][kp[-1][1]]]
        self.pc_depth = max(len(t) for t in self.pc_tape.values())
        self.reg_order = reg_order or first_use_order()
        self.emit(boot)

    def emit(self, boot):
        D, T, SEP = self.D, self.T, self.SEP
        sym = lambda v: v + 1
        regno = {r: k for k, r in enumerate(self.reg_order)}
        tm = {}

        def put(q, r, w, d, n):
            assert (q, r) not in tm, (q, r)
            tm[(q, r)] = (w, d, n)
        name = lambda n: f'n{n}'

        def ctlstate(kind, mode, e):
            if e == 0:
                return ('adv' if kind == 'brk' else 'scan') if mode is None else None
            return f'e{kind}{e}' if mode is None else f'j{mode}_{e}'
        for n in self.knodes:
            q = name(n)
            vals, writes, _ = self.val[n]
            for j, (c, v, w) in enumerate(zip(self.slots[n], vals, writes)):
                if isinstance(c, int):
                    put(q, sym(v), sym(w), 'R', name(c))
                    if w != v:
                        put(q, sym(w), sym(w), 'R', name(c))
                elif c[0] in ('inc', 'dec'):
                    put(q, sym(v), sym(w), 'R', f'c{c[0]}{regno[c[1]] + 1}')
                    if j == len(self.slots[n]) - 1:
                        put(q, sym(w), FRESH, 'L', 'adv')
                elif c[0] == 'halt':
                    put(q, sym(v), sym(v), 'R', 'halt')
                else:
                    kind, mode, h = self.ctl[(n, j)]
                    if h == 0 and mode is not None:
                        put(q, sym(v), sym(mode), 'L', 'scan')
                    else:
                        put(q, sym(v), FRESH, 'L', ctlstate(kind, mode, h))
        for (kind, mode, e), vs in sorted(self.levels.items(), key=str):
            for v in sorted(vs):
                if mode is not None and e == 1:
                    put(f'j{mode}_1', sym(v), sym(mode), 'L', 'scan')
                else:
                    put(ctlstate(kind, mode, e), sym(v), FRESH, 'L', ctlstate(kind, mode, e - 1))
        adv_vals, W, Wdec = set(), set(), set()
        for n in self.knodes:
            for c, w in zip(self.slots[n], self.val[n][1]):
                if is_op(c):
                    W.add(w)
                    if is_dec(c):
                        Wdec.add(w)
                elif isinstance(c, int):
                    adv_vals.add(w)
        root = name(self.dag.root)
        C = self.C
        for v in sorted(adv_vals):
            if v in C:
                put('adv', sym(v), FRESH, 'L', 'adv')
            else:
                put('adv', sym(v), sym(v + 1), 'L', 'scan')
        put('adv', 0, 0, 'R', root)
        for v in range(D):
            put('scan', sym(v), sym(v), 'L', 'scan')
        put('scan', 0, 0, 'R', root)
        R = len(self.reg_order)
        for k, first in (('inc', 'carry1'), ('dec', 'dstart')):
            for j in range(1, R + 1):
                put(f'c{k}{j}', 1, 1, 'R', f'c{k}{j}')
                put(f'c{k}{j}', SEP, SEP, 'R', f'c{k}{j - 1}' if j > 1 else first)
            put(f'c{k}1', 0, SEP, 'R', first)
        put('carry1', 1, 1, 'R', 'carry1')
        put('carry1', SEP, 1, 'R', 'carryS')
        put('carry1', 0, 1, 'L', 'scan')
        put('carryS', 1, SEP, 'R', 'carry1')
        put('carryS', SEP, SEP, 'R', 'carryS')
        put('carryS', 0, SEP, 'L', 'scan')
        put('dstart', 1, 1, 'R', 'dscan')
        put('dstart', SEP, SEP, 'L', 'retfail')
        put('dstart', 0, 0, 'L', 'retfail')
        put('dscan', 1, 1, 'R', 'dscan')
        put('dscan', SEP, 1, 'L', 'dput')
        put('dscan', 0, 0, 'L', 'dlast')
        put('dput', 1, SEP, 'R', 'dscan')
        put('dlast', 1, 0, 'L', 'scan')
        put('scan', SEP, SEP, 'L', 'scan')
        for q in ('retfail',):
            put(q, 1, 1, 'L', q)
            put(q, SEP, SEP, 'L', q)
        for w in sorted(Wdec):
            put('retfail', sym(w), FRESH, 'L', 'adv')
        nb = 0
        if boot is None:
            G = self.pc_depth
            for k in range(G):
                put(f'b{k}', 0, FRESH, 'R' if k < G - 1 else 'L', f'b{k + 1}' if k < G - 1 else 'scan')
            self.start = 'b0'
            self.G = G
        else:
            table, G, start = boot
            assert G >= self.pc_depth
            for (q, r), t in table.items():
                put(q, r, *t)
            self.start = start
            self.G = G
        self.tm = tm
        self.root = root

    def count(self):
        return len(self.tm)

    def breakdown(self):
        cat = Counter()
        for (q, r) in self.tm:
            k = ('nodes' if q[0] == 'n' else q if q in ('scan', 'adv') else 'erase' if q[0] in 'ej'
                 else 'chains' if q[:4] in ('cinc', 'cdec') else 'boot' if q[0] == 'b' else 'regops')
            cat[k] += 1
        return dict(cat)

    # concrete check against k215P ------------------------------------------------------
    def config(self, pc, regs):
        t = defaultdict(int)
        cells = list(map(lambda v: v + 1, self.pc_tape[pc]))
        cells += [FRESH] * (self.G - len(cells))
        for r in self.reg_order:
            cells += [self.SEP] + [1] * regs[r]
        for i, c in enumerate(cells):
            t[i] = c
        return t

    def normalize(self, t):
        """the PC digits as the walk reads them: a child slot's entry value is replaced by its
        inside value (the canonical form); the leaf slot keeps its entry value"""
        n, i, digs = self.dag.root, 0, []
        while True:
            v = t[i] - 1
            vals, writes, _ = self.val[n]
            hit = None
            for jj, c in enumerate(self.slots[n]):
                if isinstance(c, int) and v in (vals[jj], writes[jj]):
                    hit = (jj, writes[jj], c)
                elif not isinstance(c, int) and v == vals[jj]:
                    hit = (jj, vals[jj], None)
            if hit is None:
                return None
            jj, d, c = hit
            digs.append(d)
            if c is None:
                return digs
            n, i = c, i + 1

    def regs_of(self, t):
        i = len(self.pc_tape[0])
        while t[i] == FRESH:
            i += 1
        # cells from the first SEP after the PC
        i = max(i, 0)
        vals = []
        j = 0
        while t[j] != self.SEP and j <= self.G + 2:
            j += 1
        while t[j] == self.SEP:
            j += 1
            c = 0
            while t[j] == 1:
                c += 1
                j += 1
            vals.append(c)
        if any(t[k] for k in t if k >= j and t[k]):
            return None
        out = [None] * 9
        for r, v in zip(self.reg_order, vals):
            out[r] = v
        return out

    def check_pc(self, pc, regs, maxcycles=4, maxsteps=10**6, start=None):
        e = P[pc]
        nr = list(regs)
        if e['tag'] == 4:
            npc = None
        elif e['tag'] == 0:
            nr[e['arg']] += 1
            npc = e['pos']
        elif e['tag'] == 1:
            if regs[e['arg']]:
                nr[e['arg']] -= 1
                npc = e['pos']
            else:
                npc = e['zero']
        else:
            npc = e['zero']
        t = start if start is not None else self.config(pc, regs)
        q, h, steps, cycles = self.root, 0, 0, 0
        while steps < maxsteps:
            if q == 'halt':
                return npc is None, steps, None
            w, d, nq = self.tm[(q, t[h])]
            t[h] = w
            h += 1 if d == 'R' else -1
            q = nq
            steps += 1
            if q == self.root and h == 0:
                cycles += 1
                if npc is not None and t[-1] == 0 and self.normalize(t) == self.pc_tape[npc] \
                        and self.regs_of(t) == nr:
                    return True, steps, t
                if cycles >= maxcycles:
                    return False, steps, t
        return False, steps, t


def build(dag, D, order=None, rnd=None, reg_order=None, boot=None):
    """greedy merges (in `order`), repairing inconsistencies"""
    rc = Counter()
    for (a, b) in dag.nodes:
        for c in (a, b):
            if isinstance(c, int):
                rc[c] += 1
    cand = [n for n in range(len(dag.nodes)) if rc[n] == 1]
    if order is not None:
        cand = order
    elif rnd is not None:
        rnd.shuffle(cand)
    M = set()
    ctxs = contexts(dag)
    best = None
    for n in cand:
        M.add(n)
        while True:
            try:
                Machine(dag, D, M, reg_order, boot, ctxs)
                break
            except Machine.Bad as e:
                why, bad = e.args[0]
                if why == 'fit' or bad not in M:
                    bad = n
                M.discard(bad)
                if bad == n:
                    break
    m = Machine(dag, D, M, reg_order, boot, ctxs)
    return m


if __name__ == '__main__':
    dag = DAG(prologue=4)
    for D in map(int, sys.argv[1:] or [3, 4, 6, 8]):
        m = build(dag, D)
        print(f'D={D}: {m.count()} instr, {len({q for q, _ in m.tm})} states, pc depth {m.pc_depth}, '
              f'merged {len(m.L.M)}, {m.breakdown()}', flush=True)
        bad = 0
        rnd = random.Random(1)
        for pc in range(NP):
            regs = [rnd.randint(0, 3) for _ in range(9)]
            ok, _, _ = m.check_pc(pc, regs)
            if not ok:
                bad += 1
                if bad < 4:
                    print('  mismatch pc', pc, P[pc])
        print('  check: bad', bad)
