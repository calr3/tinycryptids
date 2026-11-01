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
DECJUMP = False
MARKS = None     # read-back register ops: {'i': inc marker values, 'd': dec marker values}
READBACK = False
LASTCLASH = None
UNICTL = False   # erase states shared by height
NATIVEDEC = False
VIRT = False     # virtual gotos (see Machine)
NOADV0 = False
PRESEP = False   # the boot writes all 9 separators and a trailing one (no lazy registers)
ALTS = 0         # alternative value orders tried per kary node on a value conflict
ALTRETRY = 0
ALT0 = None
XMARK = ()       # marker values reserved for native decX leaves
SEPVAL = None    # the separator's digit value (None: its own symbol D + 1)
SPECIAL = {}     # special op markers: value -> 0 (exit) or h (erase into e<h>), read by scan
CARRYTO = {}     # reserved inside values: adv erases into e<h> (virtual last control slots)  # a failed decnz as a break (decX leaves kept, see program.DAG(native_decx))  # allow a failed decnz to jump inside its kary node
_amemo = {}


def assign(sl, D, C, vh=None, alt=0):
    """Optimal slot values for a node.  Returns (e, wr, cost) or None: e[j] the value slot j is
    entered at, wr[j] what its transition writes (the inside value of a child slot, the marker
    of an op), cost = transitions.  adv/retok: a value in C carries (the node is done), any
    other value v becomes v + 1."""
    T = D - 1
    marks = MARKS
    if (SEPVAL is not None or XMARK) and not marks:
        marks = {'i': set(range(1, T + 1)), 'd': set(range(1, T + 1)) - {SEPVAL} - set(XMARK),
                 'x': set(XMARK) - {SEPVAL}}
    if marks:
        kinds = tuple('n' if isinstance(c, int) else
                      (('x' if len(c) == 3 and 'x' in marks else 'd') if is_dec(c) else 'i') if is_op(c) else 'c'
                      for c in sl)
    else:
        kinds = tuple('n' if isinstance(c, int) else 'o' if is_op(c) else 'c' for c in sl)
    CT = {}
    for r, hh in CARRYTO.items():
        CT.setdefault(hh, set()).add(r)
    reserved = set(CARRYTO)
    if vh is not None:
        kinds = kinds[:-1] + ('v',)
    key = (kinds, D, tuple(sorted(C)), marks and tuple(sorted(marks['i'])), marks and tuple(sorted(marks['d'])),
           tuple(sorted(XMARK)), alt,
           vh, tuple(sorted(CARRYTO.items())), tuple(sorted(SPECIAL)))
    smask = sum(1 << x for x in SPECIAL)
    if key in _amemo:
        return _amemo[key]
    m = len(kinds)
    best = [None]
    if m > D:
        _amemo[key] = None
        return None
    from functools import lru_cache

    js = vh[1] if isinstance(vh, tuple) and vh[0] == 'J' else None
    # alt: another tie-break order of the values (another optimal assignment)
    order = list(range(T + 1))
    if alt:
        order = order[::-1] if alt % 2 else order
        k_ = (alt // 2) % (T + 1)
        order = order[k_:] + order[:k_]

    @lru_cache(maxsize=None)
    def go(j, e, used, es=None):
        # used: bitmask of values read by the node so far (e included); es: entry of slot js
        k = kinds[j]
        if j == js:
            es = e
        last = j == m - 1 or (j == m - 2 and kinds[m - 1] == 'v')
        opts = []
        if k == 'v':
            return (0, (None,), None)
        if k == 'n':
            if last and kinds[m - 1] == 'v':
                if isinstance(vh, tuple):
                    fin = C if vh[0] == 'C' else ({es - 1} - set(C) if es else set())
                else:
                    fin = CT[vh]
            else:
                fin = C
            for i in order:
                if last != (i in fin) or (not last and i in reserved):
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
                    r = go(j + 1, ne, u | (1 << ne), es)
                    if r is not None:
                        opts.append((1 + extra + r[0], (i,) , r))
        elif k in 'oidx':
            allowed = [x for x in order if x >= 1] if k == 'o' else [x for x in order if x in marks[k]]
            if last:
                for w in allowed:
                    if (used >> w) & 1:
                        continue
                    opts.append((2, (w,), None))
                    break
            else:
                for w in allowed:
                    if (used >> w) & 1:
                        continue
                    r = go(j + 1, w, used | (1 << w), es)
                    if r is not None:
                        opts.append((1 + r[0], (w,), r))
        else:
            if last:
                opts.append((1, (None,), None))
            else:
                for ne in order:
                    if (used >> ne) & 1:
                        continue
                    r = go(j + 1, ne, used | (1 << ne), es)
                    if r is not None:
                        opts.append((1 + r[0], (None,), r))
                        break
        if not opts:
            return None
        return min(opts, key=lambda x: x[0])
    r = go(0, 0, 1 | smask)
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
        elif k in 'oidx':
            v = node[1][0]
        else:
            # the first unused value (as chosen)
            used = set(e) | {w for w, kk in zip(wr, kinds) if kk == 'n' and w is not None}
            v = next(x for x in order if x not in used and not (smask >> x) & 1)
        node = nxt
        j += 1
    if len(e) < m:
        e.append(None)
        wr.append(None)
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
        if dag.leaf_kind[pc][0] == 'decX' and not getattr(dag, 'native_decx', False):
            out.append(bits[:-1] + (1,))
            out.append(bits[:-2] + (1,))
    return out


class Machine:
    """Build the TM for a merge set; raises Bad(node) when the merge set is inconsistent."""
    class Bad(Exception):
        pass

    def __init__(self, dag, D, merged, reg_order=None, boot=None, ctxs=None):
        self.dag, self.D, self.T, self.SEP = dag, D, D - 1, D + 1
        self.K = D + 2
        if SEPVAL is not None:
            # the separator shares the symbol of digit SEPVAL (never a dec marker)
            self.SEP, self.K = SEPVAL + 1, D + 1
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
        self.alt = dict(ALT0 or {})
        ctxs = ctxs or contexts(dag)

        def core():
            self.val = {}
            C = CARRY if CARRY is not None else {D - 1}
            self.C = C
            self.vplan = {}
            if VIRT and UNICTL:
                # the plan for a last control slot after a child, from its contexts: ('C',) the
                # child carries (an exit), ('J', s) the child's inside value is slot s's entry - 1
                # (a jump inside the node), h: a reserved inside value erases into e<h> (CARRYTO)
                plans = defaultdict(set)
                for bits in (ctxs or contexts(dag)):
                    kp, leaf, path, where = L.resolve(bits)
                    if isinstance(leaf, tuple) and leaf[0] in ('brk', 'cnt'):
                        A = path[len(path) - leaf[1]][0]
                        ti, start = where[A]
                        Kt = kp[ti][0]
                        h = len(kp) - 1 - ti
                        if h >= 1:
                            p = h
                        elif leaf[0] == 'brk':
                            p = ('C',) if A not in M or start + L.size(A) == len(self.slots[Kt]) else ('J', start + L.size(A))
                        else:
                            p = ('J', start) if A in M and start > 0 else None
                        plans[tuple(kp[-1])].add(p)
                avail = set(CARRYTO.values())
                for n in self.knodes:
                    sl = self.slots[n]
                    j = len(sl) - 1
                    if j >= 1 and isinstance(sl[j - 1], int) and isinstance(sl[j], tuple) and sl[j][0] in ('brk', 'cnt'):
                        p = plans.get((n, j))
                        if p and len(p) == 1:
                            p = min(p, key=str)
                            if (isinstance(p, tuple) and p[0] == 'C') or (isinstance(p, tuple) and p[1] < j) \
                                    or (isinstance(p, int) and p in avail):
                                self.vplan[n] = p
            for n in self.knodes:
                v = assign(self.slots[n], D, C, self.vplan.get(n), self.alt.get(n, 0))
                if v is None and n in self.vplan:
                    del self.vplan[n]
                    v = assign(self.slots[n], D, C)
                if v is None:
                    raise Machine.Bad(('fit', n))
                self.val[n] = v
            # controls, per context
            self.ctl = {}                  # (K, j) -> (kind, mode, h); mode None or jump value t
            self.decact = {}               # dec marker w -> None (exit) or the jump value t
            self.jumps = set()             # (knode, value) written by a jump
            self.decslot = {}              # dec slot -> its failure action
            self.decowner = {}             # dec marker -> the first path that used it
            self.levels = defaultdict(set)  # (kind, mode, e) -> values read at that level
            self.act1 = {}                  # UNICTL: target cell value -> action
            self.act1own = {}
            self.pc_tape = {}
            ctlpath = {}
            for bits in ctxs:
                kp, leaf, path, where = L.resolve(bits)
                if isinstance(leaf, tuple) and (leaf[0] in ('brk', 'cnt') or is_dec(leaf) and NATIVEDEC):
                    # a failed decnz acts as a break to after its trie parent (or its decX target)
                    if is_dec(leaf):
                        kind, k = 'brk', (leaf[2] if len(leaf) == 3 else 1)
                    else:
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
                    if mode is not None:
                        self.jumps.add((Kt, mode))
                    if A in M and Kt in self.vplan and (kind == 'brk' and start + L.size(A) == len(self.slots[Kt]) - 1):
                        raise Machine.Bad(('virt', A if A in M else Kt))
                    if UNICTL and h >= 1:
                        # shared erase states e<h>; the target cell's value picks the action
                        v = ('u', None, h)
                        act = ('jump', mode) if mode is not None else (kind, None)
                        K1, j1 = kp[ti]
                        v1 = self.val[K1][1][j1]
                        self.act1own.setdefault(v1, K1)
                        if self.act1.setdefault(v1, act) != act:
                            bad = [n for n, _ in reversed(path) if n in M]
                            ex = Machine.Bad(('ctl', bad[0] if bad else None))
                            ex.knodes = (K1, self.act1own[v1])
                            raise ex
                    if is_dec(leaf):
                        if (h > 0 or mode is not None) and not DECJUMP:
                            bad = [n for n, _ in reversed(path) if n in M]
                            raise Machine.Bad(('dec', bad[0] if bad else None))
                        w = self.val[kp[-1][0]][1][kp[-1][1]]
                        self.decslot[tuple(kp[-1])] = v
                        self.decowner.setdefault(w, (path, kp[-1][0]))
                        if self.decact.setdefault(w, v) != v:
                            bad = [n for n, _ in list(reversed(path)) + list(reversed(self.decowner[w][0])) if n in M]
                            ex = Machine.Bad(('dec', bad[0] if bad else None))
                            ex.knodes = (kp[-1][0], self.decowner[w][1])
                            raise ex
                    else:
                        if key in self.ctl and self.ctl[key] != v:
                            global LASTCLASH
                            LASTCLASH = (key, self.ctl[key], v, Kt, start)
                            for n, _ in list(reversed(path)) + list(reversed(ctlpath[key])):
                                if n in M:
                                    raise Machine.Bad(('ctl', n))
                            raise AssertionError('control clash with nothing merged')
                        self.ctl[key] = v
                        ctlpath.setdefault(key, path)
                    for e in range(h, 0 if not (UNICTL and h >= 1) else 1, -1):
                        K, j = kp[len(kp) - 2 - h + e]
                        self.levels[v[:2] + (e,)].add(self.val[K][1][j])
                elif is_dec(leaf):
                    # a failed decnz finishes its trie parent: it exits its kary node when that
                    # parent ends the node, otherwise it jumps to the slot after the parent
                    # (retfail reads the dec's marker, so the marker decides)
                    Pn = path[-1][0]
                    ti, start = where[Pn]
                    Kd, jd = kp[-1]
                    e = start + L.size(Pn)
                    act = None if Pn not in M or e == len(self.slots[Kd]) else self.val[Kd][0][e]
                    if Kd in self.vplan and e == len(self.slots[Kd]) - 1:
                        raise Machine.Bad(('virt', Pn))
                    if act is not None and not DECJUMP:
                        raise Machine.Bad(('dec', Pn if Pn in M else next(n for n, _ in reversed(path) if n in M)))
                    w = self.val[Kd][1][jd]
                    if act is not None:
                        self.jumps.add((Kd, act))
                    self.decslot[(Kd, jd)] = act
                    self.decowner.setdefault(w, (path, Kd))
                    old = self.decact.setdefault(w, act)
                    if old != act:
                        bad = [n for n, _ in list(reversed(path)) + list(reversed(self.decowner[w][0])) if n in M]
                        ex = Machine.Bad(('dec', bad[0] if bad else None))
                        ex.knodes = (Kd, self.decowner[w][1])
                        raise ex
            # virtual gotos: a last control slot after an inc that restarts / jumps inside its own
            # kary node is dropped; the inc's marker is the target's entry value
            self.virt, self.vmark = set(), {}
            if VIRT:
                for n in self.knodes:
                    sl = self.slots[n]
                    j = len(sl) - 1
                    if j < 1 or (n, j) not in self.ctl or not is_op(sl[j - 1]):
                        continue
                    kind, mode, h = self.ctl[(n, j)]
                    if kind == 'u' or h != 0:
                        continue
                    t = mode if mode is not None else (0 if kind == 'cnt' else None)
                    if t is None or (n, self.val[n][0][j]) in self.jumps:
                        continue
                    if is_dec(sl[j - 1]):
                        # the marker is also read by retfail: t must be visible and agree
                        a = self.decslot.get((n, j - 1), 'none')
                        if t == 0 or t == SEPVAL or a == 'none' or self.decact.get(t, a) != a:
                            continue
                        self.decact[t] = a
                    self.virt.add((n, j))
                    self.vmark[(n, j - 1)] = t
            # special markers: an op's marker that scan (on the way back) turns into a control action:
            # exit the node (a last op) or erase into e<h> (a control slot after the op, dropped)
            self.lastspecial = set()
            if SPECIAL and UNICTL:
                sinv = {a: v for v, a in SPECIAL.items()}

                def dec_ok(n, j, s_):
                    if not is_dec(self.slots[n][j]):
                        return True
                    if s_ == SEPVAL:
                        return False
                    a = self.decslot.get((n, j), 'none')
                    if a == 'none' or self.decact.get(s_, a) != a:
                        return False
                    self.decact[s_] = a
                    return True
                for n in self.knodes:
                    sl = self.slots[n]
                    j = len(sl) - 1
                    if is_op(sl[j]) and 0 in sinv and dec_ok(n, j, sinv[0]):
                        self.vmark[(n, j)] = sinv[0]
                        self.lastspecial.add(n)
                        continue
                    if j < 1 or (n, j) not in self.ctl or (n, j) in self.virt or not is_op(sl[j - 1]):
                        continue
                    kind, mode, h = self.ctl[(n, j)]
                    a = h if kind == 'u' else 0 if (kind == 'brk' and mode is None and h == 0) else None
                    if a is None or a not in sinv or (n, self.val[n][0][j]) in self.jumps:
                        continue
                    if not dec_ok(n, j - 1, sinv[a]):
                        continue
                    self.virt.add((n, j))
                    self.vmark[(n, j - 1)] = sinv[a]
            for n in self.vplan:
                self.virt.add((n, len(self.slots[n]) - 1))
            self.virtual_pcs = set()
            for pc in range(NP):
                kp, leaf, _, _ = L.resolve(dag.pc_ir[pc])
                if tuple(kp[-1]) in self.virt:
                    self.virtual_pcs.add(pc)
                self.pc_tape[pc] = [self.val[K][1][j] for K, j in kp[:-1]] + [self.val[kp[-1][0]][0][kp[-1][1]]]

        for attempt in range(ALTRETRY + 1):
            try:
                core()
                break
            except Machine.Bad as e:
                ks = [k for k in getattr(e, 'knodes', ()) if k is not None and self.alt.get(k, 0) < ALTS]
                if not ks or attempt == ALTRETRY:
                    raise
                k = ks[attempt % len(ks)]
                self.alt[k] = self.alt.get(k, 0) + 1
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
            if kind == 'u':
                return f'e{e}'
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
                elif (n, j) in self.virt:
                    continue
                elif c[0] in ('inc', 'dec'):
                    if (n, j) in self.vmark:
                        w = self.vmark[(n, j)]
                    put(q, sym(v), sym(w), 'R', f'c{regno[c[1]] + 1}' if READBACK else f'c{c[0]}{regno[c[1]] + 1}')
                    if j == len(self.slots[n]) - 1 and n not in self.lastspecial:
                        put(q, sym(w), FRESH, 'L', 'adv')
                elif c[0] == 'halt':
                    put(q, sym(v), sym(v), 'R', 'halt')
                else:
                    kind, mode, h = self.ctl[(n, j)]
                    if h == 0 and mode is not None:
                        put(q, sym(v), sym(mode), 'L', 'scan')
                    else:
                        put(q, sym(v), FRESH, 'L', ctlstate(kind, mode, h))
        for v1, act in sorted(self.act1.items()):
            if act[0] == 'jump':
                put('e1', sym(v1), sym(act[1]), 'L', 'scan')
            else:
                put('e1', sym(v1), FRESH, 'L', 'scan' if act[0] == 'cnt' else 'adv')
        for (kind, mode, e), vs in sorted(self.levels.items(), key=str):
            for v in sorted(vs):
                if mode is not None and e == 1:
                    put(f'j{mode}_1', sym(v), sym(mode), 'L', 'scan')
                else:
                    put(ctlstate(kind, mode, e), sym(v), FRESH, 'L', ctlstate(kind, mode, e - 1))
        adv_vals, W, Wdec = set(), set(), set()
        for n in self.knodes:
            for j, (c, w) in enumerate(zip(self.slots[n], self.val[n][1])):
                w = self.vmark.get((n, j), w)
                if is_op(c):
                    W.add(w)
                    if is_dec(c):
                        Wdec.add(w)
                elif isinstance(c, int):
                    adv_vals.add(w)
        root = name(self.dag.root)
        C = self.C
        for v in sorted(adv_vals):
            if v in CARRYTO and UNICTL:
                put('adv', sym(v), FRESH, 'L', f'e{CARRYTO[v]}')
            elif v in C:
                put('adv', sym(v), FRESH, 'L', 'adv')
            else:
                put('adv', sym(v), sym(v + 1), 'L', 'scan')
        if not NOADV0:
            put('adv', 0, 0, 'R', root)       # the root finishing (never, with the prologue's loop)
        for v in range(D):
            if v in SPECIAL:
                a = SPECIAL[v]
                put('scan', sym(v), FRESH, 'L', f'e{a}' if a else 'adv')
            else:
                put('scan', sym(v), sym(v), 'L', 'scan')
        put('scan', 0, 0, 'R', root)
        R = len(self.reg_order)
        if READBACK:
            # one chain per register; on arrival mark the separator (MK), read the op's marker
            MK = 2
            for j in range(1, R + 1):
                put(f'c{j}', 1, 1, 'R', f'c{j}')
                put(f'c{j}', SEP, SEP if j > 1 else MK, 'R' if j > 1 else 'L', f'c{j - 1}' if j > 1 else 'back')
            put('c1', 0, MK, 'L', 'back')
            put('back', 1, 1, 'L', 'back')
            put('back', SEP, SEP, 'L', 'back')
            for n in self.knodes:
                for j, (c, w) in enumerate(zip(self.slots[n], self.val[n][1])):
                    w = self.vmark.get((n, j), w)
                    if is_op(c):
                        g = 'godec' if is_dec(c) else 'goinc'
                        if (('back', sym(w))) in tm:
                            assert tm[('back', sym(w))][2] == g, ('marker clash', w)
                        else:
                            put('back', sym(w), sym(w), 'R', g)
            for g, first in (('goinc', 'carry1'), ('godec', 'dstart')):
                put(g, 1, 1, 'R', g)
                put(g, SEP, SEP, 'R', g)
                put(g, MK, SEP, 'R', first)
        for k, first in (() if READBACK else (('inc', 'carry1'), ('dec', 'dstart'))):
            for j in range(1, R + 1):
                put(f'c{k}{j}', 1, 1, 'R', f'c{k}{j}')
                put(f'c{k}{j}', SEP, SEP, 'R', f'c{k}{j - 1}' if j > 1 else first)
            if not PRESEP:
                put(f'c{k}1', 0, SEP, 'R', first)
        put('carry1', 1, 1, 'R', 'carry1')
        put('carry1', SEP, 1, 'R', 'carryS')
        if not PRESEP:
            put('carry1', 0, 1, 'L', 'scan')
        put('carryS', 1, SEP, 'R', 'carry1')
        put('carryS', SEP, SEP, 'R', 'carryS')
        put('carryS', 0, SEP, 'L', 'scan')
        put('dstart', 1, 1, 'R', 'dscan')
        put('dstart', SEP, SEP, 'L', 'retfail')
        if not PRESEP:
            put('dstart', 0, 0, 'L', 'retfail')
        put('dscan', 1, 1, 'R', 'dscan')
        put('dscan', SEP, 1, 'L', 'dput')
        put('dscan', 0, 0, 'L', 'dlast')
        put('dput', 1, SEP, 'R', 'dscan')
        put('dlast', 1, 0, 'L', 'scan')
        if SEPVAL is None:
            put('scan', SEP, SEP, 'L', 'scan')
        for q in ('retfail',):
            put(q, 1, 1, 'L', q)
            put(q, SEP, SEP, 'L', q)
        for w in sorted(Wdec):
            t = self.decact.get(w)
            if isinstance(t, tuple):
                kind, mode, h = t
                if h == 0 and mode is not None:
                    put('retfail', sym(w), sym(mode), 'L', 'scan')
                else:
                    put('retfail', sym(w), FRESH, 'L', ctlstate(kind, mode, h))
            elif t is None:
                put('retfail', sym(w), FRESH, 'L', 'adv')
            else:
                put('retfail', sym(w), sym(t), 'L', 'scan')
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
                 else 'chains' if q[:4] in ('cinc', 'cdec') or q[:1] == 'c' and q[1:].isdigit() else 'boot' if q[0] == 'b' and q != 'back' else 'regops')
            cat[k] += 1
        return dict(cat)

    # concrete check against k215P ------------------------------------------------------
    def config(self, pc, regs):
        t = defaultdict(int)
        cells = list(map(lambda v: v + 1, self.pc_tape[pc]))
        cells += [FRESH] * (self.G - len(cells))
        for r in self.reg_order:
            cells += [self.SEP] + [1] * regs[r]
        if PRESEP:
            cells += [self.SEP] * PRESEP
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
        j = self.G
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
        while npc in self.virtual_pcs:
            npc = P[npc]['zero']
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
