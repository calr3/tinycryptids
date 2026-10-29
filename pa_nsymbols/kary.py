"""Compile the PA program (ir.py) to a Turing machine with D + 2 symbols.

Tape (0 is blank; the digit value v is the symbol v + 1; SEP = D + 1):

    0 [d_0 d_1 ... d_h] 1 1 ... 1 [SEP 1^v0] [SEP 1^v1] ... [SEP 1^v9] 0 0 ...
       program counter   gap        register file

* Program: a tree of *nodes*, each with at most D children (slots) run in order.  A node is
  one state; its cell on the program counter (PC) holds the slot being run.  The root's cell is
  cell 0, and the cell left of it is blank.  A child's cell is right of its parent's.
* 1 (digit value 0) is also the gap symbol: a fresh cell means "first slot", so the PC needs
  no length.  Advancing a cell from slot v writes v + 1; a node's last slot leaves T = D - 1
  (or is a break / continue / halt), so the advance state erases T cells (writes 1) and
  carries left.  See values() for how a node's slots are numbered.
* Dispatch: `scan` runs left to the blank before cell 0 and enters the root node, which walks
  right through the nodes to a register op, a break, a continue or halt.
* A register op is a node's transition straight into a chain state (`cinc<j>`, `cdec<j>`):
  it writes a nonzero value on the node's cell, and the chain runs right, counting separators
  to register r (the gap is 1s, so it is crossed like a register), and does the operation.  The
  return (`retok`, or `retfail` when a decnz finds 0) runs left over 1s and separators to the
  first other symbol, the node's cell, and advances it (or, for a failed decnz, erases it: the
  node is done).  The first operation on register r is always after the first on r - 1
  (registers are numbered in that order), so the file is created lazily: the last chain state
  writes a separator on a blank.
* break / continue of a label L from a node h levels below it: erase h + 1 cells (up to L's
  cell), then `adv` (break: L is done) or `scan` (continue: L starts again).
* Boot: a few states write the gap (at least as many 1s as the PC has cells), then `scan`.

Instructions are the defined transitions; a node with m slots costs m, plus 1 when m < D, its
last child is a node and it has no register op (values()).
"""
import os, sys
from collections import defaultdict, Counter
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ir as irmod

FRESH = 1                 # digit value 0, also the gap
KEEP = ('pair', 'unpair')  # stay nodes (ksim applies them by formula)


def is_ctl(s):
    return isinstance(s, str) and (s.startswith('_') or s == 'halt')


def is_decnz(s):
    return isinstance(s, str) and s.endswith('.decnz')


def is_op(s):
    return isinstance(s, str) and s.startswith('3.')


def boot_table(text, maxsteps=10**6):
    """A boot written in the standard format over the symbols 0, 1, 2 (states A, B, ...; X is
    the exit into scan): its transitions as states bA, bB, ..., and the length G of the run of
    1s it leaves.  Checked by running it: the exit must leave  [anything] 0 1^G 0 0 ...  with
    the head on the run or the blank before it (scan then finds cell 0 = the run's first cell)."""
    rows = text.strip('_').split('_')
    table = {}
    for i, row in enumerate(rows):
        for r in range(len(row) // 3):
            t = row[3 * r:3 * r + 3]
            if t != '---':
                table[(f'b{chr(65 + i)}', r)] = (int(t[0]), t[1], 'scan' if t[2] == 'X' else f'b{t[2]}')
    tape, pos, q = defaultdict(int), 0, 'bA'
    for _ in range(maxsteps):
        w, d, n = table[(q, tape[pos])]
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        if n == 'scan':
            break
        q = n
    else:
        raise ValueError('boot does not exit')
    cells = sorted(i for i, x in tape.items() if x)
    right = cells[-1]
    left = right
    while tape[left - 1] == 1:
        left -= 1
    assert tape[right] == 1 and tape[left - 1] == 0 and left - 1 <= pos <= right, 'boot leaves a bad tape'
    return table, right - left + 1


class Compiler:
    def __init__(self, D, ir=None, factor=True, boot=None, grammar_seed=None):
        assert D >= 3
        self.D, self.T = D, D - 1
        self.SEP = D + 1                    # the register separator: not a digit
        self.ir = ir or irmod.prog()
        self.boot = boot
        self.grammar_seed = grammar_seed
        self.build_nodes()
        if factor:
            self.factor()
            self.inline()
        self.split()
        self.gc()
        if factor:
            self.inline_loops()
        self.layout()
        regs = sorted({c.split('.')[1] for sl in self.nodes.values() for c in sl if is_op(c)})
        self.reg_order = regs                   # provisional, for the first run
        self.regno = {r: k for k, r in enumerate(regs)}
        self.emit()
        self.number_registers()
        self.emit()

    # -- program -> nodes --------------------------------------------------------------------
    def build_nodes(self):
        N = self.ir.nodes
        refc = Counter()
        for n in N.values():
            for c in (n[1] if n[0] == 'seq' else [n[2]]):
                if isinstance(c, int):
                    refc[c] += 1
        memo = {}

        def slots(i):
            if i in memo:
                return memo[i]
            n = N[i]
            if n[0] == 'label':
                b = n[2]
                out = slots(b) if isinstance(b, int) and N[b][0] == 'seq' else [b]
            else:
                out = []
                for j, c in enumerate(n[1]):
                    last = j == len(n[1]) - 1
                    if isinstance(c, int) and N[c][0] == 'seq' and refc[c] == 1:
                        sc = slots(c)
                        if last or not any(is_decnz(x) for x in sc):
                            out += sc
                            continue
                    out.append(c)
            memo[i] = out
            return out

        self.nodes = {}
        self.label_node = {}          # label id -> node

        def visit(i):
            if i in self.nodes:
                return
            self.nodes[i] = slots(i)
            if N[i][0] == 'label':
                self.label_node[N[i][1]] = i
            for c in self.nodes[i]:
                if isinstance(c, int):
                    visit(c)
        visit(self.ir.root)
        self.root = self.ir.root
        self.names = {}
        used = Counter(self.ir.name(i) for i in self.nodes)
        for i in self.nodes:
            nm = self.ir.name(i)
            self.names[i] = nm if nm and used[nm] == 1 else f'{nm or "s"}#{i}'

    # -- grammar compression ----------------------------------------------------------------
    def node_cost(self, sl):
        r = self.values(sl) if len(sl) <= self.D else None
        if r is None:
            return len(sl) + len(sl) // max(self.D - 2, 1) + 1    # about what splitting costs
        return len(sl) + (r[2] is not None)

    def factor(self):
        """Repeatedly factor the repeated run of slots with the largest saving into a new node
        (with grammar_seed: one of the three best, at random, a third of the time).  A run may
        not contain control slots, nor a decnz unless it ends its node in every occurrence (a
        failed decnz leaves the node that holds it)."""
        import random
        rnd = random.Random(self.grammar_seed) if self.grammar_seed is not None else None
        fid = 0
        while True:
            occ = defaultdict(list)
            for i, sl in self.nodes.items():
                n = len(sl)
                for a in range(n):
                    if is_ctl(sl[a]):
                        continue
                    for b in range(a + 2, min(n, a + self.D) + 1):
                        if is_ctl(sl[b - 1]):
                            break
                        occ[tuple(sl[a:b])].append((i, a))
            cands = []
            for run, places in occ.items():
                L = len(run)
                # non-overlapping occurrences per node, left to right
                taken, last = [], {}
                for i, a in sorted(places, key=lambda x: (str(x[0]), x[1])):
                    if a >= last.get(i, -1):
                        taken.append((i, a))
                        last[i] = a + L
                if len(taken) < 2:
                    continue
                if any(is_decnz(x) for x in run):
                    if any(a + L != len(self.nodes[i]) for i, a in taken):
                        continue
                save = len(taken) * (L - 1) - self.node_cost(list(run))
                if save > 0:
                    cands.append((save, run, taken))
            if not cands:
                return
            # the first run with the largest saving (stable: candidates are in discovery order)
            cands.sort(key=lambda x: -x[0])
            k = rnd.randrange(min(3, len(cands))) if rnd and rnd.random() < 0.33 else 0
            _, run, taken = cands[k]
            new = ('f', fid)
            fid += 1
            self.nodes[new] = list(run)
            self.names[new] = f'f{fid - 1}'
            by = defaultdict(list)
            for i, a in taken:
                by[i].append(a)
            for i, offs in by.items():
                sl = self.nodes[i]
                out, j = [], 0
                for a in sorted(offs):
                    out += sl[j:a] + [new]
                    j = a + len(run)
                self.nodes[i] = out + sl[j:]

    def inline(self):
        """Greedily replace a node by its slots in every parent when that lowers the total
        (labels stay nodes; a run with a decnz only goes where it ends its parent)."""
        labels = set(self.label_node.values())

        def cost(sl):
            if len(sl) > self.D:        # the root: chunked later, about one per slot
                return len(sl) + len(sl) // self.D
            return self.node_cost(sl)
        while True:
            uses = defaultdict(list)
            for p, sl in self.nodes.items():
                for j, c in enumerate(sl):
                    if not isinstance(c, str):
                        uses[c].append((p, j))
            best = None
            for x, us in uses.items():
                if x in labels or x == self.root or str(self.names.get(x)).split('(')[0] in KEEP:
                    continue
                xs = self.nodes[x]
                dec = any(is_decnz(c) for c in xs)
                ok, delta = True, -cost(xs)
                by = defaultdict(list)
                for p, j in us:
                    by[p].append(j)
                for p, js in by.items():
                    sl = self.nodes[p]
                    if dec and any(j != len(sl) - 1 for j in js) or p == x:
                        ok = False
                        break
                    new = []
                    for j, c in enumerate(sl):
                        new += xs if c == x else [c]
                    if len(new) > self.D and p != self.root:
                        ok = False
                        break
                    delta += cost(new) - cost(sl)
                if ok and delta < 0 and (best is None or delta < best[0]):
                    best = (delta, x)
            if best is None:
                return
            x = best[1]
            xs = self.nodes.pop(x)
            for p, sl in self.nodes.items():
                if x in sl:
                    new = []
                    for c in sl:
                        new += xs if c == x else [c]
                    self.nodes[p] = new

    # -- nodes with more than D slots -> trees -------------------------------------------------
    def inline_loops(self):
        """A label used only as the last slot of its parents, and referred to only by its own
        slots, is inlined into each parent: a continue becomes `_jmp:k` (rewrite the parent's
        cell to slot k, the label's first, and dispatch), a break `_done` (the parent is done,
        which is what finishing its last slot means).  Applied where the count drops."""
        while True:
            uses = defaultdict(list)
            for p, sl in self.nodes.items():
                for j, c in enumerate(sl):
                    if not isinstance(c, str):
                        uses[c].append((p, j))
            refs = defaultdict(set)         # label id -> nodes whose slots refer to it
            for i, sl in self.nodes.items():
                for c in sl:
                    if isinstance(c, str) and c.startswith('_') and '#' in c:
                        refs[int(c.split('#')[1])].add(i)
            best = None
            for lid, L in self.label_node.items():
                if L not in self.nodes or L == self.root or not uses[L] or refs[lid] - {L}:
                    continue
                if str(self.names.get(L)).split('(')[0] in KEEP:
                    continue
                if any(j != len(self.nodes[p]) - 1 for p, j in uses[L]):
                    continue
                news, delta = {}, -self.node_cost(self.nodes[L])
                for p, _ in uses[L]:
                    sl = self.nodes[p]
                    k = len(sl) - 1
                    body = [f'_jmp:{k}' if c == f'_cnt#{lid}' else '_done' if c == f'_brk#{lid}' else c
                            for c in self.nodes[L]]
                    new = sl[:-1] + body
                    if not self.fits(new):
                        break
                    news[p] = new
                    delta += self.node_cost(new) - self.node_cost(sl)
                else:
                    if delta < 0 and (best is None or delta < best[0]):
                        best = (delta, L, news)
            if best is None:
                return
            _, L, news = best
            self.nodes.update(news)
            del self.nodes[L]

    def fits(self, sl):
        return len(sl) <= self.D and self.values(sl) is not None

    def split(self):
        """Nodes that do not fit in D values become trees: chunks as siblings (shallow) when only
        the last chunk holds decnz / control slots; otherwise a chain: a prefix, then a node for
        the rest (a failed decnz or a break in the rest still ends the whole node, as the rest is
        its last slot)."""
        cid = [0]

        def new(sl, base):
            k = ('c', cid[0])
            cid[0] += 1
            self.nodes[k] = sl
            self.names[k] = f'{self.names[base]}.c{cid[0] - 1}'
            return k
        def upper(q):
            # cost of the levels above q bottom chunks (pure node refs), as the greedy builds them
            sl, cost = [('c', -1)] * q, 0
            while not self.fits(sl):
                cut = len(sl) % self.D
                groups = ([sl[:cut]] if cut else []) + [sl[a:a + self.D] for a in range(cut, len(sl), self.D)]
                cost += sum(self.node_cost(g) for g in groups if len(g) > 1)
                sl = [('c', -1)] * len(groups)
            return cost + self.node_cost(sl)

        def bottom(sl):
            # the bottom chunks minimising their cost plus the levels above (only the last may hold
            # decnz / control slots); None if there is no such partition
            n = len(sl)
            INF = 10**9
            best = [dict() for _ in range(n + 1)]      # best[i][q]: cost of chunking sl[i:] in q chunks
            best[n][0] = (0, None)
            for i in range(n - 1, -1, -1):
                for j in range(i + 1, min(n, i + self.D) + 1):
                    g = sl[i:j]
                    if j < n and any(is_decnz(x) or is_ctl(x) for x in g):
                        continue
                    if len(g) > 1 and not self.fits(g):
                        continue
                    c = self.node_cost(g) if len(g) > 1 else 0
                    for q, (cq, _) in best[j].items():
                        if c + cq < best[i].get(q + 1, (INF,))[0]:
                            best[i][q + 1] = (c + cq, j)
            if not best[0]:
                return None
            q = min(best[0], key=lambda q: best[0][q][0] + (upper(q) if q > 1 else 0))
            groups, i = [], 0
            while i < n:
                j = best[i][q][1]
                groups.append(sl[i:j])
                i, q = j, q - 1
            return groups

        for i in list(self.nodes):
            sl = self.nodes[i]
            if not self.fits(sl):
                groups = bottom(sl)
                if groups is not None and len(groups) > 1:
                    sl = [g[0] if len(g) == 1 else new(g, i) for g in groups]
            while not self.fits(sl):
                chunks, cur = [], []
                for x in reversed(sl):
                    if cur and not self.fits([x] + cur):
                        chunks.insert(0, cur)
                        cur = []
                    cur.insert(0, x)
                chunks.insert(0, cur)
                if not any(is_decnz(x) or is_ctl(x) for c in chunks[:-1] for x in c):
                    sl = [c[0] if len(c) == 1 else new(c, i) for c in chunks]
                    continue
                p = max(p for p in range(1, len(sl)) if self.fits(sl[:p] + [('c', -1)]))
                rest = new(sl[p:], i)
                self.nodes[i] = sl[:p] + [rest]
                i, sl = rest, self.nodes[rest]
            self.nodes[i] = sl

    def gc(self):
        seen = set()
        st = [self.root]
        while st:
            i = st.pop()
            if i in seen:
                continue
            seen.add(i)
            st += [c for c in self.nodes[i] if not isinstance(c, str)]
        self.nodes = {i: s for i, s in self.nodes.items() if i in seen}

    # -- digits, depths, control flow ----------------------------------------------------------
    def values(self, sl):
        """(the value each slot is run at, the value its transition writes, the skip value or
        None), or None if the slots do not fit in D values.

        Slot j + 1 is run at (what slot j wrote) + 1.  A register op is run straight from its
        node, which marks the cell for the return: an op writes a value other than 0 (a fresh
        cell), and since it finishes within one dispatch it may write any such value.  A node's
        last slot must leave T (the advance then finishes the node) unless it is a control slot:
        the last op writes T - (slots after it), and the following slots count up to T.  A node
        without ops whose last slot is a node and that is not full skips from m - 1 to T (one
        more transition)."""
        m, T = len(sl), self.T
        completes = not is_ctl(sl[-1])
        ops = [j for j, c in enumerate(sl) if is_op(c)]
        jstar = ops[-1] if ops and completes else None

        def run(last_op_write):
            vals, writes, v = [], [], 0
            for j, c in enumerate(sl):
                vals.append(v)
                if is_op(c):
                    w = max(v, 1)
                    if j == jstar and last_op_write is not None:
                        if last_op_write < w:
                            return None
                        w = last_op_write
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

    def layout(self):
        self.val = {i: self.values(sl) for i, sl in self.nodes.items()}
        # depth of every control slot below its label, and the cells it erases
        self.erase = {'brk': defaultdict(set), 'cnt': defaultdict(set)}   # level -> values
        self.ctl_depth = {}
        for lid, L in self.label_node.items():
            if L not in self.nodes:
                continue
            depth = {L: 0}
            via = defaultdict(set)      # node -> {(parent, value)}
            st = [L]
            while st:
                i = st.pop()
                for c, v in zip(self.nodes[i], self.val[i][0]):
                    if isinstance(c, str):
                        continue
                    if c in depth:
                        assert depth[c] == depth[i] + 1, ('depth clash', self.names[c])
                    else:
                        depth[c] = depth[i] + 1
                        st.append(c)
                    via[c].add((i, v))
            for i in depth:
                for j, c in enumerate(self.nodes[i]):
                    if isinstance(c, str) and '#' in c and c.startswith('_') and int(c.split('#')[1]) == lid:
                        kind = c[1:4]
                        h = depth[i]
                        self.ctl_depth[(i, j)] = h
                        # level e (h .. 1) erases the cell of the node at depth e - 1 on the path
                        frontier = {i}
                        for e in range(h, 0, -1):
                            nf = set()
                            for x in frontier:
                                for (p, v) in via[x]:
                                    if depth[p] == e - 1:
                                        self.erase[kind][e].add(v)
                                        nf.add(p)
                            frontier = nf
        # depth of the PC (cells used by nodes) and of the leaf cells
        memo = {}

        def h(i):
            if i not in memo:
                memo[i] = 1 + max([h(c) for c in self.nodes[i] if not isinstance(c, str)] + [0])
            return memo[i]
        self.pc_depth = h(self.root)          # cells 0 .. pc_depth - 1 hold node digits
        self.gap_min = self.pc_depth          # node cells 0 .. pc_depth - 1 are in the gap

    def number_registers(self):
        """Registers in the order of their first operation in a run from the start (the file is
        created lazily, so register r must not be used before r - 1): ksim.first_use."""
        import ksim
        self.reg_order = ksim.first_use(self)
        self.regno = {r: k for k, r in enumerate(self.reg_order)}

    # -- the machine ----------------------------------------------------------------------------
    def state_name(self, i):
        return f'n.{self.names[i]}'

    def emit(self):
        D, T = self.D, self.T
        tm = {}

        def put(q, r, w, d, n):
            assert (q, r) not in tm, (q, r)
            tm[(q, r)] = (w, d, n)
        sym = lambda v: v + 1

        def tgt(c):
            if isinstance(c, str):
                if is_op(c):
                    _, r, op = c.split('.')
                    return f'c{"inc" if op == "inc" else "dec"}{self.regno[r] + 1}'
                if c == 'halt':
                    return 'halt'
                raise ValueError(c)
            return self.state_name(c)
        root = self.state_name(self.root)
        self.root_state = root
        # boot: write the gap (1s on cells 0 .. G - 1, G >= gap_min), then dispatch
        if self.boot is None:
            G = self.gap_min
            for k in range(G):
                put(f'b{k}', 0, FRESH, 'R' if k < G - 1 else 'L', f'b{k + 1}' if k < G - 1 else 'scan')
            self.start_state = 'b0'
        else:
            table, G = boot_table(self.boot)
            assert G >= self.gap_min, (G, self.gap_min)
            for (q, r), t in table.items():
                put(q, r, *t)
            self.start_state = 'bA'
        self.G = G
        # nodes
        for i, sl in self.nodes.items():
            q = self.state_name(i)
            vals, writes, skip = self.val[i]
            for j, (c, v, w) in enumerate(zip(sl, vals, writes)):
                if isinstance(c, str) and c.startswith('_jmp:'):      # an inlined loop's continue
                    put(q, sym(v), sym(vals[int(c[5:])]), 'L', 'scan')
                elif c == '_done':                                    # an inlined label's break
                    put(q, sym(v), FRESH, 'L', 'adv')
                elif isinstance(c, str) and c.startswith('_'):
                    kind = c[1:4]
                    h = self.ctl_depth[(i, j)]
                    nxt = f'e{kind}{h}' if h else ('adv' if kind == 'brk' else 'scan')
                    put(q, sym(v), FRESH, 'L', nxt)
                else:
                    put(q, sym(v), sym(w), 'R', tgt(c))
            if skip is not None:
                put(q, sym(skip), sym(T), 'R', tgt(sl[-1]))
        # erase chains
        for kind in ('brk', 'cnt'):
            for e, vs in self.erase[kind].items():
                for v in vs:
                    nxt = f'e{kind}{e - 1}' if e > 1 else ('adv' if kind == 'brk' else 'scan')
                    put(f'e{kind}{e}', sym(v), FRESH, 'L', nxt)
        # advance: values that a finished child can leave on its parent's cell
        adv_vals = set()
        W, Wdec = set(), set()      # values register ops write (the return reads them)
        for i, sl in self.nodes.items():
            for c, w in zip(sl, self.val[i][1]):
                if is_op(c):
                    W.add(w)
                    if is_decnz(c):
                        Wdec.add(w)
                elif not is_ctl(c):
                    adv_vals.add(w)
        for v in sorted(adv_vals):
            if v == T:
                put('adv', sym(T), FRESH, 'L', 'adv')
            else:
                put('adv', sym(v), sym(v + 1), 'L', 'scan')
        put('adv', 0, 0, 'R', root)            # main is done: run it again
        # dispatch
        for v in range(D):
            put('scan', sym(v), sym(v), 'L', 'scan')
        put('scan', 0, 0, 'R', root)
        # registers
        R = len(self.reg_order)
        SEP = self.SEP
        for k, first in (('inc', 'carry1'), ('dec', 'dstart')):
            for j in range(1, R + 1):
                put(f'c{k}{j}', 1, 1, 'R', f'c{k}{j}')
                put(f'c{k}{j}', SEP, SEP, 'R', f'c{k}{j - 1}' if j > 1 else first)
            put(f'c{k}1', 0, SEP, 'R', first)         # the register is new: create it
        put('carry1', 1, 1, 'R', 'carry1')
        put('carry1', SEP, 1, 'R', 'carryS')
        put('carry1', 0, 1, 'L', 'retok')
        put('carryS', 1, SEP, 'R', 'carry1')
        put('carryS', SEP, SEP, 'R', 'carryS')
        put('carryS', 0, SEP, 'L', 'retok')
        put('dstart', 1, 1, 'R', 'dscan')
        put('dstart', SEP, SEP, 'L', 'retfail')
        put('dstart', 0, 0, 'L', 'retfail')
        put('dscan', 1, 1, 'R', 'dscan')
        put('dscan', SEP, 1, 'L', 'dput')
        put('dscan', 0, 0, 'L', 'dlast')
        put('dput', 1, SEP, 'R', 'dscan')
        put('dlast', 1, 0, 'L', 'retok')
        # the returns run left over the registers and the gap to the op's node cell
        for q in ('retok', 'retfail'):
            put(q, 1, 1, 'L', q)
            put(q, SEP, SEP, 'L', q)
        for w in sorted(W):           # done: advance this cell
            put('retok', sym(w), sym(w + 1) if w < T else FRESH, 'L', 'scan' if w < T else 'adv')
        for w in sorted(Wdec):        # a decnz found 0: the node is done
            put('retfail', sym(w), FRESH, 'L', 'adv')
        self.tm = tm

    # -- output ----------------------------------------------------------------------------------
    def named(self):
        """(order, table) in the repository's named-state format, the start state first"""
        import re
        qs = sorted({q for q, _ in self.tm})
        qs.remove(self.start_state)
        qs = [self.start_state] + qs
        clean = {}
        for q in qs:
            c = re.sub(r'[^A-Za-z0-9_]', '_', q)
            c = 'S_' + c if c[0].isdigit() else c
            while c in clean.values():
                c += '_'
            clean[q] = c
        nsym = self.D + 2
        table = {}
        for q in qs:
            row = []
            for r in range(nsym):
                t = self.tm.get((q, r))
                row.append(None if t is None else (t[0], t[1], clean.get(t[2], 'halt')))
            table[clean[q]] = row
        return [clean[q] for q in qs], table, clean

    def write_named(self, path, header=''):
        order, table, _ = self.named()
        out = [header.rstrip()] if header else []
        out.append('blank_symbol: 0')
        for n in order:
            out.append(n)
            for r, t in enumerate(table[n]):
                out.append('  -' if t is None else f'  {r} {t[0]} {t[1]} {t[2]}')
        with open(path, 'w') as f:
            f.write('\n'.join(out) + '\n')

    # -- reports ----------------------------------------------------------------------------------
    def count(self):
        return len(self.tm)

    def states(self):
        return sorted({q for q, _ in self.tm})

    def breakdown(self):
        cat = Counter()
        for (q, r) in self.tm:
            if q.startswith('n.'):
                cat['nodes'] += 1
            elif q in ('scan', 'adv'):
                cat[q] += 1
            elif q.startswith('e'):
                cat['erase'] += 1
            elif q.startswith('cinc') or q.startswith('cdec'):
                cat['chains'] += 1
            elif q.startswith('b') and (q[1:].isdigit() or len(q) == 2):
                cat['boot'] += 1
            else:
                cat['regops'] += 1
        return dict(cat)


if __name__ == '__main__':
    for D in map(int, sys.argv[1:] or [4, 6, 8, 10, 12, 16]):
        c = Compiler(D)
        print(f'D={D} symbols={D + 2}: {len(c.states())} states, {c.count()} instructions, '
              f'pc depth {c.pc_depth}, {c.breakdown()}')
