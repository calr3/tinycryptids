"""Abstract interpreter for kary.py's machines (cf. ../pa/dagsim.py).

The program counter is run with the machine's own transitions (nodes, adv, scan, the erase
states); a register op (a node's transition into a chain state) is executed in one step on
registers kept as integers, followed by the return's transition on the node's cell (`retok`,
or `retfail` when a decnz finds 0).  The register file, the chains and the return's run over
them are checked on the real machine (kevents.py).

Accelerations, as in dagsim: a repeated PC whose register operations since its last visit were
incs and successful decnzs of distinct registers is iterated in one step, and a fresh entry
into a pair/unpair node is applied by formula (check_accel.py)."""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'pa'))
from dagsim import pair, unpair, mpz

FRESH = 1
PAIR = re.compile(r'^n\.pair\((\w+),(\w+),(\w+)\)\.0$')
UNPAIR = re.compile(r'^n\.unpair\((\w+),(\w+),(\w+)\)\.0$')
CHAIN = re.compile(r'^c(inc|dec)(\d+)$')    # entered from a node: a register op


class Halted(Exception):
    pass


class KSim:
    def __init__(self, c, accel=True, accel_sub=True, strict=True):
        self.c = c
        self.tm = c.tm
        self.root = c.root_state
        regs = sorted({x.split('.')[1] for sl in c.nodes.values() for x in sl
                       if isinstance(x, str) and x.startswith('3.')})
        self.reg = {r: mpz(0) for r in regs}
        self.pc = []
        self.accel, self.accel_sub, self.strict = accel, accel_sub, strict
        self.ops, self.seen = [], {}
        self.last_leaf = ()
        self.nops = 0
        self.iterations = 0
        self.trace = None           # list of (register, op, ok) if not None (no acceleration)

    def get(self, i):
        return self.pc[i] if i < len(self.pc) else FRESH

    def set(self, i, s):
        while len(self.pc) <= i:
            self.pc.append(FRESH)
        self.pc[i] = s

    def strip(self):
        while self.pc and self.pc[-1] == FRESH:
            self.pc.pop()

    def run_ctl(self, q, pos):
        """Run adv / scan / erase states from (q, pos) until the next dispatch."""
        while True:
            if q == 'scan':
                self.strip()
                return
            assert pos >= 0, q
            w, d, n = self.tm[(q, self.get(pos))]
            self.set(pos, w)
            pos += 1 if d == 'R' else -1
            if pos < 0:             # the blank before cell 0
                w, d, n2 = self.tm[(n, 0)]
                assert n2 == self.root and d == 'R', n
                if n == 'adv':      # main is done
                    self.iterations += 1
                self.strip()
                return
            q = n

    def step(self):
        self.strip()
        key = tuple(self.pc)
        if self.accel:
            self.try_loop(key)
        q, pos = self.root, 0
        while True:
            s = self.get(pos)
            if self.accel_sub and pos >= len(self.pc) and self.try_sub(q, pos):
                return
            w, d, n = self.tm[(q, s)]
            self.set(pos, w)
            pos += 1 if d == 'R' else -1
            if n == 'halt':
                raise Halted()
            m = CHAIN.match(n)
            if m:
                op, j = m.groups()
                r = self.c.reg_order[int(j) - 1]
                assert self.get(pos) == FRESH and d == 'R' and w != FRESH
                self.last_leaf = tuple(self.pc[:pos])
                ok = True
                if op == 'inc':
                    self.reg[r] += 1
                elif self.reg[r] > 0:
                    self.reg[r] -= 1
                else:
                    ok = False
                self.ops.append((r, op, ok))
                if self.trace is not None:
                    self.trace.append((r, op, ok))
                self.nops += 1
                self.run_ctl('retok' if ok else 'retfail', pos - 1)
                return
            if d == 'L':
                self.run_ctl(n, pos)
                return
            q = n

    def try_loop(self, key):
        j = self.seen.get(key)
        self.seen[key] = len(self.ops)
        if j is None:
            if len(self.ops) > 5000:
                self.ops.clear()
                self.seen = {key: 0}
            return
        seg = self.ops[j:]
        if not seg or not all(ok for _, _, ok in seg):
            return
        dec = [r for r, op, _ in seg if op == 'dec']
        inc = [r for r, op, _ in seg if op == 'inc']
        if not dec or len(set(dec)) != len(dec) or set(dec) & set(inc):
            return
        k = min(self.reg[r] for r in dec)
        if k == 0:
            return
        for r in dec:
            self.reg[r] -= k
        for r in inc:
            self.reg[r] += k
        self.nops += k * len(seg)
        self.ops.clear()
        self.seen = {key: 0}

    def try_sub(self, q, pos):
        m = PAIR.match(q) or UNPAIR.match(q)
        if not m:
            return False
        path = tuple(self.pc[:pos])
        if len(self.last_leaf) > pos and self.last_leaf[:pos] == path:
            return False
        x, y, z = m.groups()
        R = self.reg
        if self.trace is not None:      # first touches, in the order the plain run makes them
            self.trace += [(r, 'sub', True) for r in ((y, z, x) if PAIR.match(q) else (z, x, y))]
        if PAIR.match(q):
            R[x] += pair(R[y], R[z])
            R[y] = R[z] = 0
        else:
            if R[x] or R[y]:
                if self.strict:
                    raise AssertionError(f'{q} entered with {x}={R[x]}, {y}={R[y]}')
                return False
            R[x], R[y] = unpair(R[z])
            R[z] = 0
        self.nops += 1
        self.last_leaf = path + (FRESH,)
        self.ops.clear()
        self.seen = {}
        self.run_ctl('adv', pos - 1)
        return True

    def run_iterations(self, n, maxsteps=10**7):
        target = self.iterations + n
        steps = 0
        while self.iterations < target:
            self.step()
            steps += 1
            if steps > maxsteps:
                raise RuntimeError('too many dispatches')
        return steps


def first_use(c, plain=10**5):
    """Registers in the order of their first operation, running from the start (the first
    `plain` dispatches without accelerations, then with them)."""
    sim = KSim(c, accel=False, accel_sub=False)
    sim.trace = []
    order = []
    n = 0
    while len(order) < len(sim.reg):
        if n == plain:
            sim.accel = sim.accel_sub = True
        sim.step()
        n += 1
        for r, _, _ in sim.trace:
            if r not in order:
                order.append(r)
        sim.trace.clear()
        assert sim.iterations < 3, ('registers never used', set(sim.reg) - set(order))
    return order
