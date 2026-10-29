"""Abstract interpreter for machines built by tmbuilder.py.

It runs the machine's own transitions for the decision DAG, the root (5.root.*) and the
program-counter states (6.break.*, 6.continue.*) on the program counter (PC, a list of bits),
but keeps the registers as Python integers: a register leaf `3.R.inc` / `3.R.decnz` is executed
in one step, followed by the framework's return (`6.break.0` on success, `6.break.1` when a
decnz finds 0).  The framework's register file (2b.*, 2c.*, 2e.*, 1b.*), dispatch (4.*) and boot
(0*.*) are not run here; tm_events.py checks them on the real machine.

Two accelerations make main-loop iterations with huge register values feasible:
  * loops: when a dispatch sees the same PC again and every register operation since its last
    visit was an inc or a successful decnz, with each decremented register decremented once and
    never incremented, the next iterations repeat exactly until one of those registers is 0;
    they are applied in one step (k = the least of those registers).
  * pair/unpair subroutines (by state name), entered afresh: their effect on the registers is
    applied by formula (check_accel.py compares this with plain execution on small values).
"""
import re
try:                        # optional: GMP arithmetic is much faster on the huge values
    from gmpy2 import mpz, isqrt
except ImportError:
    from math import isqrt
    mpz = int

LEAF = re.compile(r'^3\.(\w+)\.(inc|decnz)$')
CTL = re.compile(r'^6\.(break|continue)\.\d+$')
PAIR = re.compile(r'^pair\((\w+),(\w+),(\w+)\)\.0$')
UNPAIR = re.compile(r'^unpair\((\w+),(\w+),(\w+)\)\.0$')


def tri(n):
    return n * (n + 1) // 2


def pair(a, b):
    """The builder's pairing: pair(out, a, b) adds this to out."""
    return tri(a + b) + a


def unpair(n):
    """Inverse of pair."""
    # s = a + b is the largest s with tri(s) <= n
    s = (isqrt(8 * mpz(n) + 1) - 1) // 2
    a = n - tri(s)
    return a, s - a


class Halted(Exception):
    pass


class DagSim:
    def __init__(self, states, registers, accel=True, accel_sub=True, strict=True):
        """states: tmbuilder's tm.states dict {(state, '0'|'1'): Transition}.
        strict: an unpair entered with nonzero outputs is an error (the programs never do it, and
        run plainly it would take astronomically long), not a fall back to plain execution."""
        self.strict = strict
        self.d = states
        self.reg = {r: mpz(0) for r in registers}
        self.pc = [1, 1]
        self.accel = accel
        self.accel_sub = accel_sub
        self.ops = []            # (register, op, ok) since the last loop-acceleration reset
        self.seen = {}           # PC -> index into ops
        self.last_leaf = ()      # path bits of the last executed leaf
        self.nops = 0            # register operations executed (accelerated ones counted)
        self.iterations = 0
        self.halted = False

    # -- program counter --------------------------------------------------------------------
    def bit(self, i):
        return self.pc[i] if i < len(self.pc) else 0

    def setbit(self, i, b):
        while len(self.pc) <= i:
            self.pc.append(0)
        self.pc[i] = b

    def strip(self):
        while self.pc and self.pc[-1] == 0:
            self.pc.pop()

    def walk(self, state, pos):
        """Run 6.break/6.continue transitions from (state, pos) until the machine leaves them
        (to 2e.reg.cleanup_1 after a break, or to dispatch after a continue)."""
        while CTL.match(state):
            t = self.d[(state, str(self.bit(pos)))]
            self.setbit(pos, int(t.write))
            pos += 1 if t.direction == 'R' else -1
            state = t.nextstate
            assert pos >= 0
        assert state == '2e.reg.cleanup_1' or state.startswith('4.dispatch.'), state
        self.strip()

    # -- one dispatch -----------------------------------------------------------------------
    def step(self):
        """Dispatch once from the root: execute one register leaf (or one pc jump)."""
        self.strip()
        key = tuple(self.pc)
        if self.accel:
            self.try_loop(key)
        state, pos = '5.root.1', 1
        while True:
            b = self.bit(pos)
            if self.accel_sub and b == 0 and pos >= len(self.pc) and self.try_sub(state, pos):
                return
            t = self.d[(state, str(b))]
            self.setbit(pos, int(t.write))
            pos += 1 if t.direction == 'R' else -1
            nxt = t.nextstate
            if nxt == 'halt':
                self.halted = True
                raise Halted()
            m = LEAF.match(nxt)
            if m:
                r, op = m.groups()
                self.last_leaf = tuple(self.pc[:pos])
                ok = True
                if op == 'inc':
                    self.reg[r] += 1
                elif self.reg[r] > 0:
                    self.reg[r] -= 1
                else:
                    ok = False
                self.ops.append((r, op, ok))
                self.nops += 1
                self.walk('6.break.0' if ok else '6.break.1', pos - 1)
                return
            if CTL.match(nxt):
                self.walk(nxt, pos)
                return
            assert t.direction == 'R' and not nxt[0].isdigit() or nxt.startswith('5.root'), (state, b, t)
            state = nxt

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
        dec = [r for r, op, _ in seg if op == 'decnz']
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

    def try_sub(self, state, pos):
        """At a fresh entry into a pair/unpair subroutine node, apply it by formula."""
        m = PAIR.match(state) or UNPAIR.match(state)
        if not m:
            return False
        path = tuple(self.pc[:pos])
        if len(self.last_leaf) > pos and self.last_leaf[:pos] == path:
            return False          # re-entered by the subroutine's own loop: not a fresh entry
        x, y, z = m.groups()
        R = self.reg
        if PAIR.match(state):
            out, a, b = x, y, z
            R[out] += pair(R[a], R[b])
            R[a] = R[b] = 0
        else:
            o1, o2, n = x, y, z
            if R[o1] or R[o2]:
                if self.strict:
                    raise AssertionError(f'{state} entered with {o1}={R[o1]}, {o2}={R[o2]}')
                return False
            R[o1], R[o2] = unpair(R[n])
            R[n] = 0
        self.nops += 1
        self.last_leaf = path + (0,)
        self.ops.clear()
        self.seen = {}
        self.walk('6.break.0', pos - 1)     # the node at this path is complete
        return True

    # -- main loop --------------------------------------------------------------------------
    def run_iterations(self, n, maxsteps=10**7):
        """Run until n more main-loop iterations have completed (or halt)."""
        target = self.iterations + n
        steps = 0
        while self.iterations < target:
            self.step()
            steps += 1
            if self.pc == [1, 1, 1]:          # main() is complete: the root bit is set
                self.iterations += 1
            if steps > maxsteps:
                raise RuntimeError('too many dispatches')
        return steps
