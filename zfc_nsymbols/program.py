"""Glazer's register program k215P as a binary DAG (input of compiler.py).

The program: k215P's table (prog.json), a binary trie of 4751 leaves (inc, decnz, break,
continue, halt) whose control leaves have explicit targets.  Every control target is an
ancestor of the leaf; a decnz whose zero target is not "finish my parent" (4 leaves) is
rewritten as  X = (Z, brk -> A),  Z = (decnz r, brk -> X).

Relative hash-consing gives a binary DAG; single-parent children are merged into their
parents (D-ary nodes, as in pa_nsymbols/kary.py) where the semantics allow.  Control slots are
relative (erase h cells), so sharing is kept.

Tape (0 blank, digit v = symbol v + 1, SEP = D + 1):
    0 [PC digits] 1 1 ... 1 [SEP 1^r_0] ... [SEP 1^r_8] 0 ...
"""
import json, sys, os, collections
from collections import defaultdict, Counter
sys.setrecursionlimit(100000)
HERE = os.path.dirname(os.path.abspath(__file__))
P = json.load(open(os.path.join(HERE, 'k215p.json')))
NP = len(P)
FRESH = 1


# ---------------------------------------------------------------- the trie with explicit targets
def trie():
    paths = [tuple(e['path']) for e in P]
    leaf_of = {p: i for i, p in enumerate(paths)}
    rng = {}
    for i, p in enumerate(paths):
        for j in range(len(p)):
            a = p[:j]
            lo, hi = rng.get(a, (i, i))
            rng[a] = (min(lo, i), max(hi, i))
    after = lambda a: (rng[a][1] + 1) % NP
    first = lambda a: rng[a][0]
    anc = lambda p: [p[:j] for j in range(len(p) - 1, -1, -1)]
    # leaf -> IR leaf; control targets as "k levels up"
    leaves = {}
    for i, e in enumerate(P):
        p = paths[i]
        t = e['tag']
        if t == 0:
            leaves[p] = ('inc', e['arg'])
        elif t == 4:
            leaves[p] = ('halt',)
        elif t == 1:
            c = [a for a in anc(p) if after(a) == e['zero']]
            k = len(p) - len(c[0])
            leaves[p] = ('dec', e['arg']) if k == 1 else ('decX', e['arg'], k)
        elif t == 2:
            c = [a for a in anc(p) if after(a) == e['zero']]
            leaves[p] = ('brk', len(p) - len(c[0]))       # deepest candidate
        elif t == 3:
            c = [a for a in anc(p) if first(a) == e['zero']]
            leaves[p] = ('cnt', len(p) - len(c[0]))
    return paths, leaves


class DAG:
    """Binary DAG, relative hash-consing.  node id -> (car, cdr); a child is an int (node) or a
    leaf tuple.  pc_path[pc] = the sequence of (node, bit) from the root to pc's leaf (the
    IR path; a decX leaf's IR path ends at its rewritten dec leaf)."""
    def __init__(self, prologue=0):
        paths, leaves = trie()
        self.nodes = []
        memo = {}

        def intern(car, cdr):
            k = (car, cdr)
            if k not in memo:
                memo[k] = len(self.nodes)
                self.nodes.append(k)
            return memo[k]

        def build(a):
            if a in leaves:
                lf = leaves[a]
                if lf[0] == 'decX':
                    # X = (Z, brk k+1), Z = (dec r, brk 2)
                    z = intern(('dec', lf[1]), ('brk', 2))
                    return intern(z, ('brk', lf[2] + 1))
                return lf
            return intern(build(a + (0,)), build(a + (1,)))
        self.root = build(())
        self.prefix = ()
        self.synth = []          # IR paths of the prologue's leaves (not k215P pcs)
        if prologue:
            # root' = inc r0 (inc r0 ... (L)),  L = (old root, cnt -> L)
            r = intern(self.root, ('cnt', 1))
            self.synth.append((1,) * prologue + (1,))
            for _ in range(prologue):
                r = intern(('inc', 0), r)
            self.synth += [(1,) * i + (0,) for i in range(prologue)]
            self.root = r
            self.prefix = (1,) * prologue + (0,)
        self.pc_ir = []          # IR bit path of each pc's leaf
        for i, p in enumerate(paths):
            self.pc_ir.append(self.prefix + p + ((0, 0) if leaves[p][0] == 'decX' else ()))
        self.leaf_kind = [leaves[p] for p in paths]

    def walk(self, bits):
        """the nodes along an IR path: [(node, bit), ...] and the leaf"""
        out, n = [], self.root
        for b in bits:
            out.append((n, b))
            n = self.nodes[n][b]
        return out, n


def is_ctl(s):
    return isinstance(s, tuple) and s[0] in ('brk', 'cnt', 'halt', 'jmp', 'done')


def is_op(s):
    return isinstance(s, tuple) and s[0] in ('inc', 'dec')


def is_dec(s):
    return isinstance(s, tuple) and s[0] == 'dec'


def first_use_order():
    regs = [4] + [0] * 8
    pc, order = 0, [0]
    for _ in range(10**6):
        e = P[pc]
        if e['tag'] in (0, 1) and e['arg'] not in order:
            order.append(e['arg'])
        if len(order) == 9:
            break
        if e['tag'] == 0:
            regs[e['arg']] += 1
            pc = e['pos']
        elif e['tag'] == 1:
            if regs[e['arg']]:
                regs[e['arg']] -= 1
                pc = e['pos']
            else:
                pc = e['zero']
        else:
            pc = e['zero']
    return order


