"""k215P as a binary DAG with its sequences re-bracketed by a grammar (input of compiler.py).

program.DAG keeps Glazer's trie shape.  Most of k215P is a few long sequences of blocks (one has
933 items) that the trie brackets as a balanced binary tree.  Here only the *semantic* trie nodes
are kept: the root, every control target (break/continue), and every decnz scope.  Each such
node's children, read through the other (transparent) trie nodes, form an item sequence; a
grammar over all these sequences (greedy textual substitution, cost = slots of the kary nodes)
re-brackets them.  The unfolded tree is then rebuilt with each control leaf's target fixed
absolutely, the relative levels recomputed, and hash-consed into a DAG with program.DAG's
interface (nodes, root, prefix, synth, pc_ir, leaf_kind, walk).
"""
import json, os, sys
from collections import Counter, defaultdict
sys.setrecursionlimit(100000)
HERE = os.path.dirname(os.path.abspath(__file__))
from program import P, NP

GRAMMAR = os.path.join(HERE, 'grammar.json')


# ---------------------------------------------------------------- the trie, semantically
def semantic():
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
    leaves = {}          # trie leaf path -> (kind, arg, target trie path or None)
    targets = {()}
    for i, e in enumerate(P):
        p, t = paths[i], e['tag']
        if t == 0:
            leaves[p] = ('inc', e['arg'], None)
        elif t == 4:
            leaves[p] = ('halt', None, None)
        elif t == 1:
            c = [a for a in anc(p) if after(a) == e['zero']]
            targets.add(p[:-1])
            if len(p) - len(c[0]) == 1:
                leaves[p] = ('dec', e['arg'], None)
            else:
                leaves[p] = ('decX', e['arg'], c[0])
                targets.add(c[0])
        elif t == 2:
            c = [a for a in anc(p) if after(a) == e['zero']]
            leaves[p] = ('brk', None, c[0])
            targets.add(c[0])
        elif t == 3:
            c = [a for a in anc(p) if first(a) == e['zero']]
            leaves[p] = ('cnt', None, c[0])
            targets.add(c[0])
    return paths, leaves, targets


def items(a, leaves, targets):
    """the children of trie node a read through transparent trie nodes"""
    out = []
    for b in (a + (0,), a + (1,)):
        if b in leaves or b in targets:
            out.append(b)
        else:
            out += items(b, leaves, targets)
    return out


# ---------------------------------------------------------------- signatures (for the grammar)
def signatures(paths, leaves, targets):
    """a context-free name for every semantic node and leaf, so that equal subprograms get the
    same name: leaves by kind and the number of semantic levels to their target"""
    sig, memo = {}, {}

    def lvl(p, a):
        return sum(1 for j in range(len(a), len(p)) if p[:j] in targets)

    def name(x):
        if x in leaves:
            k, arg, tg = leaves[x]
            return (k, arg, None if tg is None else lvl(x, tg))
        if x not in sig:
            body = tuple(name(y) for y in items(x, leaves, targets))
            if body not in memo:
                memo[body] = len(memo)
            sig[x] = ('S', memo[body])
        return sig[x]
    name(())
    bodies = {v: list(k) for k, v in memo.items()}
    return sig, bodies, name


# ---------------------------------------------------------------- the grammar
def rcost(n):
    """transitions of a kary node of n child slots"""
    return n + (1 if n >= 3 else 0)


def greedy_grammar(seqs, pinned, D, maxlen=None, verbose=False):
    """greedy textual substitution over a dict of sequences.  pinned[name] = number of leading
    items that must stay in place (a decnz).  Returns (seqs', rules) with rules[('R', i)] = body."""
    maxlen = maxlen or D
    seqs = {k: list(v) for k, v in seqs.items()}
    rules = {}
    nid = 0
    while True:
        cnt = Counter()
        where = defaultdict(list)
        for key, s in list(seqs.items()) + list(rules.items()):
            lo = pinned.get(key, 0)
            for i in range(lo, len(s)):
                for L in range(2, maxlen + 1):
                    if i + L > len(s):
                        break
                    w = tuple(s[i:i + L])
                    where[w].append((key, i))
        best = None
        for w, occ in where.items():
            # non-overlapping occurrences, left to right per sequence
            k, last = 0, {}
            for key, i in occ:
                if i >= last.get(key, -1):
                    k += 1
                    last[key] = i + len(w)
            if k < 2:
                continue
            gain = k * (len(w) - 1) - rcost(len(w))
            if best is None or gain > best[0] or (gain == best[0] and len(w) > len(best[1])):
                best = (gain, w)
        if best is None or best[0] <= 0:
            break
        w = best[1]
        r = ('R', nid)
        nid += 1

        def sub(s, lo):
            out, i = list(s[:lo]), lo
            while i < len(s):
                if tuple(s[i:i + len(w)]) == w:
                    out.append(r)
                    i += len(w)
                else:
                    out.append(s[i])
                    i += 1
            return out
        for key in list(seqs):
            seqs[key] = sub(seqs[key], pinned.get(key, 0))
        for key in list(rules):
            rules[key] = sub(rules[key], 0)
        rules[r] = list(w)
        if verbose:
            print('rule', r, len(w), 'gain', best[0], file=sys.stderr)
    # inline rules used once
    use = Counter()
    for s in list(seqs.values()) + list(rules.values()):
        for x in s:
            if x in rules:
                use[x] += 1

    def expand(s):
        out = []
        for x in s:
            if x in rules and use[x] == 1:
                out += expand(rules[x])
            else:
                out.append(x)
        return out
    rules2 = {r: expand(b) for r, b in rules.items() if use[r] > 1}
    seqs2 = {k: expand(s) for k, s in seqs.items()}
    return seqs2, rules2


def make_grammar(D, verbose=False):
    paths, leaves, targets = semantic()
    sig, bodies, name = signatures(paths, leaves, targets)
    seqs = {('S', k): v for k, v in bodies.items()}
    pinned = {k: 1 for k, v in seqs.items() if v and v[0][0] in ('dec', 'decX')}
    s2, rules = greedy_grammar(seqs, pinned, D, verbose=verbose)
    tot = sum(rcost(len(v)) for v in s2.values()) + sum(rcost(len(v)) for v in rules.values())
    if verbose:
        print('grammar: before', sum(rcost(len(v)) for v in seqs.values()), 'after', tot,
              len(rules), 'rules', file=sys.stderr)
    return {'seqs': {str(k[1]): [list(x) for x in v] for k, v in s2.items()},
            'rules': {str(k[1]): [list(x) for x in v] for k, v in rules.items()}}


# ---------------------------------------------------------------- the DAG
class DAG:
    """program.DAG's interface, over the re-bracketed tree"""
    def __init__(self, prologue=0, grammar=None, shape='right', D=11):
        paths, leaves, targets = semantic()
        sig, bodies, name = signatures(paths, leaves, targets)
        if grammar is None:
            grammar = json.load(open(GRAMMAR))
        gseqs = {('S', int(k)): [tuple(x) for x in v] for k, v in grammar['seqs'].items()}
        grules = {('R', int(k)): [tuple(x) for x in v] for k, v in grammar['rules'].items()}
        # unfolded tree: objects are lists [kind, ...]; internal nodes ['n', car, cdr]
        # leaves ['l', kind, arg, target trie path, pc]
        obj_of = {}           # target trie path -> object
        pc_obj = {}

        def chain(xs):
            if len(xs) == 1:
                return xs[0]
            if shape == 'right':
                return ['n', xs[0], chain(xs[1:])]
            h = len(xs) // 2
            return ['n', chain(xs[:h]), chain(xs[h:])]

        def group(parts):
            """a long sequence as a top node of at most D slots: a leading decnz and a trailing
            control leaf stay on top, the middle is cut into equal groups (recursively)"""
            if len(parts) <= D:
                return parts
            head = parts[:1] if parts[0][0] == 'l' and parts[0][1] in ('dec',) else []
            tail = parts[-1:] if parts[-1][0] == 'l' and parts[-1][1] in ('brk', 'cnt') else []
            mid = parts[len(head):len(parts) - len(tail)]
            room = D - len(head) - len(tail)
            k = -(-len(mid) // D)
            while k > room:
                k = room
            k = max(k, 2)
            sz = -(-len(mid) // k)
            groups = [mid[i:i + sz] for i in range(0, len(mid), sz)]
            return head + [chain(group(g)) if len(g) > 1 else g[0] for g in groups] + tail

        def build_target(a):
            its = items(a, leaves, targets)
            names = [name(x) for x in its]
            seq = gseqs[name(a)]
            # match the grammar's expansion against the items
            pos = [0]

            def realize(sym):
                if sym in grules:
                    return chain([realize(x) for x in grules[sym]])
                x = its[pos[0]]
                assert name(x) == sym, (a, pos[0], name(x), sym)
                pos[0] += 1
                return build_item(x)
            parts = [realize(x) for x in seq]
            assert pos[0] == len(its)
            o = chain(group(parts))
            obj_of[a] = o
            return o

        def build_item(x):
            if x in leaves:
                k, arg, tg = leaves[x]
                pc = leaf_pc[x]
                if k == 'decX':
                    # X = (Z, brk -> tg), Z = (dec r, brk -> X)
                    d = ['l', 'dec', arg, None, pc]
                    Z = ['n', d, None]
                    Xo = ['n', Z, ['l', 'brk', None, tg, None]]
                    Z[2] = ['l', 'brkobj', None, Xo, None]
                    pc_obj[pc] = d
                    return Xo
                lf = ['l', k, arg, tg, pc]
                pc_obj[pc] = lf
                return lf
            return build_target(x)
        leaf_pc = {p: i for i, p in enumerate(paths)}
        root = build_target(())
        # depths and bit paths
        depth, bitp = {}, {}
        st = [(root, 0, ())]
        while st:
            o, dd, bits = st.pop()
            depth[id(o)] = dd
            bitp[id(o)] = bits
            if o[0] == 'n':
                st.append((o[1], dd + 1, bits + (0,)))
                st.append((o[2], dd + 1, bits + (1,)))
        # hash-cons
        self.nodes = []
        memo = {}

        def intern(car, cdr):
            k = (car, cdr)
            if k not in memo:
                memo[k] = len(self.nodes)
                self.nodes.append(k)
            return memo[k]

        def hc(o):
            if o[0] == 'n':
                return intern(hc(o[1]), hc(o[2]))
            _, k, arg, tg, pc = o
            if k in ('inc', 'dec'):
                return (k, arg)
            if k == 'halt':
                return ('halt',)
            if k == 'brkobj':
                return ('brk', depth[id(o)] - depth[id(tg)])
            to = obj_of[tg]
            return (k, depth[id(o)] - depth[id(to)])
        self.root = hc(root)
        self.semantic = {hc(o) for o in obj_of.values()}
        self.prefix = ()
        self.synth = []
        if prologue:
            r = intern(self.root, ('cnt', 1))
            self.synth.append((1,) * prologue + (1,))
            for _ in range(prologue):
                r = intern(('inc', 0), r)
            self.synth += [(1,) * i + (0,) for i in range(prologue)]
            self.root = r
            self.prefix = (1,) * prologue + (0,)
        self.pc_ir = [self.prefix + bitp[id(pc_obj[pc])] for pc in range(NP)]
        self.leaf_kind = [(leaves[p][0],) + ((leaves[p][1],) if leaves[p][0] != 'brk' else ()) for p in paths]
        self.depth_max = max(len(b) for b in self.pc_ir)

    def walk(self, bits):
        out, n = [], self.root
        for b in bits:
            out.append((n, b))
            n = self.nodes[n][b]
        return out, n


if __name__ == '__main__':
    D = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    g = make_grammar(D, verbose=True)
    json.dump(g, open(GRAMMAR, 'w'))
    d = DAG(prologue=4)
    print(len(d.nodes), 'nodes; IR depth', d.depth_max)
