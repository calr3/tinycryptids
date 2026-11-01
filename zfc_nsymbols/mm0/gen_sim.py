"""Proof generator: symbolic configurations of the machine and proofs of reachability.

Terms mirror the MM0 ones: kzPush c t, kzRep 1 n t, leaves (variables, 0).  A proof is a list of
segments, folded right to left:
  ('S', h, cfg)   h: kzStep a = b                 ('E', h, cfg)  h: a = b (conversion)
  ('R', h, cfg)   h: kzReach a b                  ('P', h, cfg)  h: kzReachP a b
  ('SE', h, cfg)  h: kzStep a = kzStep b, then the rest from b (must be kzReachP)
where cfg is the configuration after the segment.
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_spec
from gen_spec import num


# ---------------------------------------------------------------- terms
class T:
    pass


class Push(T):
    def __init__(self, c, t):
        self.c, self.t = c, t

    def __str__(self):
        return f'(kzPush {num(self.c)} {self.t})'

    def __eq__(self, o):
        return isinstance(o, Push) and o.c == self.c and o.t == self.t


class Rep(T):
    """kzRep 1 n t, n an int (a numeral) or a string (an MM0 nat expression)"""
    def __init__(self, n, t):
        self.n, self.t = n, t

    def __str__(self):
        return f'(kzRep 1 {snum(self.n)} {self.t})'

    def __eq__(self, o):
        return isinstance(o, Rep) and o.n == self.n and o.t == self.t


class Leaf(T):
    def __init__(self, s):
        self.s = s

    def __str__(self):
        return self.s

    def __eq__(self, o):
        return isinstance(o, Leaf) and o.s == self.s


ZERO = Leaf('0')


class Cfg:
    """kind: 'st' kzState q l r | 'ls' kzLS q l r | 'pend' kzPend c1 cS l r"""
    def __init__(self, kind, q, l, r):
        self.kind, self.q, self.l, self.r = kind, q, l, r

    def __str__(self):
        if self.kind == 'st':
            return f'(kzState {qnum(self.q)} {self.l} {self.r})'
        if self.kind == 'ls':
            return f'(kzLS {qnum(self.q)} {self.l} {self.r})'
        c1, cS = self.q
        return f'(kzPend {num(c1)} {num(cS)} {self.l} {self.r})'


def qnum(q):
    return 'kzH' if q == 'H' else num(q)


def snum(n):
    """a numeral expression for a concrete count, or the expression itself"""
    return num(n) if isinstance(n, int) else n


# ---------------------------------------------------------------- folding
def fold(segs):
    """fold segments into a proof of kzReach / kzReachP (kind returned)"""
    acc, kind = None, None
    for typ, h, _ in reversed(segs):
        if typ == 'S':
            if acc is None:
                acc, kind = f'(kzRP_end {h})', 'P'
            elif kind == 'R':
                acc, kind = f'(kzRP_st {h} {acc})', 'P'
            else:
                acc, kind = f'(kzRP_stP {h} {acc})', 'P'
        elif typ == 'E':
            if acc is None:
                acc, kind = f'(kzR_cv {h} kzReach_refl)', 'R'
            elif kind == 'R':
                acc = f'(kzR_cv {h} {acc})'
            else:
                acc = f'(kzRP_cv {h} {acc})'
        elif typ == 'R':
            if acc is None:
                acc, kind = h, 'R'
            elif kind == 'R':
                acc = f'(kzR_RR {h} {acc})'
            else:
                acc, kind = f'(kzR_RP {h} {acc})', 'P'
        elif typ == 'P':
            if acc is None:
                acc, kind = h, 'P'
            elif kind == 'R':
                acc, kind = f'(kzRP_RR {h} {acc})', 'P'
            else:
                acc, kind = f'(kzRP_RP {h} {acc})', 'P'
        elif typ == 'SE':
            assert kind == 'P', 'a step-equality needs a strict rest'
            acc = f'(kzRP_stepeq {h} {acc})'
        else:
            raise ValueError(typ)
    return acc, kind


# ---------------------------------------------------------------- the machine
class Mach:
    def __init__(self, D):
        self.D = D
        self.m, self.qs, self.idx = gen_spec.machine_numbers(D)
        self.K, self.S = D + 2, D + 1
        self.reg_order = self.m.reg_order
        self.G = self.m.G
        self.tm = self.m.tm

    def q(self, name):
        return self.idx[name]

    def act(self, qn, b):
        """the transition of state number qn on symbol b: (w, 'L'/'R', target number or 'H')"""
        w, d, t = self.tm[(self.qs[qn], b)]
        return w, d, ('H' if t == 'halt' else self.idx[t])

    def A(self, qn, b):
        return f'kzA_{qn}_{b}'

    def hq(self, qn):
        return f'kzLtH_{qn}'

    def hb(self, b):
        return f'kzLtK_{b}'

    # one concrete step on a configuration whose head cell is explicit
    def step(self, cfg):
        """('S', proof, new cfg) for kzState q l (kzPush b r); left moves need l = kzPush c l'
        (or give an LS configuration)"""
        assert cfg.kind == 'st' and isinstance(cfg.r, Push), cfg
        b = cfg.r.c
        w, d, t = self.act(cfg.q, b)
        if d == 'R':
            h = f'(kzSR {self.hq(cfg.q)} {self.hb(b)} {self.A(cfg.q, b)})'
            return ('S', h, Cfg('st', t, Push(w, cfg.l), cfg.r.t))
        h = f'(kzSLg {self.hq(cfg.q)} {self.hb(b)} {self.A(cfg.q, b)})'
        return ('S', h, Cfg('ls', t, cfg.l, Push(w, cfg.r.t)))

    def steps(self, cfg):
        """a step, then the blank written right of the head folded into 0"""
        out = [self.step(cfg)]
        c = out[-1][2]
        if c.kind == 'ls' and c.r == Push(0, ZERO):
            out.append(conv(c, ['r'], 'kzPush00', ZERO))
        return out


# ---------------------------------------------------------------- congruence
def sub(t, path):
    for p in path:
        t = getattr(t, p)
    return t


def cong(cfg, path, h):
    """a proof of cfg = cfg' from h: (subterm at path) = (new subterm)"""
    pf = h
    # walk the path from the inside out
    node = [cfg]
    for p in path[:-1]:
        node.append(getattr(node[-1], p))
    for parent, p in reversed(list(zip(node, path))):
        if isinstance(parent, Cfg):
            nm = {'st': 'kzState', 'ls': 'kzLS', 'pend': 'kzPend'}[parent.kind]
            pos = {('st', 'l'): 2, ('st', 'r'): 3, ('ls', 'l'): 2, ('ls', 'r'): 3,
                   ('pend', 'l'): 3, ('pend', 'r'): 4}[(parent.kind, p)]
            pf = f'({nm}eq{pos} {pf})'
        elif isinstance(parent, Push):
            pf = f'(kzPusheq2 {pf})'
        elif isinstance(parent, Rep):
            pf = f'(kzRepeq{3 if p == "t" else 2} {pf})'
        else:
            raise ValueError(parent)
    return pf


def replace(t, path, new):
    if not path:
        return new
    p = path[0]
    if isinstance(t, Cfg):
        c = Cfg(t.kind, t.q, t.l, t.r)
    elif isinstance(t, Push):
        c = Push(t.c, t.t)
    else:
        c = Rep(t.n, t.t)
    setattr(c, p, replace(getattr(t, p), path[1:], new))
    return c


def conv(cfg, path, h, new):
    """('E', proof of cfg = cfg', cfg')"""
    return ('E', cong(cfg, path, h), replace(cfg, path, new))


# ---------------------------------------------------------------- the register file
def file_term(S, vals):
    t = ZERO
    for v in reversed(vals):
        t = Push(S, Rep(v, t))
    return t


def file_defs(S, kmax=9):
    out = ['@_ local def kzF0: nat = $ 0 $;', "theorem kzF0_def: $ kzF0 = 0 $ = 'eqid;"]
    for k in range(1, kmax + 1):
        args = ' '.join(f'b{i}' for i in range(1, k + 1))
        body = file_term(S, [f'b{i}' for i in range(1, k + 1)])
        out.append(f'@_ local def kzF{k} ({args}: nat): nat = $ {body} $;')
        out.append(f'theorem kzF{k}_def ({args}: nat): $ kzF{k} {args} = {body} $ = \'eqid;')
    return out


class FileRef(T):
    """kzF<k> v1 .. vk (folded)"""
    def __init__(self, vals):
        self.vals = list(vals)

    def __str__(self):
        if not self.vals:
            return 'kzF0'
        return f'(kzF{len(self.vals)} {" ".join(self.vals)})'

    def __eq__(self, o):
        return isinstance(o, FileRef) and o.vals == self.vals


# ---------------------------------------------------------------- register macros
class Macros:
    """From the op transition (chain state on the first gap cell) to the op's cell:
      inc:      kzState cinc_j L (kzRep 1 g F)  ->P  kzLS scan L (kzRep 1 g F')
      dec, > 0: kzState cdec_j L (kzRep 1 g F)  ->P  kzLS scan L (kzRep 1 g F')   (v_j = suc b)
      dec, = 0: kzState cdec_j L (kzRep 1 g F)  ->P  kzLS retfail L (kzRep 1 g F) (v_j = 0)
    F has k registers; j = k + 1 creates register j (lazily)."""
    def __init__(self, M):
        self.M = M
        q = M.q
        self.scan, self.c1, self.cS = q('scan'), q('carry1'), q('carryS')
        self.ds, self.dp, self.dl, self.dst = q('dscan'), q('dput'), q('dlast'), q('dstart')
        self.rf = q('retfail')

    def name(self, op, j, k):
        return f'kzM{op}_{j}_{k}'

    def statement(self, op, j, k):
        M = self.M
        vals = [f'v{i}' for i in range(1, k + 1)]
        names = [v for i, v in enumerate(vals) if not (op == 'dec0' and i == j - 1)]
        start = vals[:]
        if op == 'decp' and j <= k:
            start[j - 1] = f'(suc v{j})'
        if op == 'dec0' and j <= k:
            start[j - 1] = '0'
            vals[j - 1] = '0'
        F0 = FileRef(start)
        if op == 'inc':
            end = vals + (['1'] if j == k + 1 else [])
            if j <= k:
                end[j - 1] = f'(suc v{j})'
            tq = self.scan
        elif op == 'decp':
            end, tq = vals, self.scan
        else:
            end = vals + (['0'] if j == k + 1 else [])
            tq = self.rf
        chain = M.q(f'c{"inc" if op == "inc" else "dec"}{j}')
        a = Cfg('st', chain, Leaf('L'), Rep('g', F0))
        b = Cfg('ls', tq, Leaf('L'), Rep('g', FileRef(end)))
        binders = ' '.join(['L', 'g'] + names)
        return a, b, f'({binders}: nat)'

    def proof(self, op, j, k):
        M, S = self.M, self.M.S
        a, b, _ = self.statement(op, j, k)
        segs = []
        vals = a.r.t.vals
        cfg = a
        # unfold the file
        seg = conv(cfg, ['r', 't'], f'kzF{k}_def', file_term(S, vals))
        segs.append(seg); cfg = seg[2]
        # the chain: cross the gap and the separators of registers 1 .. j - 1 (and register j's)
        kind = 'inc' if op == 'inc' else 'dec'
        first = self.c1 if op == 'inc' else self.dst
        nblocks = min(j, k)            # separators to cross before the register (or the end)
        cur = M.q(f'c{kind}{j}')
        for i in range(nblocks):
            # cfg.r = kzRep 1 n (kzPush S X)
            assert isinstance(cfg.r, Rep) and isinstance(cfg.r.t, Push) and cfg.r.t.c == S, cfg
            nxt = M.q(f'c{kind}{j - i - 1}') if j - i - 1 >= 1 else first
            h = f'(kzChain {M.hq(cur)} {M.hb(1)} {M.hb(S)} {M.A(cur, 1)} {M.A(cur, S)})'
            cfg = Cfg('st', nxt, Push(S, Rep(cfg.r.n, cfg.l)), cfg.r.t.t)
            segs.append(('P', h, cfg))
            cur = nxt
        if j == k + 1:
            # cross the 1s of the last register (or the gap), then create the register
            n = cfg.r.n
            assert isinstance(cfg.r, Rep) and cfg.r.t == ZERO, cfg
            segs.append(('R', f'(kzReach_I (kzLoopR {M.hq(cur)} {M.hb(1)} {M.A(cur, 1)}))',
                         Cfg('st', cur, Rep(n, cfg.l), ZERO)))
            cfg = segs[-1][2]
            seg = conv(cfg, ['r'], '(eqcom kzPush00)', Push(0, ZERO)); segs.append(seg); cfg = seg[2]
            seg = M.step(cfg); segs.append(seg); cfg = seg[2]      # writes S, now `first` on 0
            seg = conv(cfg, ['r'], '(eqcom kzPush00)', Push(0, ZERO)); segs.append(seg); cfg = seg[2]
            for seg in M.steps(cfg):                               # carry1 / dstart on 0: left
                segs.append(seg)
            cfg = segs[-1][2]
            # now an LS configuration: scan / retfail on the new separator
            return self.scan_back(segs, cfg, b)
        # cfg: `first` at the content of register j
        if op == 'inc':
            # carry1 L (kzRep 1 v X)  =  kzPend (kzPush 1 L) (kzRep 1 v X)
            seg = ('E', f'(eqcom (kzPend_push1 {M.hb(1)}))', Cfg('pend', (self.c1, self.cS), Push(1, cfg.l), cfg.r))
            segs.append(seg); cfg = seg[2]
            hyp = self.pend_hyps()
            n, X = cfg.r.n, cfg.r.t
            V = Rep(n, cfg.l)
            segs.append(('R', f'(kzReach_I (ax_mp (kzPend_loop {hyp["loop"]}) (ax_mp orl (kzPush_mod {M.hb(1)}))))',
                         Cfg('pend', cfg.q, V, X)))
            cfg = segs[-1][2]
            while cfg.r != ZERO:
                # cfg.r = kzPush S (kzRep 1 n X)
                assert isinstance(cfg.r, Push) and isinstance(cfg.r.t, Rep), cfg
                hv = self.hv(cfg.l)
                n, X = cfg.r.t.n, cfg.r.t.t
                segs.append(('R', f'(kzReach_I (ax_mp (kzPend_block {hyp["block"]}) {hv}))',
                             Cfg('pend', cfg.q, Rep(n, Push(S, cfg.l)), X)))
                cfg = segs[-1][2]
            hv = self.hv(cfg.l)
            segs.append(('SE', f'(ax_mp (kzPend_end {hyp["end"]}) {hv})', Cfg('ls', self.scan, cfg.l, ZERO)))
            cfg = segs[-1][2]
            return self.scan_back(segs, cfg, b)
        if op == 'decp':
            # dstart on kzRep 1 (suc v) X
            seg = conv(cfg, ['r'], 'kzRepS', Push(1, Rep(cfg.r.n[5:-1], cfg.r.t))); segs.append(seg); cfg = seg[2]
            seg = M.step(cfg); segs.append(seg); cfg = seg[2]        # dstart -> dscan
            n, X = cfg.r.n, cfg.r.t
            segs.append(('R', f'(kzReach_I (kzLoopR {M.hq(self.ds)} {M.hb(1)} {M.A(self.ds, 1)}))',
                         Cfg('st', self.ds, Rep(n, cfg.l), X)))
            cfg = segs[-1][2]
            # kzRep 1 n (kzPush 1 L) = kzPush 1 (kzRep 1 n L)
            seg = conv(cfg, ['l'], 'kzRep_push', Push(1, Rep(cfg.l.n, cfg.l.t.t))); segs.append(seg); cfg = seg[2]
            while cfg.r != ZERO:
                n, X = cfg.r.t.n, cfg.r.t.t
                h = (f'(kzDec_block {M.hq(self.ds)} {M.hq(self.dp)} {M.hb(1)} {M.hb(S)} '
                     f'{M.A(self.ds, 1)} {M.A(self.ds, S)} {M.A(self.dp, 1)})')
                cfg = Cfg('st', self.ds, Rep(f'(suc {n})', Push(S, cfg.l.t)), X)
                segs.append(('P', h, cfg))
                seg = conv(cfg, ['l'], 'kzRepS', Push(1, Rep(n, cfg.l.t))); segs.append(seg); cfg = seg[2]
            h = f'(kzDec_end {M.hq(self.ds)} {M.hq(self.dl)} {M.hb(0)} {M.hb(1)} {M.A(self.ds, 0)} {M.A(self.dl, 1)})'
            cfg = Cfg('ls', self.scan, cfg.l.t, ZERO)
            segs.append(('P', h, cfg))
            return self.scan_back(segs, cfg, b)
        # dec on an empty register: dstart reads S (or the blank) and runs left as retfail
        seg = conv(cfg, ['r'], 'kzRep0', cfg.r.t); segs.append(seg); cfg = seg[2]
        if cfg.r == ZERO:
            seg = conv(cfg, ['r'], '(eqcom kzPush00)', Push(0, ZERO)); segs.append(seg); cfg = seg[2]
        for seg in M.steps(cfg):
            segs.append(seg)
        cfg = segs[-1][2]
        return self.scan_back(segs, cfg, b)

    def pend_hyps(self):
        M, S = self.M, self.M.S
        c1, cS, sc = self.c1, self.cS, self.scan
        hc1, hcS, hsc = M.hq(c1), M.hq(cS), M.hq(sc)
        h0, h1, hS = M.hb(0), M.hb(1), M.hb(S)
        return {
            'loop': f'{hc1} {hcS} {h1} kzS_ne1 {M.A(c1, 1)} {M.A(cS, 1)}',
            'block': f'{hc1} {hcS} {h1} {hS} kzS_ne1 {M.A(c1, 1)} {M.A(c1, S)} {M.A(cS, 1)} {M.A(cS, S)}',
            'end': f'{hc1} {hcS} {hsc} {h0} {h1} {hS} kzS_ne1 {M.A(c1, 0)} {M.A(cS, 0)} {M.A(sc, 1)} {M.A(sc, S)}',
        }

    def hv(self, V):
        M, S = self.M, self.M.S
        if isinstance(V, Push):
            return f'(ax_mp {"orl" if V.c == 1 else "orr"} (kzPush_mod {M.hb(V.c)}))'
        assert isinstance(V, Rep) and isinstance(V.t, Push), V
        if V.t.c == 1:
            return f'(kzHv_1 {M.hb(1)})'
        return f'(kzHv_S {M.hb(1)} {M.hb(S)})'

    def scan_back(self, segs, cfg, target):
        """from an LS configuration run left (state cfg.q: scan or retfail) until the left tape is
        the target's; then convert to the target"""
        M = self.M
        q = cfg.q
        while cfg.l != target.l:
            V = cfg.l
            if isinstance(V, Rep):
                segs.append(('R', f'(kzReach_I (kzLoopLS {M.hq(q)} {M.hb(1)} {M.A(q, 1)}))',
                             Cfg('ls', q, V.t, Rep(V.n, cfg.r))))
            else:
                assert isinstance(V, Push), V
                segs.append(('S', f'(kzLS_step {M.hq(q)} {M.hb(V.c)} {M.A(q, V.c)})',
                             Cfg('ls', q, V.t, Push(V.c, cfg.r))))
            cfg = segs[-1][2]
        segs.append(('E', f'(eqcom {self.target_eq(cfg, target)})', target))
        return segs

    def target_eq(self, cur, target):
        """a proof of target = cur, where cur.r is the explicit file (with  kzPush 1 (kzRep 1 v X)
        for an incremented register and  kzPush S (kzPush 1 0)  for a created one)"""
        S = self.M.S
        vals = target.r.t.vals
        k = len(vals)
        pf = f'(kzLSeq3 (kzRepeq3 kzF{k}_def))'
        # register i's  kzRep 1 (suc v) X  ->  kzPush 1 (kzRep 1 v X)
        exp_target = file_term(S, vals)
        exp_cur = cur.r.t
        path = []
        t1, t2 = exp_target, exp_cur
        extra = []
        while isinstance(t1, Push):
            r1, r2 = t1.t, t2.t      # Rep n ...
            if r1 != r2 and isinstance(r1, Rep) and r1.n == '0' and r1.t == r2:
                extra.append((['r', 't'] + path + ['t'], 'kzRep0'))
                break
            if r1 != r2 and isinstance(r1, Rep) and isinstance(r2, Push):
                # r1 = kzRep 1 (suc v) Y  (or 1 0), r2 = kzPush 1 (kzRep 1 v Y) (or kzPush 1 0)
                p = ['r', 't'] + path + ['t']
                if r1.n == '1':
                    eqn = '(eqtr kzRepS (kzPusheq2 kzRep0))'
                else:
                    eqn = 'kzRepS'
                extra.append((p, eqn))
                break
            path += ['t', 't']
            t1, t2 = r1.t, (r2.t if isinstance(r2, Rep) else r2)
        for p, eqn in extra:
            tgt_cfg = Cfg('ls', target.q, target.l, Rep(target.r.n, exp_target))
            pf = f'(eqtr {pf} {cong(tgt_cfg, p, eqn)})'
        return pf

    def theorem(self, op, j, k):
        a, b, binders = self.statement(op, j, k)
        segs = self.proof(op, j, k)
        pf, kind = fold(segs)
        assert kind == 'P'
        return f"theorem {self.name(op, j, k)} {binders}:\n  $ kzReachP {a}\n    {b} $ =\n'{pf};"


def macro_file(D, ks=(9,)):
    M = Mach(D)
    MC = Macros(M)
    S = M.S
    out = ['import "kz_act.mm1";', '']
    out += file_defs(S)
    out.append(f"theorem kzS_ne1: $ {num(S)} != 1 $ = '(mpbir (noteq peano2) peano1);")
    out.append('')
    for k in ks:
        for j in range(1, min(k + 1, 9) + 1):
            for op in ('inc', 'decp', 'dec0'):
                if op == 'decp' and j > k:
                    continue
                out.append(MC.theorem(op, j, k))
    return out


if __name__ == '__main__':
    D = int(sys.argv[1])
    ks = [int(x) for x in sys.argv[2:]] or [9]
    open(os.path.join(HERE, 'kz_mac.mm1'), 'w').write('\n'.join(macro_file(D, ks)) + '\n')
    print('kz_mac.mm1 written')


# ---------------------------------------------------------------- one k215P step
J = Leaf('J')
BASE = Push(0, J)


def cells(digits, tail):
    t = tail
    for d in reversed(digits):
        t = Push(d + 1, t)
    return t


def strip(digits):
    d = list(digits)
    while d and d[-1] == 0:
        d.pop()
    return tuple(d)


class Sim:
    def __init__(self, D):
        self.M = M = Mach(D)
        self.MC = Macros(M)
        self.m = M.m
        self.root = M.q(self.m.root)
        self.inv = {tuple(t): pc for pc, t in self.m.pc_tape.items()}
        self.chains = {M.q(f'c{op}{j}'): (op, j) for op in ('inc', 'dec') for j in range(1, 10)}

    def conf(self, digits, vals):
        return Cfg('st', self.root, BASE, cells(digits, Rep(self.M.G - len(digits), FileRef(vals))))

    def decode(self, digits):
        """the k215P pc of a canonical tape, or None (a prologue / rewritten slot)"""
        import collections
        t = collections.defaultdict(int, {i: d + 1 for i, d in enumerate(digits)})
        for i in range(len(digits), self.M.G):
            t[i] = 1
        n = self.m.normalize(t)
        return self.inv.get(tuple(n)) if n is not None else None, n

    def leaf(self, digits):
        """the leaf slot the walk reaches"""
        import collections
        t = collections.defaultdict(int, {i: d + 1 for i, d in enumerate(digits)})
        for i in range(len(digits), self.M.G):
            t[i] = 1
        n, i = self.m.dag.root, 0
        while True:
            v = t[i] - 1
            vals, writes, _ = self.m.val[n]
            for jj, c in enumerate(self.m.slots[n]):
                if (isinstance(c, int) and v in (vals[jj], writes[jj])) or (not isinstance(c, int) and v == vals[jj]):
                    break
            c = self.m.slots[n][jj]
            if isinstance(c, int):
                n, i = c, i + 1
                continue
            return c

    def cstep(self, cfg, segs):
        """one concrete step (with the conversions it needs)"""
        M = self.M
        if cfg.kind == 'ls':
            if cfg.l == ZERO:
                segs.append(conv(cfg, ['l'], '(eqcom kzPush00)', Push(0, ZERO)))
                cfg = segs[-1][2]
            assert isinstance(cfg.l, Push), cfg
            c = cfg.l.c
            segs.append(('E', f'(kzLS_push {M.hb(c)})', Cfg('st', cfg.q, cfg.l.t, Push(c, cfg.r))))
            cfg = segs[-1][2]
        while not isinstance(cfg.r, Push):
            if isinstance(cfg.r, Rep):
                n = cfg.r.n
                assert isinstance(n, int), cfg
                if n == 0:
                    seg = conv(cfg, ['r'], 'kzRep0', cfg.r.t)
                else:
                    seg = conv(cfg, ['r'], 'kzRepS', Push(1, Rep(n - 1, cfg.r.t)))
            elif cfg.r == ZERO:
                seg = conv(cfg, ['r'], '(eqcom kzPush00)', Push(0, ZERO))
            else:
                raise AssertionError(('head cell not explicit', str(cfg)))
            segs.append(seg)
            cfg = seg[2]
        for seg in M.steps(cfg):
            segs.append(seg)
        return segs[-1][2]

    def canon(self, cfg, segs):
        """fold trailing fresh cells into the gap; returns (cfg, digits)"""
        path, t, digs = ['r'], cfg.r, []
        while isinstance(t, Push):
            digs.append(t.c - 1)
            path.append('t')
            t = t.t
        assert isinstance(t, Rep) and isinstance(t.n, int), cfg
        while digs and digs[-1] == 0:
            digs.pop()
            path.pop()
            sub_t = sub(cfg, path)
            seg = conv(cfg, path, '(eqcom kzRepS)', Rep(sub_t.t.n + 1, sub_t.t.t))
            segs.append(seg)
            cfg = seg[2]
        return cfg, tuple(digs)

    def run(self, digits, vals, branch, k, maxcycles=6):
        """symbolic execution from conf(digits, vals) for one k215P step.
        branch: 'inc', 'dec0', 'decp' (for the op of the leaf), 'ctl', 'halt'.
        Returns (segs, end cfg, end digits, end vals, end k, end pc)"""
        M, segs = self.M, []
        cfg = self.conf(digits, vals)
        first = True
        for cyc in range(maxcycles):
            lf = self.leaf(digits)
            pc, _ = self.decode(digits)
            if not first and pc is not None:
                return segs, cfg, digits, vals, k, pc
            br = branch if first else ('inc' if lf[0] == 'inc' else 'ctl')
            first = False
            # the walk and the leaf transition
            mark = len(segs)
            while True:
                if cfg.kind == 'st' and cfg.q in self.chains:
                    break
                if cfg.kind == 'st' and cfg.q == 'H':
                    return segs, cfg, None, vals, k, 'halt'
                if cfg.kind == 'st' and cfg.q == self.root and cfg.l == BASE and len(segs) > mark:
                    break
                cfg = self.cstep(cfg, segs)
            if cfg.q in self.chains:
                op, j = self.chains[cfg.q]
                assert isinstance(cfg.r, Rep) and isinstance(cfg.r.t, FileRef), cfg
                kind = br if br in ('inc', 'dec0', 'decp') else 'inc'
                if op == 'dec' and kind == 'inc':
                    raise AssertionError('dec op on an inc branch')
                assert (op == 'inc') == (kind == 'inc'), (op, kind)
                name = self.MC.name(kind, j, k)
                old = list(cfg.r.t.vals)
                new = old[:]
                if j <= k:
                    if kind == 'inc':
                        new[j - 1] = f'(suc {old[j - 1]})'
                    elif kind == 'decp':
                        assert old[j - 1].startswith('(suc ')
                        new[j - 1] = old[j - 1][5:-1]
                    else:
                        assert old[j - 1] == '0'
                else:
                    assert j == k + 1, (j, k)
                    new.append('1' if kind == 'inc' else '0')
                    k += 1
                tq = self.MC.scan if kind != 'dec0' else self.MC.rf
                cfg = Cfg('ls', tq, cfg.l, Rep(cfg.r.n, FileRef(new)))
                segs.append(('P', name, cfg))
                vals = new
                while not (cfg.kind == 'st' and cfg.q == self.root and cfg.l == BASE):
                    cfg = self.cstep(cfg, segs)
            cfg, digits = self.canon(cfg, segs)
        raise AssertionError('too many cycles')


def branches(e):
    return {0: ['inc'], 1: ['dec0', 'decp'], 2: ['ctl'], 3: ['ctl'], 4: ['halt']}[e['tag']]


def start_vals(S, e, br, k):
    vals = [f'v{i}' for i in range(1, k + 1)]
    names = list(vals)
    if br in ('dec0', 'decp'):
        j = S.m.reg_order.index(e['arg'])
        if j < k:
            if br == 'dec0':
                vals[j] = '0'
                names.remove(f'v{j + 1}')
            else:
                vals[j] = f'(suc v{j + 1})'
    return vals, names


def pc_theorem(S, name, pc, digits, br, k):
    from program import P
    e = P[pc]
    vals, names = start_vals(S, e, br, k)
    segs, cfg, d2, v2, k2, pc2 = S.run(digits, vals, br, k)
    a = S.conf(digits, vals)
    pf, kind = fold(segs)
    assert kind == 'P'
    binders = ' '.join(names + ['J'])
    thm = f"theorem {name} ({binders}: nat):\n  $ kzReachP {a}\n    {cfg} $ =\n'{pf};"
    return thm, (pc2, d2, v2, k2)
