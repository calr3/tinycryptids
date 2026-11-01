"""kz_boot.mm1: the boot, from the blank tape to the first entry of the root node, step by step
(lemmas of `chunk` steps chained).  usage: gen_boot.py D"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gen_sim import Sim, Cfg, ZERO, Push, Rep, FileRef, conv, fold, sub, cells


def main(D, chunk=200):
    S = Sim(D)
    cfg = Cfg('st', 0, ZERO, ZERO)
    out = ['import "kz_mac.mm1";', '']
    parts, segs, start, n = [], [], cfg, 0
    while not (cfg.kind == 'st' and cfg.q == S.root):
        cfg = S.cstep(cfg, segs)
        n += 1
        if n % chunk == 0:
            parts.append((start, cfg, segs))
            start, segs = cfg, []
    # the root's configuration: kzState root (kzPush 0 0) (kzRep 1 39 kzF0)
    # (or, when the boot exits into register 1's inc chain, kzRep 1 39 (kzF1 1))
    t, path = cfg.r, ['r']
    while isinstance(t, Push) and t.c == 1:
        path.append('t')
        t = t.t
    if t == ZERO:
        segs.append(conv(cfg, path, '(eqcom kzF0_def)', FileRef([]))); cfg = segs[-1][2]
    else:
        # the register file the boot (and r0's inc) wrote: S 1^v1 S 1^v2 ... 0, folded block by
        # block (innermost first) into kzPush S (kzRep 1 v X), then into kzF<k> v1 .. vk
        S_ = S.M.S
        blocks, u, p = [], t, list(path)
        while u != ZERO:
            assert isinstance(u, Push) and u.c == S_, u
            v, w, q = 0, u.t, p + ['t']
            while isinstance(w, Push) and w.c == 1:
                v += 1
                w = w.t
            blocks.append((p, v))
            u = w
            p = q + ['t'] * v
        for p, v in reversed(blocks):
            q = p + ['t']
            segs.append(conv(cfg, q + ['t'] * v, '(eqcom kzRep0)', Rep(0, sub(cfg, q + ['t'] * v)))); cfg = segs[-1][2]
            for i in range(v, 0, -1):
                inner = sub(cfg, q + ['t'] * i)
                segs.append(conv(cfg, q + ['t'] * (i - 1), '(eqcom kzRepS)', Rep(v - i + 1, inner.t))); cfg = segs[-1][2]
        vals = [str(v) for _, v in blocks]
        segs.append(conv(cfg, path, f'(eqcom kzF{len(vals)}_def)', FileRef(vals))); cfg = segs[-1][2]
    segs.append(conv(cfg, path, '(eqcom kzRep0)', Rep(0, sub(cfg, path)))); cfg = segs[-1][2]
    if cfg.l == ZERO:
        segs.append(conv(cfg, ['l'], '(eqcom kzPush00)', Push(0, ZERO))); cfg = segs[-1][2]
    assert cfg.l == Push(0, ZERO), cfg.l
    cfg, digits = S.canon(cfg, segs)
    assert digits == () and cfg.r.n == S.M.G, (digits, cfg.r.n)
    parts.append((start, cfg, segs))
    names = []
    for i, (a, b, sg) in enumerate(parts):
        pf, kind = fold(sg)
        nm = f'kzBoot{i}'
        names.append((nm, kind))
        out.append(f"theorem {nm}: $ {'kzReachP' if kind == 'P' else 'kzReach'} {a}\n    {b} $ =\n'{pf};")
    # chain
    acc_kind = None
    acc = None
    for nm, kind in reversed(names):
        if acc is None:
            acc, acc_kind = nm, kind
        else:
            acc = f'(kzRP_RP {nm} {acc})'
    out.append(f"theorem kzBoot: $ kzReachP (kzState 0 0 0)\n    {cfg} $ =\n'{acc};")
    open(os.path.join(HERE, 'kz_boot.mm1'), 'w').write('\n'.join(out) + '\n')
    print(n, 'steps,', len(parts), 'parts', file=sys.stderr)


if __name__ == '__main__':
    main(int(sys.argv[1]))
