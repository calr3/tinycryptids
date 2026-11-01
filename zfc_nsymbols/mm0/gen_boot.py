"""kz_boot.mm1: the boot, from the blank tape to the first entry of the root node, step by step
(lemmas of `chunk` steps chained).  usage: gen_boot.py D"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gen_sim import Sim, Cfg, ZERO, Push, Rep, FileRef, conv, fold, sub


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
    t, path = cfg.r, ['r']
    while isinstance(t, Push):
        path.append('t')
        t = t.t
    assert t == ZERO
    segs.append(conv(cfg, path, '(eqcom kzF0_def)', FileRef([]))); cfg = segs[-1][2]
    segs.append(conv(cfg, path, '(eqcom kzRep0)', Rep(0, FileRef([])))); cfg = segs[-1][2]
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
