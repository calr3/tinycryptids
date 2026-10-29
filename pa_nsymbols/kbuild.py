"""Build the k-symbol PA machines (kary.py) and write machines/pa_<symbols>sym_<instructions>.txt.

    python3 kbuild.py [D ...]          (default: every D in configs.CONFIGS)
    python3 kbuild.py check [D ...]    rebuild and compare with the files in machines/

configs.CONFIGS[D] is the program found by search_k.py for D digits (order, variants, switches,
grammar_seed).  The boot is the smallest of BOOTS whose gap holds the program counter.
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'pa'))
sys.path.insert(0, HERE)
import ir, kary
from configs import CONFIGS

# boots in the standard format over 0, 1, 2 (X: exit into scan), found by tools/bootsearch.c:
# (instructions, ones left, table)
BOOTS = [(7, 12, '2LB------_1RC2RB1LB_2RA1LX1RB_'),
         (8, 39, '2LB1RA1LB_1RA0LC---_1RC0RA1LX_')]

HEADER = '''; Halts iff it finds a proof of v0 e. v0 (a contradiction) in the theory T of ../pa: Tarski's
; system S2 of first-order logic with = and e., plus Friedman's set existence scheme (T is
; equiconsistent with PA).  Built by pa_nsymbols/kbuild.py: the program of ../pa/program.py,
; compiled by kary.py with {D} program-counter digits; symbols 0 (blank), 1..{D} (digits; 1 is
; also the gap and a register's unit), {S} (register separator).
; {k} symbols, {n} states, {i} instructions (defined transitions, the halting one included).
; Program: {cfg}
'''


def build(D, cfg=None):
    cfg = dict(cfg if cfg is not None else CONFIGS.get(D, {}))
    seed = cfg.pop('grammar_seed', None)
    p = ir.prog(**cfg)
    c = kary.Compiler(D, ir=p, grammar_seed=seed)
    for n, g, table in BOOTS:
        if c.pc_depth <= g:
            c = kary.Compiler(D, ir=p, grammar_seed=seed, boot=table)
            break
    return c


def write(c, D):
    cfg = CONFIGS.get(D, {})
    path = os.path.join(HERE, 'machines', f'pa_{D + 2}sym_{c.count()}.txt')
    c.write_named(path, HEADER.format(D=D, S=c.SEP, k=D + 2, n=len(c.states()), i=c.count(),
                                      cfg=cfg or '../pa/program.py defaults'))
    return path


def check(D):
    """the file machines/pa_<D+2>sym_*.txt is what build(D) writes"""
    import glob, tempfile
    files = glob.glob(os.path.join(HERE, 'machines', f'pa_{D + 2}sym_*.txt'))
    assert len(files) == 1, files
    c = build(D)
    with tempfile.TemporaryDirectory() as d:
        path = c.write_named(os.path.join(d, 'm.txt'), '') or os.path.join(d, 'm.txt')
        body = lambda t: [l for l in t.splitlines() if not l.startswith(';')]
        assert body(open(path).read()) == body(open(files[0]).read()), files[0]
    return files[0], c.count()


if __name__ == '__main__':
    if sys.argv[1:2] == ['check']:
        for D in [int(a) for a in sys.argv[2:]] or sorted(CONFIGS):
            f, n = check(D)
            print(f'{os.path.relpath(f, HERE)}: rebuilt identically ({n} instructions)')
        sys.exit()
    Ds = [int(a) for a in sys.argv[1:]] or sorted(CONFIGS)
    os.makedirs(os.path.join(HERE, 'machines'), exist_ok=True)
    for D in Ds:
        c = build(D)
        path = write(c, D)
        print(f'{D + 2} symbols: {len(c.states())} states, {c.count()} instructions '
              f'(boot {c.breakdown().get("boot")}, PC depth {c.pc_depth}) -> {os.path.relpath(path, HERE)}')
