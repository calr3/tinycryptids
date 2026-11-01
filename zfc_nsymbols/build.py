"""Build the machines: configs/<D>.json (a merge set found by search.py) -> machines/.

usage: python3 build.py [D ...]        (default: every config)
       python3 build.py check [D ...]  (also check the written files are what the compiler builds)
"""
import os, sys, json, glob, re
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import compiler
from compiler import DAG, Machine

# a 3-state boot (pa_nsymbols/tools/bootsearch.c): 8 instructions leave 0 1^39 (the gap), then
# `scan`.  Its symbol 2 is the digit 1.
BOOT = '2LB1RA1LB_1RA0LC---_1RC0RA1LX_'


def boot_table(text, exit='scan', G=39, sym2=2):
    """a boot in the standard text; X is the exit (into `exit`); the boot's symbol 2 is the
    machine's symbol sym2 (the separator when the boot also writes register 1)"""
    rows = text.strip('_').split('_')
    table = {}
    mp = lambda b: sym2 if b == 2 else b
    for i, row in enumerate(rows):
        for r in range(len(row) // 3):
            t = row[3 * r:3 * r + 3]
            if t != '---':
                table[(f'b{chr(65 + i)}', mp(r))] = (mp(int(t[0])), t[1], exit if t[2] == 'X' else f'b{t[2]}')
    return table, G, 'bA'


FLAGS = ('DECJUMP', 'UNICTL', 'VIRT', 'NOADV0', 'NATIVEDEC')


def machine(D):
    """configs/<D>.json: the merge set M, the carry set (default {1, T}) and compiler options
    (flags: DECJUMP, UNICTL, VIRT, NOADV0, NATIVEDEC; CARRYTO: reserved inside values)"""
    cfg = json.load(open(os.path.join(HERE, 'configs', f'{D}.json')))
    compiler.CARRY = set(cfg.get('carry', [1, D - 1]))
    flags = cfg.get('flags', {})
    for f in FLAGS:
        setattr(compiler, f, bool(flags.get(f, False)))
    compiler.CARRYTO = {int(k): v for k, v in cfg.get('carryto', {}).items()}
    compiler.SPECIAL = {int(k): v for k, v in cfg.get('special', {}).items()}
    compiler.SEPVAL = cfg.get('sepval')
    compiler.XMARK = tuple(cfg.get('xmark', ()))
    compiler.ALTS, compiler.ALTRETRY = cfg.get('alts', 0), cfg.get('altretry', 0)
    compiler.ALT0 = {int(k): v for k, v in cfg.get('alt0', {}).items()}
    compiler._amemo.clear()
    # BOOTINC: the boot exits into register 1's inc chain; a boot that also writes register 1
    # (cfg['boot'] = {table, G, r0}: it leaves 0 1^G S 1^r0) leaves r0 + 1 after that inc
    binc = bool(flags.get('BOOTINC', False))
    b = cfg.get('boot')
    sep = compiler.SEPVAL + 1 if compiler.SEPVAL is not None else D + 1
    compiler.PRESEP = 0
    if b:
        assert binc
        r0 = b['r0'] + 1
        if 'raw' in b:
            # a boot given as transitions (q, read, write, dir, next); symbol 2 is the separator
            mp = lambda x: sep if x == 2 else x
            boot = ({(q, mp(r)): (mp(w), d, n) for q, r, w, d, n in b['raw']}, b['G'], b['raw'][0][0])
        else:
            boot = boot_table(b['table'], 'cinc1', b['G'], sep)
        # presep: the boot also writes the other 8 separators and `presep` dummy ones after them
        compiler.PRESEP = b.get('presep', 0)
    else:
        r0 = 1 if binc else 0
        boot = boot_table(BOOT, 'cinc1' if binc else 'scan')
    dag = DAG(prologue=4 - r0, native_decx=compiler.NATIVEDEC)
    m = Machine(dag, D, set(cfg['M']), None, boot)
    m.boot_r0 = r0
    return m


HEADER = '''; Halts iff ZFC is inconsistent: simulates E. Glazer's register program k215P (the program of
; the 2-symbol machine K215, github.com/elliotglazer/k215-pa, which halts iff ZFC is inconsistent:
; MM0 theorem K215_halts_iff_ZFC_inconsistent), step for step, after a 4-instruction prologue
; that sets r0 = 4 (k215P's initial state).  Built by zfc_nsymbols/build.py (compiler.py).
; Symbols: 0 blank, 1..{D} program-counter digits 0..{T} (1 is also the gap and a register's unit),
; {S} register separator.
; {K} symbols, {N} states, {I} instructions (defined transitions, the halting one included).
'''


def named(m):
    qs = sorted({q for q, _ in m.tm})
    qs.remove(m.start)
    qs = [m.start] + qs
    clean = {q: re.sub(r'[^A-Za-z0-9_]', '_', q) for q in qs}
    nsym = m.K
    out = ['blank_symbol: 0']
    for q in qs:
        out.append(clean[q])
        for r in range(nsym):
            t = m.tm.get((q, r))
            out.append('  -' if t is None else f'  {r} {t[0]} {t[1]} {clean.get(t[2], "halt")}')
    return out, qs


def standard(m, qs):
    """bbchallenge-style: rows of <write><dir><state letter(s)>, '---' undefined, 'Z' halt"""
    idx = {q: i for i, q in enumerate(qs)}
    rows = []
    for q in qs:
        cells = []
        for r in range(m.K):
            t = m.tm.get((q, r))
            cells.append('---' if t is None else f'{t[0]}{t[1]}{"Z" if t[2] == "halt" else idx[t[2]]}')
        rows.append(','.join(cells))
    return '; '.join(rows)


def write(D):
    m = machine(D)
    lines, qs = named(m)
    n, i = len(qs), m.count()
    head = HEADER.format(D=D, T=D - 1, S=m.SEP, K=m.K, N=n, I=i)
    path = os.path.join(HERE, 'machines', f'zfc_{m.K}sym_{i}.txt')
    text = head + '\n'.join(lines) + '\n'
    return m, path, text


if __name__ == '__main__':
    args = sys.argv[1:]
    check = bool(args) and args[0] == 'check'
    if check:
        args = args[1:]
    Ds = [int(a) for a in args] or sorted(int(os.path.basename(f)[:-5]) for f in glob.glob(os.path.join(HERE, 'configs', '*.json')))
    for D in Ds:
        m, path, text = write(D)
        if check:
            ok = os.path.exists(path) and open(path).read() == text
            print(path, 'OK' if ok else 'DIFFERS')
        else:
            open(path, 'w').write(text)
            print(f'{m.K} symbols: {len({q for q, _ in m.tm})} states, {m.count()} instructions -> {path}')
