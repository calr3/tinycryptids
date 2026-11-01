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


def boot_table(text):
    rows = text.strip('_').split('_')
    table = {}
    for i, row in enumerate(rows):
        for r in range(len(row) // 3):
            t = row[3 * r:3 * r + 3]
            if t != '---':
                table[(f'b{chr(65 + i)}', r)] = (int(t[0]), t[1], 'scan' if t[2] == 'X' else f'b{t[2]}')
    return table, 39, 'bA'


def machine(D):
    cfg = json.load(open(os.path.join(HERE, 'configs', f'{D}.json')))
    compiler.CARRY = {1, D - 1}
    compiler._amemo.clear()
    return Machine(DAG(prologue=4), D, set(cfg['M']), None, boot_table(BOOT))


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
    nsym = m.D + 2
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
        for r in range(m.D + 2):
            t = m.tm.get((q, r))
            cells.append('---' if t is None else f'{t[0]}{t[1]}{"Z" if t[2] == "halt" else idx[t[2]]}')
        rows.append(','.join(cells))
    return '; '.join(rows)


def write(D):
    m = machine(D)
    lines, qs = named(m)
    n, i = len(qs), m.count()
    head = HEADER.format(D=D, T=D - 1, S=D + 1, K=D + 2, N=n, I=i)
    path = os.path.join(HERE, 'machines', f'zfc_{D + 2}sym_{i}.txt')
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
            print(f'{D + 2} symbols: {len({q for q, _ in m.tm})} states, {m.count()} instructions -> {path}')
