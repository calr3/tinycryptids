"""The register framework of a compiled machine on the real machine (../tools/sim): from a node's
transition into a chain state (cell 0 holds what the node wrote, then the gap and the register
file), every operation on every register, on random register files, including a register's
first operation (the file then ends just before it: it is created).  The run stops when it
leaves the framework (scan or adv, made undefined here); the registers decoded from the tape and
the node's cell must be what the operation and the return prescribe.

    python3 test_regs.py D [trials]
"""
import os, sys, random, importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'pa'))
sys.path.insert(0, HERE)
import kary, kbuild
# ../tools/tm.py (the name tm is legion's TMBuilder module)
_spec = importlib.util.spec_from_file_location('tmtools', os.path.join(HERE, '..', 'tools', 'tm.py'))
tmtools = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(tmtools)
from kary import FRESH


def decode(c, tape, start):
    """registers from cell `start` (the gap, then blocks SEP 1^v)"""
    i = start
    while i < len(tape) and tape[i] == FRESH:
        i += 1
    vals = []
    while i < len(tape) and tape[i] == c.SEP:
        i += 1
        v = 0
        while i < len(tape) and tape[i] == FRESH:
            v += 1
            i += 1
        vals.append(v)
    assert all(x == 0 for x in tape[i:]), tape[i:]
    return vals


def check(c, trials=40, seed=1):
    order, table, clean = c.named()
    for q in ('scan', 'adv'):
        table[clean[q]] = [None] * len(table[clean[q]])
    rnd = random.Random(seed)
    T, R = c.T, len(c.reg_order)
    n = 0
    ws = {op: sorted({w for i, sl in c.nodes.items() for x, w in zip(sl, c.val[i][1])
                      if kary.is_op(x) and x.endswith('.' + ('inc' if op == 'inc' else 'decnz'))})
          for op in ('inc', 'dec')}
    for r in range(R):
        for op in ('inc', 'dec'):
            for t in range(trials):
                have = R if t % 4 else r          # every fourth trial: r is created by this op
                vals = [rnd.choice([0, 0, 1, 2, rnd.randint(0, 9)]) for _ in range(have)]
                w = rnd.choice(ws[op])      # what the node wrote: a value ops of this kind write
                gap = rnd.randint(1, 4)
                tape = [w + 1] + [FRESH] * gap + [x for v in vals for x in [c.SEP] + [FRESH] * v]
                st, steps, q, h, out = tmtools.run(order, table, start=clean[f'c{op}{r + 1}'],
                                                   tape=''.join(chr(48 + x) for x in tape), head=1,
                                                   maxsteps=10**6)
                assert st == 'undefined', (st, r, op)
                out = [ord(ch) - 48 for ch in out]
                # the trimmed tape starts at the blank left of cell 0 (the head is there)
                assert h == 0 and out[0] == 0, (h, out[:3], q, w, r, op)
                new = vals + [0] * (r + 1 - len(vals))
                ok = True
                if op == 'inc':
                    new[r] += 1
                elif new[r]:
                    new[r] -= 1
                else:
                    ok = False
                got = decode(c, out, 2)
                assert got == new, (r, op, vals, got, new)
                if ok:
                    want = (FRESH, 'adv') if w == T else (w + 2, 'scan')
                else:
                    want = (FRESH, 'adv')
                assert (out[1], q) == (want[0], clean[want[1]]), (r, op, w, out[1], q, want)
                n += 1
    return n


if __name__ == '__main__':
    D = int(sys.argv[1])
    c = kbuild.build(D)          # the machine of machines/pa_<D+2>sym_*.txt
    print(f'D={D}: {check(c, int(sys.argv[2]) if len(sys.argv) > 2 else 40)} register operations '
          f'on the real machine are right (registers, the node cell, the state it leaves in)')
