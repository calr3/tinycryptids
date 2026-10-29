"""Run the real machine (tools/kevsim, C) from the blank tape and check its register operations
against the abstract interpreter (ksim, no accelerations): the same sequence of (register,
operation) for the first E operations, and the same register values decoded from the tape
afterwards (cf. ../pa/tm_events.py).  This checks what ksim does not run: the boot, dispatch,
the register file (including its lazy creation), the chains and the returns.

    python3 kevents.py D [E] [maxsteps]
"""
import os, sys, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'pa'))
sys.path.insert(0, HERE)
from ksim import KSim, CHAIN
from kary import FRESH

KEVSIM = os.path.join(HERE, 'tools', 'kevsim')


def real_events(c, maxsteps, maxevents):
    order, table, clean = c.named()
    inv = {v: k for k, v in clean.items()}
    idx = {n: i for i, n in enumerate(order)}
    nsym = c.D + 2
    lines = [f'{len(order)} {nsym} {maxsteps} {maxevents}']
    for n in order:
        for t in table[n]:
            lines.append('0 0 -2' if t is None else f'{t[0]} {1 if t[1] == "R" else 0} {idx.get(t[2], -1)}')
    lines += ['2' if inv[n].startswith('n.') else '1' if CHAIN.match(inv[n]) else '0' for n in order]
    out = subprocess.run([KEVSIM], input='\n'.join(lines) + '\n', capture_output=True, text=True).stdout.split('\n')
    ev = []
    for l in out:
        if l.startswith('E '):
            op, j = CHAIN.match(inv[order[int(l.split()[1])]]).groups()
            ev.append((c.reg_order[int(j) - 1], op))
    rest = [l for l in out if l and not l.startswith('E ')]
    status, steps, head = rest[0].split()
    tape = [int(ch, 36) for ch in rest[1]]
    return ev, status, int(steps), int(head), tape


def decode(c, tape, head):
    """Registers when a node has just entered a register chain: the gap of 1s, then the blocks
    SEP 1^v (registers not created yet are 0)."""
    SEP = c.SEP
    assert tape[head] in (FRESH, SEP)
    i = head
    while i < len(tape) and tape[i] == FRESH:
        i += 1
    vals, cur = [], None
    for x in tape[i:] + [0]:
        if x == SEP:
            if cur is not None:
                vals.append(cur)
            cur = 0
        elif x == FRESH and cur is not None:
            cur += 1
        else:
            assert x == 0, x
            if cur is not None:
                vals.append(cur)
            break
    vals += [0] * (len(c.reg_order) - len(vals))
    return dict(zip(c.reg_order, vals))


def check(c, nevents, maxsteps):
    ev, status, steps, head, tape = real_events(c, maxsteps, nevents)
    sim = KSim(c, accel=False, accel_sub=False)
    sim.trace = []
    while len(sim.trace) < len(ev) - 1:
        sim.step()
    got = [(r, op) for r, op, _ in sim.trace][:len(ev) - 1]
    assert got == ev[:len(got)], next(i for i in range(len(got)) if got[i] != ev[i])
    # the last event starts operation len(ev): the registers are those after len(ev) - 1
    regs = {r: 0 for r in c.reg_order}
    for r, op, ok in sim.trace[:len(ev) - 1]:
        regs[r] += 1 if op == 'inc' else (-1 if ok else 0)
    vals = decode(c, tape, head)
    assert vals == regs, (vals, regs)
    return len(ev), status, steps


if __name__ == '__main__':
    import kary, kbuild
    D = int(sys.argv[1])
    n = int(float(sys.argv[2])) if len(sys.argv) > 2 else 100000
    m = int(float(sys.argv[3])) if len(sys.argv) > 3 else int(2e10)
    c = kbuild.build(D)          # the machine of machines/pa_<D+2>sym_*.txt
    k, status, steps = check(c, n, m)
    print(f'D={D}: {c.count()} instructions; {k} register operations of the real machine '
          f'({steps} steps, stop: {status}) match ksim, and so do the registers on the tape')
