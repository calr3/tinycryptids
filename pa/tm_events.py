"""Run the real Turing machine (tools/evsim, C) and check its register operations against the
abstract interpreter (dagsim, no accelerations): the same sequence of (register, operation) for
the first E operations, and the same register values decoded from the tape afterwards.  This
checks what dagsim does not run: the boot, dispatch, the register file and the returns.

    python3 tm_events.py original|improved [E] [maxsteps]
"""
import os, sys, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
sys.setrecursionlimit(100000)
from dagsim import DagSim, LEAF

EVSIM = os.path.join(HERE, 'tools', 'evsim')


def real_events(b, maxsteps, maxevents):
    st = b.tm.states
    names = sorted({s for s, _ in st})
    names.remove(b.tm.start)
    names = [b.tm.start] + names
    idx = {n: i for i, n in enumerate(names)}
    lines = [f'{len(names)} {maxsteps} {maxevents}']
    for n in names:
        for r in '01':
            t = st.get((n, r))
            if t is None:
                lines.append('0 0 -2')
            else:
                lines.append(f'{t.write} {1 if t.direction == "R" else 0} {idx.get(t.nextstate, -1)}')
    lines += ['1' if LEAF.match(n) else '2' if n == 'main().0' else '0' for n in names]
    out = subprocess.run([EVSIM], input='\n'.join(lines) + '\n', capture_output=True, text=True).stdout.split('\n')
    ev = [LEAF.match(names[int(l.split()[1])]).groups() for l in out if l.startswith('E ')]
    status, steps, head = [l for l in out if l and not l.startswith('E ')][0].split()
    tape = [l for l in out if l and not l.startswith('E ')][1]
    return ev, status, int(steps), int(head), tape


def decode(tape, head, nregs):
    """Registers at the start of a phase-2 operation: marker, 0, the -1 register, then blocks."""
    assert tape[head] == '1' and tape[head + 1] == '0'
    rest = tape[head + 2:]
    blocks = rest.split('0')
    # blocks[0] is the -1 register; register i is blocks[1 + i] = 1^(value + 1)
    return [len(blocks[1 + i]) - 1 for i in range(nregs)]


def check(b, nevents, maxsteps):
    ev, status, steps, head, tape = real_events(b, maxsteps, nevents)
    regs = list(b.registers)
    sim = DagSim(b.tm.states, regs, accel=False, accel_sub=False)
    while len(sim.ops) < len(ev) - 1:
        sim.step()
    got = [(r, op) for r, op, _ in sim.ops]
    assert got == ev[:len(got)], next(i for i in range(len(got)) if got[i] != ev[i])
    # the last event is the start of operation len(ev): registers are those after len(ev)-1 ops
    vals = decode(tape, head, len(regs))
    assert vals == [sim.reg[r] for r in regs], (vals, sim.reg)
    return len(ev), status, steps


if __name__ == '__main__':
    which = sys.argv[1]
    n = int(float(sys.argv[2])) if len(sys.argv) > 2 else 100000
    m = int(float(sys.argv[3])) if len(sys.argv) > 3 else int(2e10)
    if which == 'original':
        import baseline; b = baseline.build()
    else:
        import program; b = program.build()
    k, status, steps = check(b, n, m)
    print(f'{which}: {b.state_count()} states; {k} register operations of the real machine '
          f'({steps} steps, stop: {status}) match dagsim, and so do the registers on the tape')
