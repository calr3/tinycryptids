"""Check dagsim's accelerations against plain execution, routine by routine.

For every subroutine node of the decision DAG (a state named `name(args).0`), set the program
counter to a path that reaches it, put small random values in the registers, run the node to
completion once without and once with the accelerations, and compare the registers.  Nodes whose
plain run takes too long on the drawn values are skipped for that draw.

    python3 check_accel.py MODULE [VARIANT]     (MODULE.build(VARIANT) returns a built builder)
"""
import os, sys, random, re, importlib
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
sys.setrecursionlimit(100000)
from dagsim import DagSim, Halted

ROOT_PREFIX = [1, 1, 0]          # 5.root.1 reads a 1, 5.root.2 a 0, then main().0


def dag_paths(states):
    """Shortest DAG path (bits after ROOT_PREFIX) to every decision-DAG state."""
    paths = {'main().0': ()}
    todo = ['main().0']
    while todo:
        q = todo.pop(0)
        for b in '01':
            t = states.get((q, b))
            if t is None:
                continue
            n = t.nextstate
            if t.direction == 'R' and not n[0].isdigit() and n != 'halt' and n not in paths:
                paths[n] = paths[q] + (int(b),)
                todo.append(n)
    return paths


def ambiguous(states, path):
    """True if a pair/unpair node lies on the path with only 0 bits after it: starting there
    is (correctly) a fresh entry into that subroutine, so the node itself would not be tested."""
    from dagsim import PAIR, UNPAIR
    q = 'main().0'
    for i, bit in enumerate(path):
        if (PAIR.match(q) or UNPAIR.match(q)) and not any(path[i:]):
            return True
        q = states[(q, str(bit))].nextstate
    return False


def run_node(b, path, init, accel, budget):
    s = DagSim(b.tm.states, list(b.registers), accel=accel, accel_sub=accel, strict=False)
    s.reg.update(init)
    s.pc = ROOT_PREFIX + list(path)
    while s.pc and s.pc[-1] == 0:
        s.pc.pop()
    prefix = ROOT_PREFIX + list(path)
    n = 0
    while True:
        s.step()
        n += 1
        pc = s.pc + [0] * (len(prefix) - len(s.pc))
        if pc[:len(prefix)] != prefix:
            return dict(s.reg), tuple(s.pc)
        if n > budget:
            return None


def check(b, draws=40, seed=1, maxval=4, budget=20000, verbose=False):
    rnd = random.Random(seed)
    paths = dag_paths(b.tm.states)
    subs = sorted(n for n in paths if re.match(r'^\w+\(.*\)\.0$', n))
    regs = list(b.registers)
    tested = {}
    for name in subs:
        if ambiguous(b.tm.states, paths[name]):
            continue
        for _ in range(draws):
            init = {r: rnd.randint(0, maxval) for r in regs}
            # scratch registers are zero at every call site
            for r in regs:
                if r.startswith('scratch'):
                    init[r] = 0
            try:
                plain = run_node(b, paths[name], init, False, budget)
            except Halted:
                continue
            if plain is None:
                continue
            fast = run_node(b, paths[name], init, True, budget)
            assert plain == fast, (name, init, plain, fast)
            tested[name] = tested.get(name, 0) + 1
    if verbose:
        for n in subs:
            print(f'  {tested.get(n, 0):3d}  {n}')
    return tested, subs


if __name__ == '__main__':
    mod = importlib.import_module(sys.argv[1])
    b = mod.build(*sys.argv[2:])
    tested, subs = check(b, verbose=True)
    print(f'{len(tested)} of {len(subs)} subroutine nodes checked, {sum(tested.values())} runs: plain == accelerated')
