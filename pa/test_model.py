"""Compare a compiled machine (run by dagsim on its own DAG transitions) with the reference
model (ref.py), one main-loop iteration at a time.

  * the natural run from the blank start (all registers 0), for N iterations;
  * random single iterations: a random step (axiomcode, p1, p2, p3) encoded in prooflist, and
    random theorems on the stack (random wff-shaped codes), so every candidate, DET's and GEN's
    pops and B6a's side condition are exercised with large values.

    python3 test_model.py original [N] [R]     legion/pa.py's machine (baseline.build())
    python3 test_model.py improved [N] [R]     program.build()
    python3 test_model.py improved344 [N] [R]  program.build(stack_rev=False)
"""
import os, sys, random
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
sys.setrecursionlimit(100000)
from dagsim import DagSim, Halted, mpz
import ref

PERSIST = ('prooflist', 'nextproof', 'topwff', 'wffstack')


def setup(which):
    if which == 'original':
        import baseline
        return baseline.build(), lambda s: ref.iterate_original(s, ref.ORIGINAL_ORDER), {'scratch1', 'scratch2', 'scratch3'}
    import program
    b = program.build(**(dict(stack_rev=False, reload2=False, b6a2=False, shared_eq=False) if which == 'improved344' else {}))
    return b, lambda s: ref.iterate_tail(s, b.order, b.stack_rev, b.shared_eq, b.variants), {'scratch1', 'scratch2', 'param2'}


def one(b, model, zero_regs, st):
    """Run one iteration from model state st on both; return (halted, state)."""
    sim = DagSim(b.tm.states, list(b.registers))
    for r, v in zip(PERSIST, st.tuple()):
        sim.reg[r] = mpz(v)
    ms = ref.State(*st.tuple())
    mh = model(ms)
    try:
        sim.run_iterations(1, maxsteps=10**6)
        sh = False
    except Halted:
        sh = True
    assert sh == mh, ('halt', st.tuple(), sh, mh)
    if not sh:
        got = tuple(sim.reg[r] for r in PERSIST)
        assert got == ms.tuple(), ('state', st.tuple(), got, ms.tuple())
        for r in zero_regs:
            assert sim.reg[r] == 0, ('not cleared', r, sim.reg[r])
    return sh, ms


def rand_wff(rnd, depth):
    if depth == 0 or rnd.random() < 0.3:
        return rnd.randint(0, 4)
    k = rnd.randint(0, 4)
    if k == 3:
        return ref.neg(rand_wff(rnd, depth - 1))
    return ref.pair(ref.pair(rand_wff(rnd, depth - 1), rand_wff(rnd, depth - 1)), k)


def natural(b, model, zero_regs, n):
    sim = DagSim(b.tm.states, list(b.registers))
    ms = ref.State()
    for i in range(n):
        sim.run_iterations(1)
        assert not model(ms)
        got = tuple(sim.reg[r] for r in PERSIST)
        assert got == ms.tuple(), (i, got, ms.tuple())
        for r in zero_regs:
            assert sim.reg[r] == 0, (i, r)
    return sim


def randomized(b, model, zero_regs, n, seed=7, ncand=16):
    rev = getattr(b, 'stack_rev', False)
    rnd = random.Random(seed)
    for i in range(n):
        ac = rnd.randint(0, ncand + 2)
        ps = [rnd.choice([rnd.randint(0, 5), rand_wff(rnd, 3)]) for _ in range(3)]
        if rnd.random() < 0.3:          # B6a's side condition
            ps[2] = ps[rnd.randint(0, 1)]
        stack = 0
        thms = [rand_wff(rnd, 3) for _ in range(rnd.randint(0, 4))]
        if rnd.random() < 0.4 and len(thms) >= 3:
            # make DET applicable: a premise q and q -> p1 in the positions DET reads
            q = thms[1]
            thms[2] = ref.imp(q, ps[0])
            if rnd.random() < 0.5:
                thms[0], thms[1] = thms[1], ref.imp(thms[1], ps[0])
        for t in reversed(thms[1:]):
            stack = ref.join(t, stack, rev)
        top = thms[0] if thms else 0
        st = ref.State(ref.encode(ac, *ps, rest=rnd.randint(0, 3), rev=rev), rnd.randint(0, 5), top, stack)
        one(b, model, zero_regs, st)
    return n


if __name__ == '__main__':
    which = sys.argv[1]
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    r = int(sys.argv[3]) if len(sys.argv) > 3 else 300
    b, model, zero_regs = setup(which)
    print(which, b.state_count(), 'states')
    sim = natural(b, model, zero_regs, n)
    print(f'natural run: {n} iterations match the model (about 2^{sim.nops.bit_length()} register operations)')
    randomized(b, model, zero_regs, r)
    print(f'random steps: {r} iterations match the model')
