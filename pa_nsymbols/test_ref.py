"""Compare a compiled k-symbol machine (run by ksim on its own PC transitions) with the
reference model ../pa/ref.py, one main-loop iteration at a time (cf. ../pa/test_model.py):
the natural run from the start, and random single iterations.

    python3 test_ref.py D [N] [R]
"""
import os, sys, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'pa'))
sys.path.insert(0, HERE)
sys.setrecursionlimit(100000)
import ref
from ksim import KSim, Halted, mpz

PERSIST = ('prooflist', 'nextproof', 'topwff', 'wffstack')
ZERO = ('scratch1', 'scratch2', 'param2')


def rand_wff(rnd, depth):
    if depth == 0 or rnd.random() < 0.3:
        return rnd.randint(0, 4)
    k = rnd.randint(0, 4)
    if k == 3:
        return ref.neg(rand_wff(rnd, depth - 1))
    return ref.pair(ref.pair(rand_wff(rnd, depth - 1), rand_wff(rnd, depth - 1)), k)


def model_of(c):
    b = c.ir.b
    return lambda s: ref.iterate_tail(s, b.order, b.stack_rev, b.shared_eq, b.variants)


def one(c, model, st):
    sim = KSim(c)
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
        for r in ZERO:
            assert sim.reg[r] == 0, ('not cleared', r, sim.reg[r])
    return sh


def natural(c, model, n):
    sim = KSim(c)
    ms = ref.State()
    for i in range(n):
        sim.run_iterations(1)
        assert not model(ms)
        got = tuple(sim.reg[r] for r in PERSIST)
        assert got == ms.tuple(), (i, got, ms.tuple())
        for r in ZERO:
            assert sim.reg[r] == 0, (i, r)
    return sim


def randomized(c, model, n, seed=7, ncand=14):
    rnd = random.Random(seed)
    halts = 0
    for i in range(n):
        ac = rnd.randint(0, ncand + 2)
        ps = [rnd.choice([rnd.randint(0, 5), rand_wff(rnd, 3)]) for _ in range(3)]
        if rnd.random() < 0.3:
            ps[2] = ps[rnd.randint(0, 1)]
        stack = 0
        thms = [rand_wff(rnd, 3) for _ in range(rnd.randint(0, 4))]
        if rnd.random() < 0.4 and len(thms) >= 3:
            q = thms[1]
            thms[2] = ref.imp(q, ps[0])
            if rnd.random() < 0.5:
                thms[0], thms[1] = thms[1], ref.imp(thms[1], ps[0])
        if rnd.random() < 0.1 and len(thms) >= 2:
            # DET (the last candidate) kept, on q (the theorem pushed this step, popped by GEN)
            # and q -> (v0 e. v0) below it: modus ponens derives v0 e. v0, so the step halts
            ps[0] = 1
            thms[1] = ref.imp(thms[0], 1)
            ac = rnd.randint(ncand, ncand + 3)
        for t in reversed(thms[1:]):
            stack = ref.join(t, stack, True)
        top = thms[0] if thms else 0
        st = ref.State(ref.encode(ac, *ps, rest=rnd.randint(0, 3), rev=True), rnd.randint(0, 5), top, stack)
        halts += one(c, model, st)
    return halts


if __name__ == '__main__':
    import kary, kbuild
    D = int(sys.argv[1])
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    r = int(sys.argv[3]) if len(sys.argv) > 3 else 200
    c = kbuild.build(D)          # the machine of machines/pa_<D+2>sym_*.txt
    model = model_of(c)
    print(f'D={D}: {c.count()} instructions')
    sim = natural(c, model, n)
    print(f'natural run: {n} iterations match the model (about 2^{sim.nops.bit_length()} register operations)')
    h = randomized(c, model, r)
    print(f'random steps: {r} iterations match the model ({h} halted)')
