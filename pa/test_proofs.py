"""End-to-end proofs on the compiled machine (dagsim runs its own DAG transitions).

  1. A three-step derivation fed in as one proof code from the blank start: a B3 instance
     A -> (-. A -> x), then A = B2(v0 = v0), then modus ponens (DET; GEN pops the minor premise
     A first, DET the major one): the kept theorems are checked.
  2. Generalisation (GEN) of A over v9.
  3. Halting: modus ponens with major premise q -> (v0 e. v0) keeps v0 e. v0, and the machine halts.

    python3 test_proofs.py
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
sys.setrecursionlimit(100000)
from dagsim import DagSim, Halted, mpz
import ref, program

b = b_ = program.build()
assert b.stack_rev and b.cascade and b.shared_eq
CAND = list(b.order) + ['B6a', 'GEN', 'DET']
code = {name: i + 1 for i, name in enumerate(CAND)}     # axiomcode of each candidate
regs = list(b.registers)


def params(name, a, b, c):
    """(p1, p2, p3) that give the formal parameters (a, b, c) to candidate `name`."""
    perm = b_.variants.get(name, ((1, 2, 3), 0))[0] if name in ref.FORMS else (1, 2, 3)
    ps = [0, 0, 0]
    for formal, k in zip((a, b, c), perm):
        ps[k - 1] = formal
    return ps


def run_steps(steps, check):
    """steps: [(candidate, a, b, c)], run from the blank start through one proof code."""
    pl = 0
    for name, fa, fb, fc in reversed(steps):
        pl = ref.encode(code[name], *params(name, fa, fb, fc), rest=pl, rev=True)
    sim = DagSim(b.tm.states, regs)
    sim.reg['nextproof'] = mpz(0)
    sim.reg['prooflist'] = mpz(pl)
    s = ref.State(pl, 0, 0, 0)
    for i in range(len(steps)):
        sim.run_iterations(1)
        assert not ref.iterate_tail(s, b.order, True, True, b.variants)
        assert sim.reg['topwff'] == s.topwff and sim.reg['wffstack'] == s.wffstack
        check(i, int(sim.reg['topwff']))
    return sim


# 1. A -> (-. A -> x), A, hence -. A -> x   (B2, B3 are only ever relabelled)
A = ref.AXIOMS['B2'](0, 0, 0)             # (-. v0=v0 -> v0=v0) -> v0=v0
x = ref.eq(5, 7)                          # any wff
M = ref.AXIOMS['B3'](A, x, 0)             # A -> (-. A -> x)
assert all(f == 0 for _, f in [b.variants.get(n, ((1, 2, 3), 0)) for n in ('B2', 'B3')])
target = ref.imp(ref.neg(A), x)
want = [M, A, target]
run_steps([('B3', A, x, 0), ('B2', 0, 0, 0), ('DET', target, 0, 0)],
          lambda i, t: (t == want[i]) or sys.exit(f'step {i}: got {t}, want {want[i]}'))
print('modus ponens: B3, B2, MP gives -. A -> x as the machine\'s theorem')

# 2. generalisation: A, then GEN with p1 = v9
want = [A, ref.all_(9, A)]
run_steps([('B2', 0, 0, 0), ('GEN', 9, 0, 0)],
          lambda i, t: (t == want[i]) or sys.exit(f'step {i}: got {t}, want {want[i]}'))
print('generalisation: A. v9 A')

# 3. halting: theorems q (top) and q -> v0 e. v0 (below), DET with p1 = 1
q = A
st = ref.State(ref.encode(code['DET'], ref.FALSUM, 0, 0, rev=True), 0, q,
               ref.join(ref.imp(q, ref.FALSUM), 0, True))
assert ref.iterate_tail(ref.State(*st.tuple()), b.order, True, True, b.variants)
sim = DagSim(b.tm.states, regs)
for r, v in zip(('prooflist', 'nextproof', 'topwff', 'wffstack'), st.tuple()):
    sim.reg[r] = mpz(v)
try:
    sim.run_iterations(1)
    sys.exit('did not halt')
except Halted:
    print('halting: deriving v0 e. v0 halts the machine')
