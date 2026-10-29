"""Every pair / unpair node of a compiled machine, entered afresh from small random registers,
plain execution vs the formula ksim applies (cf. ../pa/check_accel.py).

    python3 check_kaccel.py D [trials]
"""
import os, sys, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'pa'))
sys.path.insert(0, HERE)
import kary, kbuild
from ksim import KSim, PAIR, UNPAIR, FRESH, mpz


def paths(c):
    """one PC path (cell symbols of the ancestors) to every node"""
    out = {c.root: ()}
    st = [c.root]
    while st:
        i = st.pop()
        vals = c.val[i][0]
        for x, v in zip(c.nodes[i], vals):
            if not isinstance(x, str) and x not in out:
                out[x] = out[i] + (v + 1,)
                st.append(x)
    return out


def check(c, trials=30, seed=1):
    rnd = random.Random(seed)
    P = paths(c)
    n = 0
    for i in c.nodes:
        q = c.state_name(i)
        m = PAIR.match(q) or UNPAIR.match(q)
        if not m:
            continue
        for t in range(trials):
            regs0 = {r: mpz(rnd.randint(0, 6)) for r in KSim(c).reg}
            x, y, z = m.groups()
            if UNPAIR.match(q):
                regs0[x] = regs0[y] = 0
            res = []
            for sub in (False, True):
                sim = KSim(c, accel=False, accel_sub=sub)
                sim.reg = dict(regs0)
                sim.pc = list(P[i])
                pos = len(P[i])
                # run until the node's parent cell changes (the node is done)
                before = sim.pc[pos - 1]
                k = 0
                while True:
                    sim.step()
                    k += 1
                    if sim.get(pos - 1) != before:
                        break
                    assert k < 10**6
                res.append((dict(sim.reg), tuple(sim.pc[:pos])))
            assert res[0] == res[1], (q, regs0, res)
            n += 1
    return n


if __name__ == '__main__':
    D = int(sys.argv[1])
    c = kbuild.build(D)          # the machine of machines/pa_<D+2>sym_*.txt
    print(f'D={D}: {check(c, int(sys.argv[2]) if len(sys.argv) > 2 else 30)} accelerated entries match plain execution')
