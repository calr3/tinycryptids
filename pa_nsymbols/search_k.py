"""Simulated annealing over the program's axiom order, each axiom's variant (parameter
relabelling and equivalent form, ../pa/program.PA.FORMS) and its switches, for the k-symbol
compile's instruction count (cf. ../pa/search_variants.py).

    python3 search_k.py D SEED ITERATIONS [maxdepth] [start=LOGFILE]

The count includes the cheapest boot whose gap holds the program counter (BOOTS: instructions,
gap), else one instruction per cell (the straight-line boot).
"""
import os, sys, random, math, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'pa'))
sys.path.insert(0, HERE)
import program, ir, kary

kary.Compiler.number_registers = lambda self: None     # the count does not depend on it
PERMS = list(itertools.permutations((1, 2, 3)))
NAMES = ['B1', 'B2', 'B3', 'B4', 'B6b', 'B6c', 'B7', 'B8a', 'B8b', 'B8c', 'E']
SWITCHES = {'vchain': ['half', 'nested', 'flat']}
BOOTS = [(7, 12), (8, 39)]


def boot_cost(depth):
    return min([n for n, g in BOOTS if depth <= g] + [depth])


def size(D, cfg, maxdepth):
    order, var, sw = cfg
    sw = dict(sw)
    seed = sw.pop('grammar_seed', None)
    try:
        c = kary.Compiler(D, ir=ir.prog(order=order, variants=var, **sw), grammar_seed=seed)
    except AssertionError:
        return 10**6
    n = c.count() - c.G + boot_cost(c.pc_depth)
    return n + (1000 if c.pc_depth > maxdepth else 0)


def mutate(rnd, cfg):
    order, var, sw = cfg[0][:], dict(cfg[1]), dict(cfg[2])
    r = rnd.random()
    if r < 0.05:
        k = rnd.choice(list(SWITCHES))
        sw[k] = rnd.choice(SWITCHES[k])
    elif r < 0.1:
        if 'grammar_seed' in sw and rnd.random() < 0.3:
            del sw['grammar_seed']
        else:
            sw['grammar_seed'] = rnd.randrange(10**6)
    elif r < 0.35:
        i, j = rnd.sample(range(len(order)), 2)
        order[i], order[j] = order[j], order[i]
    else:
        name = rnd.choice(NAMES + ['B6a'])
        perm, form = var.get(name, ((1, 2, 3), 0))
        if name == 'B6a':
            perm = rnd.choice([(1, 2, 3), (2, 1, 3)])
            form = rnd.randrange(2)
        elif rnd.random() < 0.5 or len(program.PA.FORMS[name]) == 1:
            perm = rnd.choice(PERMS)
        else:
            form = rnd.randrange(len(program.PA.FORMS[name]))
        var[name] = (perm, form)
    return order, var, sw


if __name__ == '__main__':
    D, seed, iters = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    args = [a for a in sys.argv[4:] if not a.startswith('start=')]
    starts = [a[6:] for a in sys.argv[4:] if a.startswith('start=')]
    maxdepth = int(args[0]) if args else 99
    rnd = random.Random(seed)
    cfg = (list(program.ORDER), dict(program.VARIANTS), {})
    if starts:
        line = [l for l in open(starts[0]) if l.strip() and not l.startswith('start')][-1]
        cfg = eval(line.split(' ', 2)[2])
    cur = size(D, cfg, maxdepth)
    best = (cur, cfg)
    print('start', cur, flush=True)
    T = 2.0
    for it in range(iters):
        new = mutate(rnd, cfg)
        n = size(D, new, maxdepth)
        if n <= cur or rnd.random() < math.exp((cur - n) / T):
            cfg, cur = new, n
            if n < best[0]:
                best = (n, new)
                print(it, n, new, flush=True)
        T = max(0.05, T * 0.999)
    print('best', best[0], best[1])
