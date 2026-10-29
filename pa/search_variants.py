"""Simulated annealing over the axiom order and each axiom's variant (parameter relabelling and
equivalent form, program.PA.FORMS).   python3 search_variants.py SEED ITERATIONS [key=value ...]"""
import os, sys, random, math, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import program

KW = {}
T0 = 2.0
for a in sys.argv[3:]:
    if a.startswith('start='):
        continue
    if a.startswith('T0='):
        T0 = float(a[3:]); continue
    k, v = a.split('=', 1)
    KW[k] = v if k == 'vchain' else eval(v)
PERMS = list(itertools.permutations((1, 2, 3)))
NAMES = ['B1', 'B2', 'B3', 'B4', 'B6b', 'B6c', 'B7', 'B8a', 'B8b', 'B8c', 'E']

BREAKERS = [(), ('pair(scratch1,wffstack,topwff).0',), ('pushwff().0',),
            ('pushwff().0', 'cons().0'), ('pushwff().0', 'wn().0'), ('pushwff().0', 'wim().0'),
            ('pushwff().0', 'unpair(scratch2,scratch1,wffstack).0'), ('v_1().0',), ('wn().0',)]

def size(order, var):
    kw = dict(KW)
    if '_br' in var:
        kw['breakers'] = BREAKERS[var['_br']]
    if '_g' in var:
        kw['grammar_seed'], kw['grammar_p'] = var['_g']
    v = {k: x for k, x in var.items() if not k.startswith('_')}
    return program.build(order=order, variants=v, **kw).state_count()

def mutate(rnd, order, var):
    order, var = order[:], dict(var)
    r = rnd.random()
    if r < 0.04:
        var['_br'] = rnd.randrange(len(BREAKERS))
    elif r < 0.07:
        var['_g'] = rnd.choice([None, (rnd.randrange(10**6), rnd.choice([0.1, 0.2]))])
        if var['_g'] is None:
            del var['_g']
    elif r < 0.12:
        # merge two non-propositional candidates into a conjunction, or split one
        merged = [i for i, k in enumerate(order) if '+' in k]
        if merged and rnd.random() < 0.5:
            i = rnd.choice(merged); parts = order.pop(i).split('+')
            for p in parts:
                order.insert(rnd.randrange(len(order) + 1), p)
        else:
            ok = [i for i, k in enumerate(order) if k not in ('B1', 'B2', 'B3')]
            if len(ok) >= 2:
                i, j = sorted(rnd.sample(ok, 2))
                y = order.pop(j); x = order.pop(i)
                order.insert(i, x + '+' + y)
    elif r < 0.35:
        i, j = rnd.sample(range(len(order)), 2); order[i], order[j] = order[j], order[i]
    else:
        name = rnd.choice(NAMES + ['B6a'])
        perm, form = var.get(name, ((1, 2, 3), 0))
        if name == 'B6a':
            perm = rnd.choice([(1, 2, 3), (2, 1, 3)]); form = rnd.randrange(2)
        elif rnd.random() < 0.5 or len(program.PA.FORMS[name]) == 1:
            perm = rnd.choice(PERMS)
        else:
            form = rnd.randrange(len(program.PA.FORMS[name]))
        var[name] = (perm, form)
    return order, var

if __name__ == '__main__':
    seed, iters = int(sys.argv[1]), int(sys.argv[2])
    rnd = random.Random(seed)
    order = list(program.ORDER); var = {}
    if len(sys.argv) > 3 and sys.argv[3].startswith('start='):
        order, var = eval(open(sys.argv[3][6:]).read())
        del sys.argv[3]
    curv = size(order, var); best = (curv, order, var)
    T = T0
    for it in range(iters):
        o, v = mutate(rnd, order, var)
        n = size(o, v)
        if n <= curv or rnd.random() < math.exp((curv - n) / T):
            order, var, curv = o, v, n
            if n < best[0]:
                best = (n, o, v); print(it, n, ','.join(o), v, flush=True)
        T = max(0.05, T * 0.998)
    print('best', best[0], ','.join(best[1]), best[2])
