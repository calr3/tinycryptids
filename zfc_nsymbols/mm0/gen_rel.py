"""kz_rel.mm1: the simulation relation.  kzD<i> s c: the k215P state s has the pc of state i and
c is state i's configuration with s's registers;  kzRel s c: a balanced disjunction of them.
usage: gen_rel.py D"""
import os, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gen_sim import Sim, cells, Rep, FileRef, Cfg, Push, ZERO, nd
from gen_spec import num


def pnum(pc):
    return str(pc) if pc <= 9 else (f'k215Num{pc}' if pc <= 215 else f'k215PNum{pc}')


def regs_of(order, v):
    return [f'(k215PR{o} {v})' for o in order]


def conf_of(S, digits, v, virtual=False):
    vals = regs_of(S.m.reg_order, v) + ['0'] * nd()
    r = cells(list(digits), Rep(S.M.G - len(digits), FileRef(vals)))
    if virtual:
        return Cfg('st', S.M.q('scan'), ZERO, Push(0, r))
    return Cfg('st', S.root, Push(0, ZERO), r)


def tree(xs):
    if len(xs) == 1:
        return xs[0]
    h = len(xs) // 2
    return f'({tree(xs[:h])} \\/ {tree(xs[h:])})'


def main(D):
    S = Sim(D)
    E = json.load(open(os.path.join(HERE, 'entries.json')))
    states = [(pc, tuple(d)) for pc, d in E['states']]
    out = ['import "kz_mac.mm1";',
           'import "k215-pa/pa-mm0/k215_literal_runtime_registers.mm1";',
           'import "k215-pa/pa-mm0/k215_literal_runtime_progress.mm1";',
           'import "k215-pa/pa-mm0/k215_literal_runtime_native_interface.mm1";', '']
    for i, (pc, d) in enumerate(states):
        c = conf_of(S, d, '(k215PRegs s)', pc in S.m.virtual_pcs)
        out.append(f'@_ local def kzD{i} (s c: nat): wff = $ k215PPC s = {pnum(pc)} /\\ c = {c} $;')
    out.append('@_ local def kzRel (s c: nat): wff = $ ' + tree([f'kzD{i} s c' for i in range(len(states))]) + ' $;')
    open(os.path.join(HERE, 'kz_rel.mm1'), 'w').write('\n'.join(out) + '\n')
    json.dump([[pc, list(d)] for pc, d in states], open(os.path.join(HERE, 'states.json'), 'w'))
    print(len(states), 'states', file=sys.stderr)


if __name__ == '__main__':
    main(int(sys.argv[1]))
