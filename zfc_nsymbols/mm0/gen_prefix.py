"""kz_prefix.mm1: the start.  The machine from the blank tape reaches (boot, prologue, the first
k215P steps with a partial register file) the configuration of k215P's state after N steps,
which is related to it; and k215PIter N k215PInitial is that state.  usage: gen_prefix.py D"""
import os, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..'))
from gen_sim import Sim, cells, Rep, FileRef, Cfg, Push, ZERO
from gen_rel import pnum
from gen_glue import Glue
from program import P


def conf(S, digits, vals):
    return Cfg('st', S.root, Push(0, ZERO), cells(list(digits), Rep(S.M.G - len(digits), FileRef(vals))))


def vec(regs):
    return '(k215PVector ' + ' '.join(pnum(r) for r in regs) + ')'


def pstate(pc, regs):
    return f'(k215PState {pnum(pc)} {vec(regs)})'


def main(D, chunk=40):
    S = Sim(D)
    G = Glue(D)
    look = G.look
    run = json.load(open(os.path.join(HERE, 'prefix.json')))
    E = json.load(open(os.path.join(HERE, 'entries.json')))
    prologue = E['entries'][0]['name']
    order = S.m.reg_order
    out = ['import "kz_halt.mm1";', 'import "kz_boot.mm1";', '']
    # the machine: kzBoot, the prologue, then the prefix lemmas, in segments with explicit ends
    confs = [conf(S, r['digits'], [pnum(r['regs'][o]) for o in order[:r['k']]]) for r in run]
    names = ['kzBoot', prologue] + [r['lemma'] for r in run[:-1]]
    # names[0]: blank -> conf of the fresh tape (k = 0); names[1]: -> confs[0]; names[i + 2]: confs[i] -> confs[i + 1]
    segs, cur = [], None
    pieces = []
    last = None
    for i in range(1, len(names)):
        pieces.append(names[i])
        if len(pieces) == chunk or i == len(names) - 1:
            end = confs[i - 1]
            nm = f'kzPre{len(segs)}'
            acc = pieces[-1]
            for p in reversed(pieces[:-1]):
                acc = f'(kzRP_RP {p} {acc})'
            start = 'kzBoot' if not segs else None
            if segs:
                a = segs[-1][1]
                out.append(f"theorem {nm}: $ kzReachP {a}\n    {end} $ =\n'{acc};")
            else:
                out.append(f"theorem {nm}: $ kzReachP (kzState 0 0 0)\n    {end} $ =\n'(kzRP_RP kzBoot {acc});")
            segs.append((nm, end))
            pieces = []
    acc = segs[-1][0]
    for nm, _ in reversed(segs[:-1]):
        acc = f'(kzRP_RP {nm} {acc})'
    cN = confs[-1]
    out.append(f"theorem kzTMpre: $ kzReachP (kzState 0 0 0)\n    {cN} $ =\n'{acc};")
    # k215P: k215PIter n k215PInitial = s_n
    def pstep(pc, regs):
        e = P[pc]
        LK = look[str(pc)][0]
        a = e['arg']
        if e['tag'] == 0:
            return (f'(eqtr (k215PAtCI {LK}) (k215PStateeq2 (eqtr (k215PSeteq2 (suceq k215PGet{a}_vector)) '
                    f'k215PSet{a}_vector)))')
        if e['tag'] == 1:
            if regs[a] == 0:
                return f'(eqtr (k215PAtCD {LK}) (ifpos k215PGet{a}_vector))'
            return (f'(eqtr (k215PAtCD {LK}) (eqtr (ifneg (mpbir (noteq (eqeq1 k215PGet{a}_vector)) peano1)) '
                    f'(k215PStateeq2 (eqtr (k215PSeteq2 (eqtr (subeq1 k215PGet{a}_vector) sucsub1)) k215PSet{a}_vector))))')
        return f'({"k215PAtCB" if e["tag"] == 2 else "k215PAtCC"} {LK})'
    N = len(run) - 1
    prev = None
    for n0 in range(0, N, chunk):
        n1 = min(N, n0 + chunk)
        pf = 'k215PIter_zero' if n0 == 0 else prev
        for n in range(n0, n1):
            pf = f'(eqtr k215PIter_succ (eqtr (k215PStepeq {pf}) {pstep(run[n]["pc"], run[n]["regs"])}))'
        nm = f'kzPI{n1}'
        out.append(f"theorem {nm}: $ k215PIter {pnum(n1)} k215PInitial = {pstate(run[n1]['pc'], run[n1]['regs'])} $ =\n'{pf};")
        prev = nm
    # the relation at the switch
    pcN, dN, rN = run[-1]['pc'], tuple(run[-1]['digits']), run[-1]['regs']
    i = G.index[(pcN, dN)]
    eqs = [f'(eqtr (k215PR{o}eq k215PRegs_state) k215PR{o}_vector)' for o in order]
    leaf = f'(iani k215PPC_state (eqcom {G.conf_cong(dN, eqs)}))'
    out.append(f"theorem kzRelpre: $ kzRel {pstate(pcN, rN)}\n    {cN} $ =\n'{G.intro(i, leaf)};")
    out.append(f'-- N = {N}')
    open(os.path.join(HERE, 'kz_prefix.mm1'), 'w').write('\n'.join(out) + '\n')
    json.dump(dict(N=N), open(os.path.join(HERE, 'prefix_n.json'), 'w'))
    print('prefix N =', N, file=sys.stderr)


if __name__ == '__main__':
    main(int(sys.argv[1]))
