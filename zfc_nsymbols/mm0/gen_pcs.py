"""Generate the per-step lemmas.

* prefix: the prologue (from the tape the boot leaves, no registers) and k215P's run from its
  initial state, following the branches it takes, while the register file is still partial;
* main: from the first configuration with all 9 registers, every (pc, canonical tape) reachable
  over both branches of every decnz.

Writes kz_p<NNN>.mm1 (chunks), entries.json (the lemmas: name, pc, tape, branch, k, result) and
prefix.json (the run: P states with concrete registers).  usage: gen_pcs.py D [chunk size]
"""
import os, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..'))
from gen_sim import Sim, strip, branches, pc_theorem, start_vals
from program import P


def pstep(pc, regs):
    e = P[pc]
    regs = list(regs)
    if e['tag'] == 0:
        regs[e['arg']] += 1
        return e['pos'], regs, 'inc'
    if e['tag'] == 1:
        if regs[e['arg']]:
            regs[e['arg']] -= 1
            return e['pos'], regs, 'decp'
        return e['zero'], regs, 'dec0'
    if e['tag'] == 4:
        return None, regs, 'halt'
    return e['zero'], regs, 'ctl'


def main(D, chunk):
    S = Sim(D)
    thms, entries = [], []
    seen = {}

    def lemma(pc, digits, br, k, tag):
        key = (pc, digits, br, k)
        if key in seen:
            return seen[key]
        name = f'kzP{len(entries)}'
        if pc is None:
            # the prologue: from the fresh tape, k = 0, through the 4 incs to pc 0
            from gen_sim import fold, Cfg
            segs, cfg, d2, v2, k2, pc2 = S.run(digits, [], 'inc', 0)
            a = S.conf(digits, [])
            pf, kind = fold(segs)
            thm = f"theorem {name} (J: nat):\n  $ kzReachP {a}\n    {cfg} $ =\n'{pf};"
            res = (pc2, d2, v2, k2)
        else:
            thm, res = pc_theorem(S, name, pc, digits, br, k)
        thms.append(thm)
        ent = dict(name=name, pc=pc, digits=list(digits), branch=br, k=k, tag=tag,
                   next_pc=res[0], next_digits=list(res[1]) if res[1] is not None else None,
                   next_vals=res[2], next_k=res[3])
        entries.append(ent)
        seen[key] = ent
        return ent

    # the prologue
    ent = lemma(None, (), 'inc', 0, 'prologue')
    assert ent['next_pc'] == 0 and ent['next_k'] == 1
    pc, digits, k = 0, tuple(ent['next_digits']), 1
    regs = [4] + [0] * 8
    run = [dict(pc=pc, digits=list(digits), k=k, regs=regs, lemma=None)]
    while k < 9:
        npc, nregs, br = pstep(pc, regs)
        ent = lemma(pc, digits, br, k, 'prefix')
        assert ent['next_pc'] == npc, (pc, ent['next_pc'], npc)
        run[-1]['lemma'] = ent['name']
        run[-1]['branch'] = br
        pc, digits, k, regs = npc, tuple(ent['next_digits']), ent['next_k'], nregs
        run.append(dict(pc=pc, digits=list(digits), k=k, regs=regs, lemma=None))
    print('prefix:', len(run) - 1, 'k215P steps', file=sys.stderr)
    # the main part: closure over (pc, tape)
    todo = [(pc, digits)]
    states = {(pc, digits)}
    while todo:
        pc, digits = todo.pop()
        for br in branches(P[pc]):
            ent = lemma(pc, digits, br, 9, 'main')
            if ent['next_pc'] == 'halt':
                continue
            nxt = (ent['next_pc'], tuple(ent['next_digits']))
            assert ent['next_k'] == 9
            if nxt not in states:
                states.add(nxt)
                todo.append(nxt)
    print('main:', len(states), '(pc, tape) states,', len(entries), 'lemmas', file=sys.stderr)
    # chunks
    nchunks = (len(thms) + chunk - 1) // chunk
    for c in range(nchunks):
        with open(os.path.join(HERE, f'kz_p{c:03d}.mm1'), 'w') as f:
            f.write('import "kz_mac.mm1";\n\n' + '\n'.join(thms[c * chunk:(c + 1) * chunk]) + '\n')
    json.dump(dict(entries=entries, states=sorted([pc, list(d)] for pc, d in states), nchunks=nchunks),
              open(os.path.join(HERE, 'entries.json'), 'w'))
    json.dump(run, open(os.path.join(HERE, 'prefix.json'), 'w'))
    print(nchunks, 'chunks', file=sys.stderr)


if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]) if len(sys.argv) > 2 else 500)
