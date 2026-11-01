"""Write kz_act.mm1: bounds of the digits and states, the row of every state, and
kzAction q b = (w, d, t) for every defined transition of the machine.  usage: gen_act.py D"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_spec
from gen_spec import num


def nested(lemma, n, base):
    s = base
    for _ in range(n):
        s = f'(eqtr {lemma} {s})'
    return s


def act_lines(D):
    m, qs, idx = gen_spec.machine_numbers(D)
    N, K = len(qs), m.K
    out = ['import "kz_lib.mm1";', '']
    # bounds
    out.append(f'theorem kzLtK_{K - 1}: $ {num(K - 1)} < kzK $ = \'ltsucid;')
    for b in range(K - 2, -1, -1):
        out.append(f'theorem kzLtK_{b}: $ {num(b)} < kzK $ = \'(kzLt_suc kzLtK_{b + 1});')
    out.append(f'theorem kzLtH_{N - 1}: $ {num(N - 1)} < kzH $ = \'ltsucid;')
    for q in range(N - 2, -1, -1):
        out.append(f'theorem kzLtH_{q}: $ {num(q)} < kzH $ = \'(kzLt_suc kzLtH_{q + 1});')
    out.append('')
    for q in range(N):
        out.append(f'theorem kzT_{q}: $ kzNth {num(q)} kzTable = kzRow{q} $ = \'{nested("kzNth_S", q, "kzNth_0")};')
    out.append('')
    for q in range(N):
        for b in range(K):
            t = m.tm.get((qs[q], b))
            if t is None:
                continue
            w, d, tq = t
            tgt = 'kzH' if tq == 'halt' else num(idx[tq])
            act = f'({num(w)}, {1 if d == "R" else 0}, {tgt})'
            out.append(f'theorem kzA_{q}_{b}: $ kzAction {num(q)} {num(b)} = {act} $ = '
                       f'\'(eqtr (kzNtheq2 kzT_{q}) {nested("kzNth_S", b, "kzNth_0")});')
    return out


if __name__ == '__main__':
    D = int(sys.argv[1])
    open(os.path.join(HERE, 'kz_act.mm1'), 'w').write('\n'.join(act_lines(D)) + '\n')
    print('kz_act.mm1 written')
