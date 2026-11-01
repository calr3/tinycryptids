"""Write kz_tm.mm0 / kz_tm.mm1: the transition table of the machine built by ../build.py, run from
the blank tape.  usage: gen_spec.py D"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
import build

PEANO = 'k215-pa/lean-mm0/vendor/peano'


def num(n):
    return str(n) if n <= 10 else f'kzNum{n}'


def machine_numbers(D):
    m = build.machine(D)
    _, qs = build.named(m)
    idx = {q: i for i, q in enumerate(qs)}
    return m, qs, idx


def spec(D):
    m, qs, idx = machine_numbers(D)
    N, K = len(qs), D + 2
    H = N
    out = [f'import "{PEANO}.mm0";', '',
           f'-- The {K}-symbol machine zfc_nsymbols/machines/zfc_{K}sym_{m.count()}.txt: {N} states',
           f'-- (0 .. {N - 1}, state 0 starts), halt label {H}; symbols 0 .. {K - 1}, 0 blank.', '']
    for n in range(11, max(N, K) + 1):
        out.append(f'def kzNum{n}: nat = $ suc {num(n - 1)} $;')
    out += ['', f'def kzK: nat = $ {num(K)} $;', f'def kzH: nat = $ {num(H)} $;', '',
            '-- nth n l is suc (the n-th element) or 0', 'def kzNth (n l: nat): nat = $ nth n l - 1 $;', '',
            '-- an action (w, d, t): write w, move left (d = 0) or right (d = 1), go to state t;',
            '-- undefined transitions go to the halt label']
    for i, q in enumerate(qs):
        acts = []
        for b in range(K):
            t = m.tm.get((q, b))
            if t is None:
                acts.append(f'(0, 1, kzH)')
            else:
                w, d, tq = t
                tgt = 'kzH' if tq == 'halt' else num(idx[tq])
                acts.append(f'({num(w)}, {1 if d == "R" else 0}, {tgt})')
        out.append(f'def kzRow{i}: nat = $ ' + ' : '.join(acts) + ' : 0 $;  -- ' + q)
    out.append('def kzTable: nat = $ ' + ' : '.join(f'kzRow{i}' for i in range(N)) + ' : 0 $;')
    out += ['',
            'def kzAction (q b: nat): nat = $ kzNth b (kzNth q kzTable) $;',
            'def kzState (q l r: nat): nat = $ (q, l, r) $;',
            'def kzQ (s: nat): nat = $ fst s $;',
            'def kzL (s: nat): nat = $ fst (snd s) $;',
            'def kzR (s: nat): nat = $ snd (snd s) $;',
            'def kzWrite (a: nat): nat = $ fst a $;',
            'def kzDir (a: nat): nat = $ fst (snd a) $;',
            'def kzTarget (a: nat): nat = $ snd (snd a) $;',
            '-- tapes are numbers in base kzK, the head cell (right) / the cell left of it (left) lowest',
            'def kzMove (a l r: nat): nat =',
            '$ if (kzDir a = 0)',
            '    (kzState (kzTarget a) (l // kzK) (l % kzK + kzK * (kzWrite a + kzK * (r // kzK))))',
            '    (kzState (kzTarget a) (kzWrite a + kzK * l) (r // kzK)) $;',
            'def kzStep (s: nat): nat =',
            '$ if (kzQ s < kzH) (kzMove (kzAction (kzQ s) (kzR s % kzK)) (kzL s) (kzR s)) s $;',
            'def kzRun (n s .x: nat): nat = $ rec s (\\ x, kzStep x) n $;',
            'def kzHalts (.n: nat): wff = $ E. n kzQ (kzRun n (kzState 0 0 0)) = kzH $;', '']
    return '\n'.join(out)


if __name__ == '__main__':
    D = int(sys.argv[1])
    s = spec(D)
    open(os.path.join(HERE, 'kz_tm.mm0'), 'w').write(s)
    # the .mm1 has the same definitions (with automatic equality theorems)
    s1 = s.replace(f'import "{PEANO}.mm0";', f'import "{PEANO}.mm1";')
    s1 = '\n'.join(('@_ ' + l if l.startswith('def ') else l) for l in s1.split('\n'))
    open(os.path.join(HERE, 'kz_tm.mm1'), 'w').write(s1)
    print('kz_tm.mm0 written')
