"""Condensed-detachment search for propositional theorems of Lukasiewicz's system
(the propositional base B1-B3 of the PA machine's theory):

    B1  CCpqCCqrCpr      B2  CCNppp      B3  CpCNpq

Finds D-proofs of the targets below and writes them to cd_proofs.txt (one derived theorem per
line: name, formula, major, minor), which gen_logic.py turns into Lean.  Formulas are tuples:
('C', a, b), ('N', a), or a variable (int).

    python3 cd_search.py
"""
import itertools, sys, time

AX = {'B1': 'CCpqCCqrCpr', 'B2': 'CCNppp', 'B3': 'CpCNpq'}
TARGETS = {
    'perm': 'CCpCqrCqCpr',     # permutation of antecedents
    'contra': 'CCpqCNqNp',     # contraposition
    'contr': 'CCpCpqCpq',      # contraction
    'andl': 'CNCpNqp',         # first part of a conjunction
    'idt': 'Cpp',
}


def parse(s):
    names = {}
    def go(i):
        c = s[i]
        if c == 'C':
            a, i = go(i + 1); b, i = go(i)
            return ('C', a, b), i
        if c == 'N':
            a, i = go(i + 1)
            return ('N', a), i
        if c not in names: names[c] = len(names)
        return names[c], i + 1
    t, i = go(0)
    assert i == len(s)
    return t


def show(t):
    if isinstance(t, int): return 'pqrstuvwxyzabcdefghijklmno'[t] if t < 26 else f'v{t}'
    if t[0] == 'N': return 'N' + show(t[1])
    return 'C' + show(t[1]) + show(t[2])


def size(t):
    if isinstance(t, int): return 1
    return 1 + sum(size(x) for x in t[1:])


def shift(t, k):
    if isinstance(t, int): return t + k
    return (t[0],) + tuple(shift(x, k) for x in t[1:])


def maxvar(t):
    if isinstance(t, int): return t
    return max((maxvar(x) for x in t[1:]), default=-1)


def walk(t, s):
    while isinstance(t, int) and t in s: t = s[t]
    return t


def occurs(v, t, s):
    t = walk(t, s)
    if t == v: return True
    if isinstance(t, int): return False
    return any(occurs(v, x, s) for x in t[1:])


def unify(a, b, s):
    a = walk(a, s); b = walk(b, s)
    if a == b: return s
    if isinstance(a, int):
        if occurs(a, b, s): return None
        s = dict(s); s[a] = b; return s
    if isinstance(b, int):
        return unify(b, a, s)
    if a[0] != b[0] or len(a) != len(b): return None
    for x, y in zip(a[1:], b[1:]):
        s = unify(x, y, s)
        if s is None: return None
    return s


def subst(t, s):
    t = walk(t, s)
    if isinstance(t, int): return t
    return (t[0],) + tuple(subst(x, s) for x in t[1:])


def canon(t):
    m = {}
    def go(t):
        if isinstance(t, int):
            if t not in m: m[t] = len(m)
            return m[t]
        return (t[0],) + tuple(go(x) for x in t[1:])
    return go(t)


def match(pat, t, s):
    """one-way: is t an instance of pat"""
    if isinstance(pat, int):
        if pat in s: return s if s[pat] == t else None
        s = dict(s); s[pat] = t; return s
    if isinstance(t, int) or pat[0] != t[0] or len(pat) != len(t): return None
    for x, y in zip(pat[1:], t[1:]):
        s = match(x, y, s)
        if s is None: return None
    return s


def cd(major, minor):
    """condensed detachment: major = C A B, minor unifies with A; result B"""
    if isinstance(major, int) or major[0] != 'C': return None
    k = maxvar(major) + 1
    mn = shift(minor, k)
    s = unify(major[1], mn, {})
    if s is None: return None
    return canon(subst(major[2], s))


def search(maxsize=24, timeout=1200):
    """Given-clause search, lightest theorem first, with forward subsumption (a new theorem that
    is an instance of a kept one is dropped)."""
    import heapq
    t0 = time.time()
    usable, names, queue, cnt = [], {}, [], 0
    def add(t, name, proof):
        nonlocal cnt
        heapq.heappush(queue, (size(t), cnt, t, name, proof)); cnt += 1
    for n, f in AX.items():
        add(canon(parse(f)), n, None)
    targets = {n: canon(parse(f)) for n, f in TARGETS.items()}
    found = {}
    while queue and time.time() - t0 < timeout:
        sz, _, t, name, proof = heapq.heappop(queue)
        if any(match(u[0], t, {}) is not None for u in usable):
            continue
        idx = len(usable)
        usable.append((t, name, proof)); names[name] = idx
        for tn, tg in targets.items():
            if tn not in found and match(t, tg, {}) is not None:
                found[tn] = idx
                print('found', tn, show(t), 'kept', idx, f'{time.time()-t0:.0f}s', flush=True)
        if len(found) == len(targets): break
        for j in range(len(usable)):
            for a, b in ((idx, j), (j, idx)):
                r = cd(usable[a][0], usable[b][0])
                if r is None or size(r) > maxsize: continue
                add(r, f'u{cnt}', (usable[a][1], usable[b][1]))
    return usable, names, found


if __name__ == '__main__':
    maxsize = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    usable, names, found = search(maxsize)
    need = set()
    def walk(name):
        if name in need: return
        t, n, p = usable[names[name]]
        if p: walk(p[0]); walk(p[1])
        need.add(name)
    for tn, idx in found.items(): walk(usable[idx][1])
    with open('cd_proofs.txt', 'w') as f:
        for n in sorted(need, key=lambda n: names[n]):
            t, nm, p = usable[names[n]]
            f.write(f'{nm} {show(t)} {"" if p is None else p[0] + " " + p[1]}\n')
        for tn, idx in found.items():
            f.write(f'target {tn} {usable[idx][1]} {TARGETS[tn]}\n')
    print(len(need), 'theorems used; missing:', set(TARGETS) - set(found))
