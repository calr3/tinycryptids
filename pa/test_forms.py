"""Every axiom form of program.PA.FORMS (postfix over a, b, c, v0..v3) evaluates to the same
wff as the hand-written ref.FORMS, for random parameters and every relabelling, and every
form > 0 is a tautological rewrite of form 0 (checked by evaluating both as propositional
formulas over their maximal non-propositional subformulas, for all truth assignments; for E,
the matrices under the common prefix E.v1 A.v0).

    python3 test_forms.py
"""
import os, sys, random, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import program, ref

OPS = {'eq': 0, 'el': 1, 'imp': 2, 'all': 4}


def postfix(text, a, b, c):
    st = []
    for t in text.split():
        if t[0] == 'v':
            st.append(int(t[1:]))
        elif t in 'abc':
            st.append({'a': a, 'b': b, 'c': c}[t])
        elif t == 'neg':
            st.append(ref.neg(st.pop()))
        elif t == 'ex':
            y, x = st.pop(), st.pop(); st.append(ref.ex(x, y))
        elif t == 'and':
            y, x = st.pop(), st.pop(); st.append(ref.and_(x, y))
        else:
            y, x = st.pop(), st.pop(); st.append(ref.pair(ref.pair(x, y), OPS[t]))
    assert len(st) == 1
    return st[0]


def truth(w, atoms, val):
    """Truth value of wff code w read propositionally: -> and -. are connectives, any other
    wff is an atom (looked up in val by code)."""
    x, op = ref.unpair(w)
    if op == 2:
        p, q = ref.unpair(x)
        return (not truth(p, atoms, val)) or truth(q, atoms, val)
    if op == 3:
        return not truth(x, atoms, val)
    atoms.add(w)
    return val.get(w, False)


def strip_e(w):
    """E = E.v1 A.v0 M = -. A.v1 -. A.v0 M: return M (the forms of E differ only in M, and
    provably equivalent matrices give provably equivalent quantified formulas)."""
    x, op = ref.unpair(w); assert op == 3                 # -.
    x, op = ref.unpair(x); assert op == 4                 # A.
    v, x = ref.unpair(x); assert v == 1
    x, op = ref.unpair(x); assert op == 3                 # -.
    x, op = ref.unpair(x); assert op == 4                 # A.
    v, m = ref.unpair(x); assert v == 0
    return m


def tautologically_equal(w1, w2):
    atoms = set()
    truth(w1, atoms, {}); truth(w2, atoms, {})
    atoms = sorted(atoms)
    for bits in itertools.product((False, True), repeat=len(atoms)):
        val = dict(zip(atoms, bits))
        if truth(w1, set(), val) != truth(w2, set(), val):
            return False
    return True


rnd = random.Random(3)
n = 0
for name, forms in program.PA.FORMS.items():
    for f, text in enumerate(forms):
        for k, v in program.PA.E_PARTS.items():
            text = text.replace(k, v)
        for _ in range(20):
            # distinct atomic formulas as parameters, so that the tautology check treats them as
            # propositional atoms (B6a: c distinct from a, b)
            a, b, c = rnd.sample(sorted({ref.el(i, j) for i in range(6) for j in range(6)}), 3)
            want = ref.FORMS[name][f](a, b, c)
            assert postfix(text, a, b, c) == want, (name, f)
            if f > 0:
                w0 = ref.FORMS[name][0](a, b, c)
                if name == 'E':
                    want, w0 = strip_e(want), strip_e(w0)
                assert tautologically_equal(want, w0), (name, f)
            n += 1
print(f'{n} checks: program forms == ref forms; forms > 0 are tautologically equivalent to form 0')
