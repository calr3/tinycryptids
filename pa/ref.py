"""Reference model of one main-loop iteration, written directly from the axiom schemas.

State between iterations: prooflist, nextproof (the proof enumeration), topwff (the last theorem)
and wffstack (the other theorems, as nested pairs).  A wff is a number:
    x = y : pair(pair(x, y), 0)     x e. y : pair(pair(x, y), 1)     ph -> ps : pair(pair(ph, ps), 2)
    -. ph : pair(ph, 3)             A. x ph : pair(pair(x, ph), 4)
with variables v_i = i, and pair(a, b) = (a + b)(a + b + 1)/2 + a.  Codes are not unique (1 is
both v_1 and v0 e. v0); the theory only ever compares codes.

Each iteration decodes one step (axiomcode, p1, p2, p3) from prooflist, pushes the last theorem,
computes every candidate (an axiom instance or a rule application), keeps candidate number
axiomcode (counting from 1; 0 keeps the default v0 = v0, code 0; codes past the end keep the last
candidate), and halts if the kept wff is 1 = v0 e. v0.
"""
from dagsim import pair, unpair


def eq(x, y): return pair(pair(x, y), 0)
def el(x, y): return pair(pair(x, y), 1)
def imp(x, y): return pair(pair(x, y), 2)
def neg(x): return pair(x, 3)
def all_(x, y): return pair(pair(x, y), 4)
def ex(x, y): return neg(all_(x, neg(y)))
def and_(x, y): return neg(imp(x, neg(y)))


FALSUM = el(0, 0)
assert FALSUM == 1 and eq(0, 0) == 0

# Tarski's system S2 (as in pa.py) and Friedman's axiom.  B6a needs p3 distinct from p1, p2.
AXIOMS = {
    'B1': lambda p1, p2, p3: imp(imp(p1, p2), imp(imp(p2, p3), imp(p1, p3))),
    'B2': lambda p1, p2, p3: imp(imp(neg(p1), p1), p1),
    'B3': lambda p1, p2, p3: imp(p1, imp(neg(p1), p2)),
    'B4': lambda p1, p2, p3: imp(all_(p1, imp(p2, p3)), imp(all_(p1, p2), all_(p1, p3))),
    'B6a': lambda p1, p2, p3: (and_(imp(eq(p1, p2), all_(p3, eq(p1, p2))),
                                    imp(el(p1, p2), all_(p3, el(p1, p2))))
                               if p3 != p1 and p3 != p2 else 0),
    'B6b': lambda p1, p2, p3: imp(all_(p1, all_(p2, p3)), all_(p2, all_(p1, p3))),
    'B6c': lambda p1, p2, p3: imp(ex(p1, all_(p1, p2)), p2),
    'B7': lambda p1, p2, p3: ex(p1, eq(p1, p2)),
    'B8a': lambda p1, p2, p3: imp(eq(p1, p2), imp(eq(p1, p3), eq(p2, p3))),
    'B8b': lambda p1, p2, p3: imp(eq(p1, p2), imp(el(p1, p3), el(p2, p3))),
    'B8c': lambda p1, p2, p3: imp(eq(p1, p2), imp(el(p3, p1), el(p3, p2))),
    'E': lambda p1, p2, p3: ex(1, all_(0, and_(
        imp(imp(neg(el(0, 2)), eq(0, 3)), imp(all_(1, p1), el(0, 1))),
        imp(el(0, 1), all_(1, p1))))),
}

def _e(a, form):
    # form bits: 1 = antecedents A, B swapped; 2 = conjuncts swapped; 4 = A written as
    # (-. v0 = v3 -> v0 e. v2), tautologically equivalent to (-. v0 e. v2 -> v0 = v3)
    A = imp(neg(eq(0, 3)), el(0, 2)) if form & 4 else imp(neg(el(0, 2)), eq(0, 3))
    B = all_(1, a)
    C = el(0, 1)
    ant = imp(B, imp(A, C)) if form & 1 else imp(A, imp(B, C))
    cons = imp(C, B)
    return ex(1, all_(0, and_(cons, ant) if form & 2 else and_(ant, cons)))


# Equivalent forms of each axiom (form 0 is the one above), as functions of the formal
# parameters a, b, c.  Forms > 0 swap two antecedents or commute a conjunction: each is
# tautologically equivalent to form 0, so either one gives the same theorems.
FORMS = {
    'B1': [lambda a, b, c: AXIOMS['B1'](a, b, c)],
    'B2': [lambda a, b, c: AXIOMS['B2'](a, b, c)],
    'B3': [lambda a, b, c: AXIOMS['B3'](a, b, c)],
    'B4': [lambda a, b, c: AXIOMS['B4'](a, b, c),
           lambda a, b, c: imp(all_(a, b), imp(all_(a, imp(b, c)), all_(a, c)))],
    'B6b': [lambda a, b, c: AXIOMS['B6b'](a, b, c)],
    'B6c': [lambda a, b, c: AXIOMS['B6c'](a, b, c)],
    'B7': [lambda a, b, c: AXIOMS['B7'](a, b, c)],
    'B8a': [lambda a, b, c: AXIOMS['B8a'](a, b, c),
            lambda a, b, c: imp(eq(a, c), imp(eq(a, b), eq(b, c)))],
    'B8b': [lambda a, b, c: AXIOMS['B8b'](a, b, c),
            lambda a, b, c: imp(el(a, c), imp(eq(a, b), el(b, c)))],
    'B8c': [lambda a, b, c: AXIOMS['B8c'](a, b, c),
            lambda a, b, c: imp(el(c, a), imp(eq(a, b), el(c, b)))],
    'E': [lambda a, b, c, f=f: _e(a, f) for f in range(8)],
    'B6a': [lambda a, b, c: AXIOMS['B6a'](a, b, c),
            lambda a, b, c: (and_(imp(el(a, b), all_(c, el(a, b))), imp(eq(a, b), all_(c, eq(a, b))))
                             if c != a and c != b else 0)],
}
assert FORMS['E'][0](5, 0, 0) == AXIOMS['E'](5, 0, 0)


def axiom(name, variants, p1, p2, p3):
    """Candidate `name` with variants[name] = (perm, form): formal (a, b, c) = (p_perm[0], ...)."""
    perm, form = variants.get(name, ((1, 2, 3), 0))
    ps = (p1, p2, p3)
    return FORMS[name][form](ps[perm[0] - 1], ps[perm[1] - 1], ps[perm[2] - 1])


class State:
    def __init__(self, prooflist=0, nextproof=0, topwff=0, wffstack=0):
        self.prooflist, self.nextproof, self.topwff, self.wffstack = prooflist, nextproof, topwff, wffstack

    def tuple(self):
        return (self.prooflist, self.nextproof, self.topwff, self.wffstack)


# rev=False: wffstack = pair(top, rest), proof codes pair(component, rest)   (legion/pa.py)
# rev=True:  wffstack = pair(rest, top), proof codes pair(rest, component)   (program.py)

def split(n, rev):
    """(component, rest) of a stack or proof code."""
    a, b = unpair(n)
    return (b, a) if rev else (a, b)


def join(c, rest, rev):
    return pair(rest, c) if rev else pair(c, rest)


def decode(s, rev=False):
    """The common start of an iteration: next proof code, then (axiomcode, p1, p2, p3)."""
    if s.prooflist == 0:
        s.prooflist = s.nextproof
        s.nextproof += 1
    else:
        s.prooflist -= 1
    out = []
    for _ in range(4):
        a, s.prooflist = split(s.prooflist, rev)
        out.append(a)
    return out


def encode(ac, p1, p2, p3, rest=0, rev=False):
    """A prooflist value whose next step is (ac, p1, p2, p3), followed by rest."""
    return join(ac, join(p1, join(p2, join(p3, rest, rev), rev), rev), rev) + 1


def push(s, x, rev=False):
    s.wffstack = join(x, s.wffstack, rev)


def pop(s, rev=False):
    top, s.wffstack = split(s.wffstack, rev)
    return top


def iterate_original(s, order):
    """legion/pa.py: candidates in `order` (DET and GEN pop their premises when axiomcode is
    exactly 1 at their turn, i.e. when they will be the one kept)."""
    ac, p1, p2, p3 = decode(s)
    s.wffstack = pair(s.topwff, s.wffstack)
    sel = 0
    for name in order:
        if name == 'DET':
            if ac == 1:
                p3 = pop(s)
                p2 = pop(s)
            val = p1 if p2 == imp(p3, p1) else 0
        elif name == 'GEN':
            if ac == 1:
                p3 = pop(s)
            val = all_(p1, p3)
        else:
            val = AXIOMS[name](p1, p2, p3)
        if ac > 0:
            ac -= 1
            sel = val
    s.topwff = sel
    return sel == FALSUM


ORIGINAL_ORDER = ['DET', 'GEN', 'B1', 'B2', 'B3', 'B4', 'B6b', 'B8b', 'B6a', 'B6b', 'B6c', 'B7',
                  'B8a', 'B8b', 'B8c', 'E']


def iterate_tail(s, order, rev=True, shared_eq=True, variants={}):
    """The improved program (program.py): the axioms in `order`, then B6a, GEN and DET.  GEN
    pops the top theorem whenever GEN or DET will be kept.  DET then pops its major premise
    (shared_eq: the minor premise is the theorem GEN popped) or its two premises (otherwise: a
    DET step then uses the second and third theorems; the first is dropped)."""
    ac, p1, p2, p3 = decode(s, rev)
    push(s, s.topwff, rev)
    sel = 0

    def select(val):
        nonlocal ac, sel
        if ac > 0:
            ac -= 1
            sel = val
    for key in order:
        names = key.split('+')        # 'X+Y': the conjunction X /\ Y as one candidate
        w = axiom(names[0], variants, p1, p2, p3)
        for n in names[1:]:
            w = and_(w, axiom(n, variants, p1, p2, p3))
        select(w)
    select(axiom('B6a', variants, p1, p2, p3))
    # GEN: param3 is 0 here unless popped
    q3 = pop(s, rev) if ac > 0 else 0
    select(all_(p1, q3))
    # DET: param2 is 0 here unless popped
    if ac > 0:
        if not shared_eq:
            q3 = pop(s, rev)
        q2 = pop(s, rev)
    else:
        q2 = 0
    select(p1 if q2 == imp(q3, p1) else 0)
    s.topwff = sel
    return sel == FALSUM
