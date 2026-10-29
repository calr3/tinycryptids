"""The improved PA program: same theory and the same register-machine style as legion/pa.py
(LegionMammal978, after A. J. Wade's zf2.py), reorganised to need fewer Turing-machine states.

Changes to the program (see README.md for why each one is sound):
  * the duplicate B6b and B8b candidates of pa.py are dropped;
  * the candidates are reordered (the order changes which subsequences the builder can share);
  * B6a, GEN and DET come last, so they may destroy the parameters instead of copying them:
    B6a compares p3 with p2 and p1 using two scratch registers (scratch3 is gone), DET compares
    its premise in place and moves p1 into the result;
  * GEN and DET pop their premises when axiomcode != 0 at their turn (one test, instead of
    pa.py's "axiomcode == 1" test); when DET is kept, GEN has popped once before it, so a DET
    step uses the second and third theorems of the stack;
  * param2 is not cleared at the start of an iteration: DET's comparison always leaves it 0.
The reference semantics is ref.iterate_tail.
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.setrecursionlimit(100000)
import tmbuilder
from tmbuilder import subroutine
sys.modules.setdefault('TMBuilder', tmbuilder)
sys.path.insert(0, os.path.join(HERE, 'legion'))
import pa as legion_pa

# candidate order found by search (search_order.py); B6a, GEN and DET always follow
ORDER = ['E', 'B2', 'B8c', 'B8b', 'B8a', 'B3', 'B7', 'B4', 'B6b', 'B1', 'B6c']
# each axiom's relabelling (formal a, b, c = param_i, param_j, param_k) and form (see FORMS),
# found with the order by search_variants.py
VARIANTS = {'E': ((3, 1, 2), 1), 'B4': ((1, 3, 2), 1), 'B8a': ((2, 3, 1), 0),
            'B8c': ((2, 1, 3), 0), 'B6a': ((2, 1, 3), 0), 'B6b': ((2, 1, 3), 0),
            'B3': ((2, 3, 1), 0), 'B7': ((2, 1, 3), 0), 'B1': ((3, 2, 1), 0),
            'B6c': ((2, 3, 1), 0), 'B2': ((3, 2, 1), 0), 'B8b': ((2, 3, 1), 0)}


class PA(legion_pa.PA):
    order = ORDER
    dispatch_reset = True
    merge_equal = True

    def __init__(self):
        tmbuilder.TMBuilder.__init__(self)
        self.prooflist = self.reg("prooflist")
        self.nextproof = self.reg("nextproof")
        self.topwff = self.reg("topwff")
        self.wffstack = self.reg("wffstack")
        self.axiomcode = self.reg("axiomcode")
        self.param1 = self.reg("param1")
        self.param2 = self.reg("param2")
        self.param3 = self.reg("param3")
        self.scratch1 = self.reg("scratch1")
        self.scratch2 = self.reg("scratch2")

    # stack_rev: wffstack = pair(rest, top) instead of pair(top, rest), and proof codes are
    # read as pair(rest, component).  Then every pop is one unpair instance, unpair(scratch2,
    # scratch1, .), and cons can build pair(a, b) with pushwff's pair instance (a moved into
    # wffstack first).  Wff codes are unchanged.
    stack_rev = True
    reload2 = True
    b6a2 = True
    shared_eq = True
    cascade = True

    def un(self, src):
        """scratch1 := second component, scratch2 := first component of src (src := 0)."""
        if self.stack_rev:
            return self.unpair(self.scratch2, self.scratch1, src)
        return self.unpair(self.scratch1, self.scratch2, src)

    @subroutine
    def pushwff(self):
        if not self.stack_rev:
            return super().pushwff()
        return [self.pair(self.scratch1, self.wffstack, self.topwff),
                self.while_decnz(self.scratch1, self.wffstack.inc)]

    @subroutine
    def cons(self):
        if not self.stack_rev:
            return super().cons()
        # stack = pair(rest, a), topwff = b  ->  topwff = pair(a, b), stack = rest
        return [self.un(self.wffstack),
                self.while_decnz(self.scratch1, self.wffstack.inc),
                self.pair(self.scratch1, self.wffstack, self.topwff),
                self.while_decnz(self.scratch1, self.topwff.inc),
                self.while_decnz(self.scratch2, self.wffstack.inc)]

    @subroutine
    def pop(self, p):
        """p (zero) := the top of wffstack, popped."""
        if not self.stack_rev:
            return [self.unpair(self.scratch1, self.scratch2, self.wffstack),
                    self.while_decnz(self.scratch2, self.wffstack.inc),
                    self.while_decnz(self.scratch1, p.inc)]
        return [self.un(self.wffstack),
                self.while_decnz(self.scratch2, self.wffstack.inc),
                self.while_decnz(self.scratch1, p.inc)]

    @subroutine
    def select(self):
        """Keep the candidate (topwff) if axiomcode != 0 (and decrement it), else restore the
        current selection from the stack."""
        if not self.stack_rev:
            return super().select()
        return [self.un(self.wffstack),
                self.while_decnz(self.scratch2, self.wffstack.inc),
                self.label("sel", [
                    [self.axiomcode.decnz, [self.zero(self.scratch1), "break_sel"]],
                    [self.zero(self.topwff), self.while_decnz(self.scratch1, self.topwff.inc)]])]

    def decode(self, target):
        """target (zero) := the next component of prooflist."""
        if self.stack_rev:
            return [self.un(self.prooflist),
                    self.while_decnz(self.scratch2, self.prooflist.inc),
                    self.while_decnz(self.scratch1, target.inc)]
        return [self.unpair(self.scratch1, self.scratch2, self.prooflist),
                self.while_decnz(self.scratch2, self.prooflist.inc),
                self.while_decnz(self.scratch1, target.inc)]

    @subroutine
    def ifsel(self, body):
        """if axiomcode != 0: body (axiomcode unchanged)."""
        return [[self.axiomcode.decnz, [self.axiomcode.inc, body]]]

    @subroutine
    def zero(self, r):
        return self.while_decnz(r, ())

    def b6a_check1(self, ZT):
        return [
            self.while_decnz(self.param3, [self.scratch1.inc, self.scratch2.inc]),
            self.if_eq(self.param2, self.scratch2, ZT),
            self.while_decnz(self.scratch1, self.scratch2.inc),
            self.while_decnz(self.param1, [self.param2.inc, self.scratch1.inc]),
            self.while_decnz(self.scratch1, self.param1.inc),
            self.if_eq(self.param2, self.scratch2, ZT)]

    def b6a_check2(self, ZT):
        # the same comparisons, built from loops that exist anyway
        return [
            self.while_decnz(self.param3, [self.scratch1.inc, self.scratch2.inc]),   # s1 = s2 = p3
            self.if_eq(self.param2, self.scratch2, ZT),                             # p2 vs p3
            self.while_decnz(self.scratch1, self.param2.inc),                       # param2 = p3
            self.while_decnz(self.param1, [self.scratch1.inc, self.scratch2.inc]),   # s1 = s2 = p1
            self.while_decnz(self.scratch1, self.param1.inc),                       # p1 restored
            self.if_eq(self.param2, self.scratch2, ZT)]                             # p3 vs p1

    # Axiom forms, in postfix over the formal parameters a, b, c (the permutation in
    # `variants` says which of param1..param3 each one is) and the variables v0..v3.
    # Forms other than 0 are tautologically equivalent rewrites (antecedents swapped, a
    # conjunction commuted); B1..B3, the propositional base, are only relabelled.
    FORMS = {
        'B1': ['a b imp b c imp a c imp imp imp'],
        'B2': ['a neg a imp a imp'],
        'B3': ['a a neg b imp imp'],
        'B4': ['a b c imp all a b all a c all imp imp',
               'a b all a b c imp all a c all imp imp'],
        'B6b': ['a b c all all b a c all all imp'],
        'B6c': ['a a b all ex b imp'],
        'B7': ['a a b eq ex'],
        'B8a': ['a b eq a c eq b c eq imp imp', 'a c eq a b eq b c eq imp imp'],
        'B8b': ['a b eq a c el b c el imp imp', 'a c el a b eq b c el imp imp'],
        'B8c': ['a b eq c a el c b el imp imp', 'c a el a b eq c b el imp imp'],
        'E': [f'v1 v0 {x} {y} and all ex' for x, y in (
            ('ANT1', 'CONS'), ('ANT2', 'CONS'), ('CONS', 'ANT1'), ('CONS', 'ANT2'),
            ('ANT3', 'CONS'), ('ANT4', 'CONS'), ('CONS', 'ANT3'), ('CONS', 'ANT4'))],
        # B6a: c is always param3 (the variable tested for distinctness)
        'B6a': ['a b eq c a b eq all imp a b el c a b el all imp and',
                'a b el c a b el all imp a b eq c a b eq all imp and'],
    }
    E_PARTS = {   # E's pieces: A = (-. v0 e. v2 -> v0 = v3), B = A.v1 P (P = a), C = v0 e. v1
        'ANT1': 'v0 v2 el neg v0 v3 eq imp v1 a all v0 v1 el imp imp',     # A -> (B -> C)
        'ANT2': 'v1 a all v0 v2 el neg v0 v3 eq imp v0 v1 el imp imp',     # B -> (A -> C)
        'ANT3': 'v0 v3 eq neg v0 v2 el imp v1 a all v0 v1 el imp imp',     # A' -> (B -> C)
        'ANT4': 'v1 a all v0 v3 eq neg v0 v2 el imp v0 v1 el imp imp',     # B -> (A' -> C)
        'CONS': 'v0 v1 el v1 a all imp',                                    # C -> B
    }   # A' = (-. v0 = v3 -> v0 e. v2), tautologically equivalent to A
    variants = VARIANTS     # name -> (perm, form); missing names: ((1, 2, 3), 0)
    breakers = ('pushwff().0',)

    def axiom(self, name):
        perm, form = self.variants.get(name, ((1, 2, 3), 0))
        text = self.FORMS[name][form]
        for k, v in self.E_PARTS.items():
            text = text.replace(k, v)
        par = {1: self.par1(), 2: self.par2(), 3: self.par3()}
        tok = {'a': par[perm[0]], 'b': par[perm[1]], 'c': par[perm[2]],
               'v0': self.v_0(), 'v1': self.v_1(), 'v2': self.v_2(), 'v3': self.v_3(),
               'eq': self.weq(), 'el': self.wel(), 'imp': self.wim(), 'neg': self.wn(),
               'all': self.wal(), 'ex': self.wex(), 'and': self.wa()}
        return [tok[t] for t in text.split()]

    def candidates(self):
        par1 = self.par1(); par3 = self.par3(); wim = self.wim(); wal = self.wal()
        select = self.select()
        c = {name: self.axiom(name) + [select] for name in self.FORMS if name != 'B6a'}
        # a key 'X+Y' in the order is one candidate X /\ Y (X, Y not B1..B3, not B6a): it gives
        # the same theorems as X and Y separately
        for key in self.order:
            if '+' in key:
                parts = key.split('+')
                assert all(p in self.FORMS and p not in ('B1', 'B2', 'B3', 'B6a') for p in parts)
                toks = self.axiom(parts[0])
                for p in parts[1:]:
                    toks = toks + self.axiom(p) + [self.wa()]
                c[key] = toks + [select]
        ZT = self.zero(self.topwff)
        tail = [
            # B6a; then keep it only if p3 != p2 and p3 != p1 (destroys p2, p3; keeps p1)
            *self.axiom('B6a'),
            *(self.b6a_check3() if self.shared_eq else
              self.b6a_check2(ZT) if self.b6a2 else self.b6a_check1(ZT)),
            select]
        if self.cascade:
            # GEN and DET are only computed when kept: each is one test of axiomcode.  GEN pops
            # the minor premise (as below), DET the major one; drop() discards the selection.
            tail += [
                [self.axiomcode.decnz, [self.pop(self.param3), par1, par3, wal, self.drop()]],
                [self.axiomcode.decnz, [self.pop(self.param2), par3, par1, wim,
                    self.while_decnz(self.topwff, self.scratch2.inc),
                    self.if_eq(self.param2, self.scratch2, self.eqbody()),
                    self.drop()]]]
            return c, tail
        tail += [
            # GEN (param3 is 0 here)
            self.ifsel(self.pop(self.param3)),
            par1, par3, wal, select]
        if self.shared_eq:
            # DET (param2 is 0 here): GEN has popped the minor premise q into param3 when DET is
            # kept; pop the major premise into param2 and derive p1 if it is q -> p1
            tail += [
                self.ifsel(self.pop(self.param2)),
                par3, par1, wim,
                self.while_decnz(self.topwff, self.scratch2.inc),
                self.if_eq(self.param2, self.scratch2, self.eqbody()),
                select]
        else:
            # DET (param2 is 0 here): from p3 and p3 -> p1 derive p1
            tail += [
                self.ifsel([self.zero(self.param3), self.pop(self.param3), self.pop(self.param2)]),
                par3, par1, wim,
                self.if_eq(self.topwff, self.param2, self.while_decnz(self.param1, self.topwff.inc)),
                select]
        return c, tail

    vchain = 'half'        # how v_1 .. v_4 (push, then topwff := k) are built
    @subroutine
    def inc2(self):
        return [self.topwff.inc, self.topwff.inc]

    @subroutine
    def v_1(self):
        return [self.pushwff(), self.topwff.inc]

    @subroutine
    def v_2(self):
        if self.vchain == 'nested':
            return [self.v_1(), self.topwff.inc]
        if self.vchain == 'flat':
            return [self.pushwff(), self.topwff.inc, self.topwff.inc]
        return [self.pushwff(), self.inc2()]

    @subroutine
    def v_3(self):
        if self.vchain == 'nested':
            return [self.v_2(), self.topwff.inc]
        if self.vchain == 'flat':
            return [self.pushwff(), self.topwff.inc, self.topwff.inc, self.topwff.inc]
        return [self.v_1(), self.inc2()]

    @subroutine
    def v_4(self):
        if self.vchain == 'nested':
            return [self.v_3(), self.topwff.inc]
        if self.vchain == 'flat':
            return [self.pushwff(), self.topwff.inc, self.topwff.inc, self.topwff.inc, self.topwff.inc]
        return [self.v_2(), self.inc2()]

    # shallow: pair, unpair and if_eq re-nested so that no continue erases more than two PC
    # bits and no break skips more than one level (6.continue.2, .3 and 6.break.2 disappear)
    shallow = True

    @subroutine
    def pair(self, out, in1, in2):
        if not self.shallow:
            return super().pair(out, in1, in2)
        # out += T(in1 + in2) + in1; in1 = in2 = 0
        w1 = self.while_decnz(in1, [in2.inc, out.inc])
        return [w1, self.label("loop", [in2.decnz, [
            [out.inc, self.while_decnz(in2, in1.inc), w1], "continue_loop"]])]

    @subroutine
    def unpair(self, out1, out2, in1):
        if not self.shallow:
            return super().unpair(out1, out2, in1)
        # in1 = pair(out1, out2) (out1, out2 zero): each unit of in1 moves one step along a diagonal
        return [self.label("loop", [in1.decnz, [
            [out1.inc, self.label("z", [[out2.decnz, "break_z"], self.while_decnz(out1, out2.inc)])],
            "continue_loop"]])]

    @subroutine
    def if_eq(self, in1, in2, body):
        if not self.shallow:
            return super().if_eq(in1, in2, body)
        # if in1 == in2: body.  Zeroes in1 and in2.
        return [self.label("fn", [
            self.label("loop", [in1.decnz, [[in2.decnz, "continue_loop"],
                                            [self.while_decnz(in1, ()), "break_fn"]]]),
            [[in2.decnz, [self.while_decnz(in2, ()), "break_fn"]], body]])]

    @subroutine
    def drop(self):
        """Discard the current selection (on the stack under the candidate in topwff)."""
        return [self.un(self.wffstack),
                self.while_decnz(self.scratch2, self.wffstack.inc),
                self.zero(self.scratch1)]

    @subroutine
    def eqbody(self):
        """The one if_eq body: topwff := param1 (B6a calls it with param1 = 0)."""
        return [self.zero(self.topwff), self.while_decnz(self.param1, self.topwff.inc)]

    def b6a_check3(self):
        # p1 parked in param3 so that eqbody zeroes topwff
        return [
            self.while_decnz(self.param3, [self.scratch1.inc, self.scratch2.inc]),   # s1 = s2 = p3
            self.while_decnz(self.param1, self.param3.inc),                         # param3 = p1
            self.if_eq(self.param2, self.scratch2, self.eqbody()),                  # p2 vs p3
            self.while_decnz(self.scratch1, self.param2.inc),                       # param2 = p3
            self.while_decnz(self.param3, [self.scratch1.inc, self.scratch2.inc]),   # s1 = s2 = p1
            self.if_eq(self.param2, self.scratch2, self.eqbody()),                  # p3 vs p1
            self.while_decnz(self.scratch1, self.param1.inc)]                       # p1 restored

    @subroutine
    def main(self):
        c, tail = self.candidates()
        body = [x for k in self.order for x in c[k]]
        if self.reload2:
            # copy nextproof through scratch1/scratch2 (loops that exist anyway)
            reload = [self.while_decnz(self.nextproof, [self.scratch1.inc, self.scratch2.inc]),
                      self.while_decnz(self.scratch1, self.nextproof.inc),
                      self.while_decnz(self.scratch2, self.prooflist.inc),
                      self.nextproof.inc]
        else:
            reload = [self.while_decnz(self.nextproof, [self.scratch1.inc, self.prooflist.inc]),
                      self.while_decnz(self.scratch1, self.nextproof.inc),
                      self.nextproof.inc]
        return [
            self.if_not_decnz(self.prooflist, reload),
            self.zero(self.axiomcode),
            self.zero(self.param1),
            self.zero(self.param3),
            *self.decode(self.axiomcode),
            *self.decode(self.param1),
            *self.decode(self.param2),
            *self.decode(self.param3),
            self.v_0(),
            *body, *tail,
            # halt iff the kept wff is 1 = v0 e. v0
            [self.topwff.decnz, self.label("if", [[self.topwff.decnz,
                [[self.topwff.inc, self.topwff.inc], "break_if"]], "halt"])],
        ]


def build(order=None, **switches):
    attrs = dict(switches)
    if order:
        attrs['order'] = order if isinstance(order, list) else order.split(',')
    b = type('PAv', (PA,), attrs)()
    b.build_machine()
    return b


if __name__ == '__main__':
    b = build()
    print(b.state_count(), 'states')
