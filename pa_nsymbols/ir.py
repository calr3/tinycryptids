"""The PA program of ../pa/program.py (the 309-state configuration) as a symbolic tree.

../pa/tmbuilder.py resolves `break_X` / `continue_X` into binary PC bit counts as the program
is built.  Here `label` keeps them symbolic instead: a labelled body becomes a sequence
("@LABEL#<id>", body), and its references become "_brk#<id>" / "_cnt#<id>".  Everything else
(subroutines, memoisation, the candidates, their order and forms) is program.py's.

prog() returns a Prog: nodes {i: Seq | Label}, leaves as strings:
  "3.R.inc", "3.R.decnz"   register operations;  "halt";  "_brk#L", "_cnt#L".
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'pa'))
import program


class Sym(program.PA):
    def __init__(self):
        super().__init__()
        self.nlabels = 0

    def label(self, name, seq, zeros=0, ones=0):
        brk, cnt = 'break_' + name, 'continue_' + name

        def unres(v):
            if isinstance(v, str):
                return v in (brk, cnt)
            if isinstance(v, int):
                return name in self.sequences[v].unresolved_labels
            return any(unres(x) for x in v)

        if not unres(seq):
            return seq
        lid = self.nlabels
        self.nlabels += 1

        def rename(v, old, nid):
            """an inner label's copy refers to itself by its new id"""
            if isinstance(v, str):
                return f'{v[:5]}{nid}' if v in (f'_brk#{old}', f'_cnt#{old}') else v
            if isinstance(v, int):
                return [rename(x, old, nid) for x in self.sequences[v].seq]
            return [rename(x, old, nid) for x in v]

        def bind(v):
            if not unres(v):
                return v
            if isinstance(v, str):
                return f'_brk#{lid}' if v == brk else f'_cnt#{lid}'
            if isinstance(v, int):
                s = self.sequences[v].seq
                if isinstance(s[0], str) and s[0].startswith('@LABEL#'):
                    # an inner label whose body refers to this one: a new copy of it
                    nid = self.nlabels
                    self.nlabels += 1
                    body = self.add_sequence(rename(bind(s[1]), int(s[0][7:]), nid))
                    return self.add_sequence((f'@LABEL#{nid}', body))
                return [bind(x) for x in s]
            return [bind(x) for x in v]

        body = self.add_sequence(bind(seq))
        return self.add_sequence((f'@LABEL#{lid}', body))


def build(**switches):
    """switches: program.PA attributes (order, variants, vchain, cascade, ...)"""
    b = type('S', (Sym,), dict(switches))()
    b.main()
    return b


class Prog:
    """nodes: id -> ('seq', [children]) | ('label', lid, child); root: id."""
    def __init__(self, b):
        self.b = b
        self.nodes = {}
        self.root = self._conv(b.find_seq('main().0'))

    def _conv(self, v):
        if isinstance(v, str):
            return v
        if v in self.nodes:
            return v
        s = self.b.sequences[v].seq
        if isinstance(s[0], str) and s[0].startswith('@LABEL#'):
            self.nodes[v] = None
            self.nodes[v] = ('label', int(s[0][7:]), self._conv(s[1]))
        else:
            self.nodes[v] = None
            self.nodes[v] = ('seq', [self._conv(x) for x in s])
        return v

    def name(self, i):
        return self.b.sequences[i].name


def prog(**switches):
    return Prog(build(**switches))


if __name__ == '__main__':
    p = prog()
    from collections import Counter
    seqs = [n for n in p.nodes.values() if n[0] == 'seq']
    labs = [n for n in p.nodes.values() if n[0] == 'label']
    print(len(seqs), 'sequences,', len(labs), 'labels')
    print('lengths', sorted(Counter(len(n[1]) for n in seqs).items()))
    leaves = Counter(c for n in seqs for c in n[1] if isinstance(c, str))
    print('leaf kinds', Counter(l.split('#')[0] if '#' in l else l.rsplit('.', 1)[-1] for l in leaves))
