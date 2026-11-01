"""The k215P side: per-state lemmas  kzD<i> s c -> kzGood s c  and  kzSimAll: kzRel s c -> kzGood s c.

Writes kz_simh.mm1 (numeral helpers, register get/set), kz_s<NNN>.mm1 (per state, chunked) and
kz_simall.mm1.  usage: gen_glue.py D [chunk]"""
import os, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..'))
from gen_sim import Sim, cells, Rep, FileRef, Cfg, Push, ZERO, num, nd
from gen_rel import pnum, tree
from program import P


def ne(a, b):
    """proof of a != b for small numerals"""
    if a > 0 and b == 0:
        return 'peano1'
    if a == 0 and b > 0:
        return '(ax_mp necom peano1)'
    return f'(mpbir (noteq peano2) {ne(a - 1, b - 1)})'


def helpers():
    out = ['import "kz_glue.mm1";']
    for f in sorted(os.listdir(os.path.join(HERE, 'k215-pa/pa-mm0'))):
        if f.startswith('k215_literal_runtime_lookups_norm') and f.endswith('.mm1'):
            out.append(f'import "k215-pa/pa-mm0/{f}";')
    out.append('')
    for a in range(10):
        for b in range(10):
            if a != b:
                out.append(f"theorem kzNe_{a}_{b}: $ {a} != {b} $ = '{ne(a, b)};")
    for a in range(9):
        pf = 'eqid' if a == 8 else '(ifpos eqid)'
        for i in range(min(a, 8) - 1, -1, -1):
            pf = f'(eqtr (ifneg kzNe_{a}_{i}) {pf})'
        out.append(f"theorem kzGet_{a} (v: nat): $ k215PGet {a} v = k215PR{a} v $ = '{pf};")
    for a in range(9):
        for o in range(9):
            if o == a:
                out.append(f"theorem kzRS_{a}_{o} (x v: nat): $ k215PR{o} (k215PSet {a} x v) = x $ = "
                           f"'(eqtr k215PR{o}_vector (ifpos eqid));")
            else:
                out.append(f"theorem kzRS_{a}_{o} (x v: nat): $ k215PR{o} (k215PSet {a} x v) = k215PR{o} v $ = "
                           f"'(eqtr k215PR{o}_vector (ifneg kzNe_{a}_{o}));")
    return out


class Glue:
    def __init__(self, D):
        self.S = Sim(D)
        self.order = self.S.m.reg_order
        E = json.load(open(os.path.join(HERE, 'entries.json')))
        self.states = [(pc, tuple(d)) for pc, d in json.load(open(os.path.join(HERE, 'states.json')))]
        self.index = {st: i for i, st in enumerate(self.states)}
        self.lem = {}
        for e in E['entries']:
            if e['tag'] == 'main':
                self.lem[(e['pc'], tuple(e['digits']), e['branch'])] = e
        self.look = json.load(open(os.path.join(HERE, 'lookups.json')))
        self.n = len(self.states)
        self.root = self.S.root

    def path(self, i):
        """L/R path of leaf i in gen_rel.tree"""
        lo, hi, p = 0, self.n, []
        while hi - lo > 1:
            h = (hi - lo) // 2
            if i < lo + h:
                p.append('L')
                hi = lo + h
            else:
                p.append('R')
                lo = lo + h
        return p

    def intro(self, i, pf, ded=False):
        """from pf: kzD<i> s c (or G -> ..., ded) to kzRel s c"""
        for b in reversed(self.path(i)):
            if ded:
                pf = f'(syl {"orl" if b == "L" else "orr"} {pf})'
            else:
                pf = f'(ax_mp {"orl" if b == "L" else "orr"} {pf})'
        return pf

    def conf_cong(self, digits, eqs, ded=False, virtual=False):
        """kzState root (kzPush 0 0) (cells (kzRep 1 g (kzF9 ..)))  =  same with eqs on the 9 args
        (virtual: kzState scan 0 (kzPush 0 (cells ..)))"""
        d = 'd' if ded else ''
        eqs = list(eqs) + [('eqidd' if ded else 'eqid')] * nd()
        pf = f'(kzF{9 + nd()}eq{d} {" ".join(eqs)})'
        pf = f'(kzRepeq3{d} {pf})'
        for _ in digits:
            pf = f'(kzPusheq2{d} {pf})'
        if virtual:
            pf = f'(kzPusheq2{d} {pf})'
        return f'(kzStateeq3{d} {pf})'

    def theorem(self, i):
        pc, digits = self.states[i]
        e = P[pc]
        LK = self.look[str(pc)][0]
        N = pnum(pc)
        tag, a = e['tag'], e['arg']
        virt = self.S.m.virtual_pcs
        h5 = f'(mpbir (lteq1 kzState_Q) kzLtH_{self.S.M.q("scan") if pc in virt else self.root})'
        stat = f'(eqtrd (kzStat {LK}) (a1i k215PETag_entry))'
        not4 = f'(mtbird (eqeq1d {stat}) (a1i kzNe_{tag}_4))' if tag != 4 else None
        hdr = f'theorem kzS{i} (s c: nat): $ kzD{i} s c -> kzGood s c $ =\n'
        if tag == 4:
            le = self.lem[(pc, digits, 'halt')]
            return hdr + f"'(kzG_halt {stat} {le['name']} kzState_Q {h5});"
        if tag in (0, 2, 3):
            le = self.lem[(pc, digits, 'inc' if tag == 0 else 'ctl')]
            j = self.index[(le['next_pc'], tuple(le['next_digits']))]
            if tag == 0:
                step = f'(kzStepAt (k215PAtCI {LK}))'
                eqs = []
                for o in self.order:
                    if o == a:
                        eqs.append(f'(eqtr (k215PR{o}eq k215PRegs_state) (eqtr kzRS_{a}_{o} (suceq kzGet_{a})))')
                    else:
                        eqs.append(f'(eqtr (k215PR{o}eq k215PRegs_state) kzRS_{a}_{o})')
            else:
                step = f'(kzStepAt ({"k215PAtCB" if tag == 2 else "k215PAtCC"} {LK}))'
                eqs = [f'(k215PR{o}eq k215PRegs_state)' for o in self.order]
            nd = tuple(le['next_digits'])
            leaf = f'(iani k215PPC_state (eqcom {self.conf_cong(nd, eqs, False, le["next_pc"] in virt)}))'
            return hdr + f"'(kzG_det {not4} {step} {le['name']} {self.intro(j, leaf)} {h5});"
        # decnz
        lz, lp = self.lem[(pc, digits, 'dec0')], self.lem[(pc, digits, 'decp')]
        jz = self.index[(lz['next_pc'], tuple(lz['next_digits']))]
        jp = self.index[(lp['next_pc'], tuple(lp['next_digits']))]
        pos = self.order.index(a)
        AT = f'(kzStepAt (k215PAtCD {LK}))'
        h2z = f'(exp (eqtrd (anwl {AT}) (syl ifpos (sylibr (eqeq1 kzGet_{a}) anr))))'
        h2p = f'(exp (eqtrd (anwl {AT}) (syl ifneg (sylibr (noteq (eqeq1 kzGet_{a})) anr))))'
        # the start configuration with r = 0 / r = suc (r - 1)
        cz = ['eqidd'] * 9
        cz[pos] = 'id'
        cp = ['eqidd'] * 9
        cp[pos] = '(eqcomd sub1can)'
        h3z = f"(mpbird (kzReachPeqd {self.conf_cong(digits, cz, True)} eqidd) (a1i {lz['name']}))"
        h3p = f"(mpbird (kzReachPeqd {self.conf_cong(digits, cp, True)} eqidd) (a1i {lp['name']}))"
        # targets
        ez = []
        for o in self.order:
            if o == a:
                ez.append(f'(eqtrd (a1i (k215PR{o}eq k215PRegs_state)) id)')
            else:
                ez.append(f'(a1i (k215PR{o}eq k215PRegs_state))')
        ndz = tuple(lz['next_digits'])
        leafz = f'(iand (a1i k215PPC_state) (eqcomd {self.conf_cong(ndz, ez, True, lz["next_pc"] in virt)}))'
        h4z = self.intro(jz, leafz, ded=True)
        ep = []
        for o in self.order:
            if o == a:
                ep.append(f'(eqtr (k215PR{o}eq k215PRegs_state) (eqtr kzRS_{a}_{o} (subeq1 kzGet_{a})))')
            else:
                ep.append(f'(eqtr (k215PR{o}eq k215PRegs_state) kzRS_{a}_{o})')
        ndp = tuple(lp['next_digits'])
        leafp = f'(iani k215PPC_state (eqcom {self.conf_cong(ndp, ep, False, lp["next_pc"] in virt)}))'
        h4p = f'(a1i {self.intro(jp, leafp)})'
        return hdr + f"'(kzG_dec {not4} {h2z} {h2p} {h3z} {h3p} {h4z} {h4p} {h5});"

    def simall(self):
        def go(lo, hi):
            if hi - lo == 1:
                return f'kzS{lo}'
            h = (hi - lo) // 2
            return f'(ax_mp (ax_mp eor {go(lo, lo + h)}) {go(lo + h, hi)})'
        return f"theorem kzSimAll (s c: nat): $ kzRel s c -> kzGood s c $ =\n'{go(0, self.n)};"


def main(D, chunk):
    open(os.path.join(HERE, 'kz_simh.mm1'), 'w').write('\n'.join(helpers()) + '\n')
    G = Glue(D)
    E = json.load(open(os.path.join(HERE, 'entries.json')))
    pchunks = [f'kz_p{c:03d}.mm1' for c in range(E['nchunks'])]
    nchunks = (G.n + chunk - 1) // chunk
    for c in range(nchunks):
        lines = ['import "kz_simh.mm1";'] + [f'import "{p}";' for p in pchunks] + ['']
        lines += [G.theorem(i) for i in range(c * chunk, min(G.n, (c + 1) * chunk))]
        open(os.path.join(HERE, f'kz_s{c:03d}.mm1'), 'w').write('\n'.join(lines) + '\n')
    lines = [f'import "kz_s{c:03d}.mm1";' for c in range(nchunks)] + ['', G.simall()]
    open(os.path.join(HERE, 'kz_simall.mm1'), 'w').write('\n'.join(lines) + '\n')
    print(nchunks, 'chunks of per-state lemmas', file=sys.stderr)


if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]) if len(sys.argv) > 2 else 500)
