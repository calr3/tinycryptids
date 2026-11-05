"""Generator for a 2-symbol beeping Turing machine for amicable numbers (see README.md)."""
import sys
ST = {}; ORDER = []
def S(name, t0, t1):
    assert name not in ST, name
    ST[name] = [t0, t1]; ORDER.append(name)
def T(w, d, n): return (w, d, n)
def parser_right(p, found):
    S(p+'1', T(0,'R',p+'2'), T(1,'R',p+'1')); S(p+'2', T(0,'R',p+'1'), found)
def parser_left(p, found):
    S(p+'1', T(0,'L',p+'2'), T(1,'L',p+'1')); S(p+'2', T(0,'L',p+'1'), found)

SEED = ''
def seed():
    if not SEED: return
    for i, ch in enumerate(SEED):
        S(f'seed{i}', T(int(ch), 'R', f'seed{i+1}' if i + 1 < len(SEED) else 'k0'), None)

def modwalk():   # ../oddperfect verbatim
    S('ma1', T(1,'R','ma2'), None)
    S('ma2', T(0,'L','mw1'), T(0,'R','PR1'))
    S('mw1', T(0,'R','mw2'), T(1,'L','mw1'))
    S('mw2', None, T(1,'R','mw3'))
    S('mw3', None, T(0,'R','PR1'))
    parser_right('PR', T(1,'L','ra1'))
    S('ra1', T(1,'R','ra2'), None)
    S('ra2', None, T(1,'R','ra3'))
    S('ra3', T(0,'L','e1'), T(1,'L','ra4'))
    S('ra4', None, T(0,'L','PM1'))
    parser_left('PM', T(1,'R','ma1'))
    S('e1', T(0,'L','e2'), T(1,'L','e1'))
    S('e2', T(0,'L','e3'), None)
    S('e3', T(1,'L','a2'), T(1,'L','f1'))

def shift():
    S('f1', T(1,'R','f2'), T(1,'L','f1'))
    S('f2', T(0,'R','f3'), T(1,'R','f2'))
    S('f3', T(0,'R','f4'), T(0,'L','CE1'))      # 1: the marker: copy for the next round done
    S('f4', T(0,'L','H0'), T(0,'R','f5'))       # 0: subtraction copy done
    S('f5', None, T(0,'R','f6'))
    S('f6', T(0,'R','PE1'), T(1,'L','PM2'))     # 0: pass over

def add():
    # D hole one cell down; each step grows the accumulator (3rd zero left) by one cell
    S('a1', T(1,'L','a2'), None)
    S('a2', T(0,'R','f2'), T(0,'L','Z1'))
    S('Z1', T(0,'L','Z2'), T(1,'L','Z1'))
    S('Z2', T(0,'L','Z3'), None)
    S('Z3', T(1,'L','W'), T(1,'L','Z3'))
    S('W', T(0,'R','PA1'), T(0,'R','PA1'))
    parser_right('PA', T(1,'L','a1'))

def passend():
    # f6 read 0 at X+4: pass 1 has blank to the right, pass 2 has 00 N
    S('PE1', T(0,'R','PE2'), None)
    S('PE2', T(0,'L','G0'), T(1,'L','R1'))
    # pass 1: N stays 1^n (its zeros are blank); abundance check at P's hole
    S('G0', T(0,'L','G0'), T(1,'L','G1'))
    S('G1', T(0,'L','G2'), T(1,'L','G1'))
    S('G2', T(0,'L','G3'), None)
    S('G3', T(1,'L','G4'), T(1,'L','G3'))       # fill the hole
    S('G4', T(1,'L','g1'), T(1,'R','x1'))       # 0: grown: pass 2 on P'
    S('g1', T(1,'L','g2'), None)
    S('g2', T(1,'L','V4'), None)
    # pass 2: fill X, then the subtraction copy of N (n units)
    S('R1', T(0,'L','R2'), None)
    S('R2', T(0,'L','FL2'), None)
    S('FL2', T(1,'L','FL2'), T(1,'R','T1'))
    S('T1', T(0,'R','T2'), T(1,'R','T1'))
    S('T2', T(0,'R','T3'), None)
    S('T3', T(1,'L','a2'), T(1,'R','T3'))
    # subtraction check: back to the hole (N's extra cell erased on the way)
    S('H0', T(0,'L','H0'), T(0,'L','H1'))
    S('H1', T(0,'L','H2'), T(1,'L','H1'))
    S('H2', T(0,'L','H3'), None)
    S('H3', T(1,'L','H4'), T(1,'L','H3'))       # fill the hole
    S('H4', T(0,'R','x1'), T(1,'L','H5'))
    S('H5', T(0,'R','x1'), T(1,'R','x1'))       # 0: s(m) = n: THE BEEP

def cleanup():
    # N := 1^(n+4), marker 2 cells further, copy N (from a new cell) to the far left
    S('k0', T(1,'R','k1'), T(1,'R','k0'))
    S('k1', T(1,'R','k2'), None)
    S('k2', T(1,'R','k3'), None)
    S('k3', T(0,'R','k4'), None)
    S('k4', T(0,'R','k5'), None)
    S('k5', T(1,'L','k6'), None)
    S('k6', T(0,'L','k7'), None)
    S('k7', T(1,'L','a2'), None)
    # junk left of N is one block now (the checks filled its hole): erase it from the right
    S('x1', T(0,'L','er'), T(1,'R','x1'))
    S('er', T(0,'R','bk'), T(0,'L','er'))
    S('bk', T(0,'R','bk'), T(1,'R','k0'))
    # copy done (f3 on the marker): preload, CONV N, pass 1
    S('CE1', T(1,'L','V1'), None)                # N's last new cell
    S('V1', T(0,'L','V2'), T(1,'L','V1'))
    S('V2', T(0,'L','V3'), None)
    S('V3', None, T(0,'R','V4'))
    S('V4', T(0,'R','V4'), T(1,'R','C1'))
    S('C1', None, T(0,'R','C2'))
    S('C2', None, T(0,'L','f2'))

def build(beep='BEEP'):
    ST.clear(); ORDER.clear()
    seed(); cleanup(); modwalk(); shift(); add(); passend()
    refs = {t[2] for v in ST.values() for t in v if t}
    assert not refs - set(ST), refs - set(ST)
    lines = ['; amicable prototype', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    open(sys.argv[1] if len(sys.argv) > 1 else 'amicable.txt', 'w').write(build()); print(len(ORDER), 'states')
