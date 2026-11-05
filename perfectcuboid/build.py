"""Generator for a 2-symbol Turing machine that halts iff a perfect cuboid exists:
positive a, b, c with a^2+b^2, a^2+c^2, b^2+c^2 and a^2+b^2+c^2 all perfect squares.

Tape (blocks of 1s separated by '00'; a hole is a single 0 inside a block):

    A 00 B 00 C 00 Z  G  S

* A, B, C: real blocks of L >= 4 cells, standing for v(L) = floor(L/2) - 1.
* Z = '111': a block worth 0 that closes the queue A B C Z.
* G: eight cells, the window counter W in {0, 1, 2}: '00000000', '00001100' (W = 1) or
  '00110000' (W = 2) (a marker '11' that the parsers cross like a block).
* S: a leading 1, the cycle cells 1 .. 2k+1, a terminator 1. Its hole p counts
  N = k^2 + (p - 1); N is a square iff p = 1 (home). Fresh: '101'.
Processing a block X of L cells: h on X's last cell (home), m on L-3, the region m+2 .. L-1
(sizes 1, 3, ..., 2v-1 as m moves two cells left at a time). One unit = advance h
cyclically in the region (a completed cycle moves m), then advance S. When m cannot move
the block is done: X gave v^2 units.
After a block, the next block Y is set up (h, m; for Z only h) and S is checked: not a
square -> abort. A square: W ticks; when it wraps, S is reset; then Y is processed. The
blocks run cyclically, so the windows between resets are [A B C] [Z A B] [C Z A] [B C Z]:
the checks that can fail test a^2+b^2, a^2+b^2+c^2, c^2+a^2 and b^2+c^2. After Z, with
W = 2 (the fourth window passed): halt; otherwise home to A.
Abort: S's hole home (the next tuple's first check passes and resets S), W := 2, a scan
home filling Y's holes, then NEXCOM on (A, B, C) (compositions of every total, parts at
least 4 cells, A with the free end on the left; blocks merged and cut at fixed offsets).
Start: S's 101; the abort routine writes G, finds no queue, and a chain writes Z and
(4, 4, 4).
"""
import sys
ST = {}
ORDER = []
def S(name, t0, t1):
    assert name not in ST, name
    ST[name] = [t0, t1]; ORDER.append(name)
def T(w, d, n): return (w, d, n)

def parser_right(prefix, found):
    S(prefix+'1', T(0,'R',prefix+'2'), T(1,'R',prefix+'1'))
    S(prefix+'2', T(0,'R',prefix+'1'), found)
def parser_left(prefix, found):
    S(prefix+'1', T(0,'L',prefix+'2'), T(1,'L',prefix+'1'))
    S(prefix+'2', T(0,'L',prefix+'1'), found)

def seed():
    # S's leading 1; the abort routine writes the rest (S, W, Z) and, finding no queue,
    # NEXCOM's cut chains write the first tuple (4, 4, 4)
    S('seed0', T(1,'R','seed1'), None)
    S('seed1', T(0,'R','seed2'), None)
    S('seed2', T(1,'L','seed3'), None)
    S('seed3', T(0,'L','ab9'), None)

def process():
    parser_left('PL', T(1,'R','hA'))             # from S to h (lands at h-1)
    S('hA', T(1,'R','hB'), None)                 # fill h
    S('hB', T(0,'L','hW'), T(0,'R','hC'))        # 0: h was home: wrap to the region start
    S('hC', T(0,'L','hG1'), T(1,'R','PS1'))      # 0: the new h is home: the cycle is complete
    S('hW', T(0,'L','hX'), T(1,'L','hW'))        # scan left to m (or the separator)
    S('hX', T(0,'R','d1'), T(1,'R','hY'))        # 0: no m: the block is done
    S('hY', T(0,'R','hW2'), None)
    S('hW2', None, T(1,'R','hW3'))               # the spacer
    S('hW3', None, T(0,'R','hC'))                # h on the region's first cell
    S('hG1', T(0,'L','hG2'), None)
    S('hG2', T(1,'L','hG3'), T(1,'L','hG2'))     # fill m
    S('hG3', None, T(1,'L','hG4'))
    S('hG4', T(0,'R','hR'), T(1,'L','hG5'))      # 0: m was at 1: last region done
    S('hG5', T(0,'R','hR'), T(1,'R','hG6'))      # 0: m was at 2: last region done
    S('hG6', None, T(0,'R','hR'))                # m two cells left
    S('hR', T(0,'R','PS1'), T(1,'R','hR'))       # to h, then to S
    parser_right('PS', T(1,'R','s1'))
    S('s1', T(1,'R','s4'), T(1,'L','s2'))        # 0: p+1 is the terminator
    S('s2', None, T(0,'L','s3'))
    S('s3', T(1,'L','PL1'), None)
    S('s4', T(1,'L','s5'), None)
    S('s5', T(1,'L','s6'), T(1,'L','s5'))
    S('s6', T(0,'R','s7'), T(1,'L','s6'))
    S('s7', None, T(1,'R','s8'))
    S('s8', None, T(0,'L','PL1'))

def check(halt_state):
    # after the next block Y is set up: to S's hole, check the sum of the blocks so far
    parser_right('PK', T(1,'L','k1'))
    S('k1', T(0,'L','k2'), None)
    S('k2', None, T(1,'L','k3'))
    S('k3', T(0,'L','ta'), T(1,'R','ab1'))       # 0: a square: tick W
    # W tick, read from S's side: cells -3, -4 (W = 1), -5, -6 (W = 2)
    S('ta', T(0,'L','tb'), None)
    S('tb', T(0,'L','td'), T(0,'L','tc1'))       # 1: W = 1 -> 2
    S('tc1', None, T(0,'L','tc2'))
    S('tc2', T(1,'L','tc3'), None)
    S('tc3', T(1,'L','PL1'), None)
    S('td', T(0,'L','te'), None)
    S('te', T(0,'R','tf'), T(0,'L','tw'))        # 0: W = 0 -> 1; 1: W = 2 -> 0, reset S
    S('tf', T(1,'R','tg'), None)
    S('tg', T(1,'L','PL1'), None)
    S('tw', None, T(0,'R','PR2'))
    parser_right('PR', T(1,'R','r1'))            # S's hole is home: S := 101
    S('r1', T(0,'L','r2'), T(0,'R','r1'))
    S('r2', T(0,'L','r2'), T(1,'L','r3'))
    S('r3', T(0,'L','PL1'), None)                # back to Y's h: process Y
    # not a square: S's hole home, W := 2, Z and its separator rewritten, then a scan to the left
    # end that fills any hole (Y's h and m), then NEXCOM
    # S's hole moves home (the next tuple's first check resets S), then G, Z, separator
    S('ab1', None, T(1,'R','ab2'))               # p-1
    S('ab2', T(1,'L','ab3'), None)               # fill p
    S('ab3', T(0,'R','ab4'), T(1,'L','ab3'))
    S('ab4', None, T(1,'R','ab5'))               # leading 1
    S('ab5', None, T(0,'L','ab9'))               # home
    S('ab9', None, T(1,'L','ab10'))
    # cells -1 .. -8: 0 0 0 0 1 1 0 0 (G with W = 2)
    pat = '00001100'
    for i, ch in enumerate(pat):
        nx = f'ab{11+i}' if i + 1 < len(pat) else 'q1'
        w = int(ch)
        both = i in (2, 3, 4, 5)
        S(f'ab{10+i}', T(w,'L',nx), T(w,'L',nx) if both else None)
    # to the left end, filling single holes (a run of three 0s ends in a hole)
    S('q1', T(0,'L','q2'), T(1,'L','q1'))
    S('q2', T(0,'L','q4'), T(1,'R','q3'))        # 1: the 0 just passed was a hole
    S('q3', T(1,'L','q1'), None)
    S('q4', T(0,'L','q5'), T(1,'L','q1'))
    S('q5', T(0,'R','q6'), T(1,'R','q3'))        # 0: four 0s: the left end
    S('q6', T(0,'R','na4'), None)
    S('na4', T(0,'R','na5'), None)
    S('na5', T(0,'R','ea0'), None)

def nextblock(halt_state):
    # X done (head on X's cell -2): to the next block Y and set it up
    S('d1', T(0,'R','d2'), None)
    S('d2', T(0,'R','n4'), T(1,'R','d2'))
    S('n4', T(0,'R','n5'), None)
    S('n5', T(0,'L','wa'), T(1,'R','n6'))        # 0: end of the queue (W = 0 or 1): wrap
    S('n6', None, T(1,'R','n7'))
    S('n7', T(0,'L',halt_state), T(1,'R','n8'))  # 0: W's marker on G's cells 3, 4: W = 2: HALT
    S('n8', T(0,'L','nz'), T(1,'R','n9'))        # 0: Z
    S('nz', None, T(0,'R','PK1'))                # Z: only h
    S('n9', T(0,'L','i1'), T(1,'R','n9'))
    S('i1', None, T(0,'L','i2'))                 # h
    S('i2', None, T(1,'L','i3'))
    S('i3', None, T(0,'R','i4'))                 # m
    S('i4', None, T(1,'R','i5'))
    S('i5', T(0,'R','PK1'), None)
    # to the leftmost block
    S('wa', T(0,'L','wb'), T(1,'L','wa'))
    S('wb', T(0,'L','wc'), None)
    S('wc', T(0,'R','wd'), T(1,'L','wa'))
    S('wd', T(0,'R','we'), None)
    S('we', T(0,'R','n5'), None)

def nexcom():
    # entry at A's cell 0 (ea0 reads it). Lengths x, y, z of A, B, C, minimum 4.
    S('ea0', T(0,'L','zc1'), T(1,'R','ea1'))     # 0: no queue yet: write Z and (4, 4, 4)
    pat = '11100' + '111100' + '111100' + '1111'
    for i, ch in enumerate(pat):
        S(f'zc{i+1}', T(int(ch),'L',f'zc{i+2}' if i + 1 < len(pat) else 'wa'), None)
    for i in range(1, 4):
        S(f'ea{i}', None, T(1,'R',f'ea{i+1}'))
    S('ea4', T(0,'R','eb0'), T(1,'R','ca1'))     # 0: x = 4
    # x > 4: (x-1, y+1, z)
    S('ca1', T(0,'L','ca2'), T(1,'R','ca1'))
    S('ca2', None, T(0,'R','ca3'))
    S('ca3', T(0,'R','ca4'), None)
    S('ca4', T(1,'L','wa'), None)
    S('eb0', T(0,'R','eb1'), None)
    for i in range(1, 5):
        S(f'eb{i}', None, T(1,'R',f'eb{i+1}'))
    S('eb5', T(1,'R','cc1'), T(1,'R','cb1'))     # 0: y = 4
    # x = 4, y > 4: (y-1, 4, z+1): B gives a cell to C, A and B merge, B is cut again
    S('cb1', T(0,'L','cb2'), T(1,'R','cb1'))
    S('cb2', None, T(0,'R','cb3'))
    S('cb3', T(0,'R','cb4'), None)
    S('cb4', T(1,'L','cb5'), None)
    S('cb5', T(0,'L','cb6'), None)
    S('cb6', T(0,'L','cb7'), None)
    S('cb7', T(1,'L','cb8'), T(1,'L','cb7'))
    S('cb8', T(1,'R','cb9'), None)
    S('cb9', T(0,'L','k1c'), T(1,'R','cb9'))
    # cut B: from B's right separator (b), cells b-1 .. b-4 are B, b-5, b-6 the separator,
    # then over A's last four cells (on a blank tape these write the block)
    for i, (w, nx) in enumerate([(1,'k2c'), (1,'k3c'), (1,'k4c'), (1,'k5c'), (0,'k6c'), (0,'wa')]):
        S(f'k{i+1}c', None, T(w,'L',nx))
    # x = y = 4: (z+1, 4, 4): merge all, one more cell on the left, cut C and B again
    S('cc1', T(1,'L','cc2'), None)               # (eb5 has filled B's right separator)
    S('cc2', T(1,'L','cc3'), T(1,'L','cc2'))
    S('cc3', T(1,'L','cc4'), None)
    S('cc4', T(1,'R','cc5'), T(1,'L','cc4'))
    S('cc5', T(0,'L','j1c'), T(1,'R','cc5'))
    for i, (w, nx) in enumerate([(1,'j2c'), (1,'j3c'), (1,'j4c'), (1,'j5c'), (0,'j6c'), (0,'k1c')]):
        S(f'j{i+1}c', None, T(w,'L',nx))

def build(halt_state='halt'):
    ST.clear(); ORDER.clear()
    seed(); process(); check(halt_state); nextblock(halt_state); nexcom()
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    lines = ['; Halts iff a perfect cuboid exists.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'perfectcuboid.txt', 'w').write(out)
    print(len(ORDER), 'states')
