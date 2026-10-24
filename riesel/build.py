"""Generator for a 2-symbol Turing machine that halts iff no odd k < 509203 is a
Riesel number: iff every odd k < 509203 has some n >= 1 with k*2^n - 1 prime.
(A Sigma_1 statement: the machine halts iff it is TRUE.)

The earlier 110-state design of ../sierpinski/ with k*2^n - 1 in place of k*2^n + 1:
For k = 5, 7, ..., 509201 in turn it tests P = k*2 - 1, k*4 - 1, ... by trial
division until one is prime; then it moves on to k + 2.  After the prime for
k = 509201 it halts.  (k = 1 and 3 are not run: 1*4 - 1 = 3, 3*2 - 1 = 5.)

Tape layout (blocks of 1s separated by '00'):
  C 00 K 00 D 00 R
  - C: a binary counter c, in five groups of four bits b3 b2 b1 b0 followed
    by a marker 1, most significant group first: the number of k still to come.
  - K: k + 7 cells while k is tested (no hole).
  - D (d+2 cells, hole at cell c+1) and R (r+2 cells, a hole at cell j during
    the mod walk) hold the trial divisor d and r = P - d.
Trial division (a mod walk and shift) starts at d = 3 (P is odd).
  composite: rebuild D := 3, R := the rest (P - 1 cells), hole at R[1];
             then the loop doubles R: P := 2P + 1.
  prime:     wipe D and R; the loop moves K and copies it to T; decrement C
             (halt if it was 0); T becomes a region (D := 3, hole at R[1]),
             and the loop doubles R: P = 2(k + 2) - 1.
The loop (s*): consume the block X left of the head from its right end; each
cell moves to the block X' on its right (the separator moves left) and one
more cell is appended to the block T after X'.  It stops at the first 0: the
R hole (X = R) or the C/K separator (X = K); t1 tells them apart.
  X = R: the gap and the X'/T separator are filled: R := 2|R| + 2 cells.
  X = K: the gap is filled: K gets 2 cells (k += 2); T has |K| cells.
The seed writes C = 254599 (0x3E287; its two leading 0 bits are left blank)
and K for the step to k = 5 (10 cells).
"""
import sys
ST = {}          # name -> [t0, t1]
ORDER = []
def S(name, t0, t1):
    assert name not in ST, name
    ST[name] = [t0, t1]; ORDER.append(name)
def T(w, d, n): return (w, d, n)

def parser_right(prefix, found):
    """Move right to the next hole. Lands at hole+1 (a 1) and performs
    `found` (a transition tuple) on that 1."""
    S(prefix+'1', T(0,'R',prefix+'2'), T(1,'R',prefix+'1'))
    S(prefix+'2', T(0,'R',prefix+'1'), found)
def parser_left(prefix, found):
    """Move left to the next hole. Lands at hole-1 (a 1), performs `found`."""
    S(prefix+'1', T(0,'L',prefix+'2'), T(1,'L',prefix+'1'))
    S(prefix+'2', T(0,'L',prefix+'1'), found)

C0 = 254599
def counter_cells(c):
    """C as a string: groups (msb first) of 4 bits, each followed by a marker 1"""
    assert 0 <= c < 1 << 20
    return ''.join(format((c >> (4 * g)) & 15, '04b') + '1' for g in (4, 3, 2, 1, 0))

def seed():
    # C (without its leading 0s), then K (10 cells, for k = 5) except its
    # last cell: that cell plays the loop's first erased cell (s1), then s4
    pat = counter_cells(C0).lstrip('0') + '00' + '1' * 9 + '0'
    for i, ch in enumerate(pat):
        S(f'seed{i}', T(int(ch),'R', f'seed{i+1}' if i+1 < len(pat) else 's4'), None)

def modwalk():
    # advance the D hole cyclically (head ends right of it), then the R hole
    S('ma1', T(1,'R','ma2'), None)
    S('ma2', None, T(1,'R','ma3'))
    S('ma3', T(0,'L','maw1'), T(1,'L','ma4'))     # 0: the hole was at the last cell
    S('ma4', None, T(0,'R','PR1'))
    S('maw1', T(0,'R','maw2'), T(1,'L','maw1'))
    S('maw2', None, T(1,'R','maw3'))
    S('maw3', None, T(0,'R','PR1'))
    parser_right('PR', T(1,'L','ra1'))
    S('ra1', T(1,'R','ra2'), None)
    S('ra2', None, T(1,'R','ra3'))
    S('ra3', T(0,'L','PK1'), T(1,'L','ra4'))      # 0: R exhausted (hole gone)
    S('ra4', None, T(0,'L','PM1'))
    parser_left('PM', T(1,'R','ma1'))
    # is the D hole at cell 1?
    parser_left('PK', T(1,'L','k1'))
    S('k1', T(0,'R','x1'), T(1,'R','k2'))         # 0: d | P: composite
    S('k2', None, T(1,'R','k3'))
    S('k3', T(1,'L','rs1'), None)                 # fill hole, reset it to cell 1
    S('rs1', T(0,'R','rs2'), T(1,'L','rs1'))
    S('rs2', None, T(1,'R','rs3'))
    S('rs3', None, T(0,'R','sh1'))
    # shift: d += 1, r -= 1
    S('sh1', T(1,'R','sh2'), T(1,'R','sh1'))
    S('sh2', T(0,'R','sh3'), None)
    S('sh3', None, T(0,'R','sh4'))
    S('sh4', None, T(1,'R','sh5'))
    S('sh5', None, T(1,'R','sh6'))
    S('sh6', T(0,'L','w1'), T(1,'L','sh7'))       # 0: r = 0: P is prime
    S('sh7', None, T(0,'L','PM1'))                # R hole at cell 1, mod walk

def rebuild():
    # composite: from left of D (hole at cell 1): D := 3 (cells 0..4),
    # separator at 5, 6, R := the rest, hole at R[1]; then the
    # loop on R
    S('x1', None, T(1,'R','x2'))
    S('x2', T(0,'R','c1'), None)
    S('c1', T(1,'R','c2'), T(1,'R','c1'))
    S('c2', T(1,'R','c3'), None)
    S('c3', T(0,'L','c4'), T(1,'R','c3'))
    S('c4', T(0,'R','c5'), T(1,'L','c4'))
    S('c5', None, T(1,'R','c6'))
    S('c6', None, T(1,'R','c6b'))
    S('c6b', None, T(1,'R','c7'))
    S('c7', None, T(0,'R','c8'))
    S('c8', None, T(0,'R','h0'))
    S('h0', None, T(1,'R','h1'))
    S('h1', None, T(0,'R','h3'))
    S('h3', T(0,'L','s1'), T(1,'R','h3'))

def wipe():
    # prime: erase R (2 cells) and D (with its hole), stop at K's last cell
    S('w1', T(0,'L','w2'), T(0,'L','w1'))
    S('w2', T(0,'L','w3'), None)
    S('w3', T(0,'L','w4'), T(0,'L','w3'))
    S('w4', T(0,'L','s1'), T(0,'L','w3'))

def loop():
    S('s1', T(0,'L','t1'), T(0,'R','s4'))         # 0: X used up
    S('s4', T(0,'R','s5'), None)
    S('s5', T(1,'R','s6'), None)                  # X' grows on the left
    S('s6', T(0,'R','s6b'), T(1,'R','s6'))
    S('s6b', T(0,'R','s6c'), None)
    S('s6c', T(1,'L','s7'), T(1,'R','s6c'))       # T grows on the right
    S('s7', T(0,'L','s7b'), T(1,'L','s7'))
    S('s7b', T(0,'L','s7c'), None)
    S('s7c', T(0,'L','s8'), T(1,'L','s7c'))
    S('s8', T(0,'L','s1'), None)
    S('t1', T(0,'L','Dm'), T(1,'R','a1'))         # 0: X was K; 1: X was R

def double_end():
    # X = R: fill the gap (cells 2, 3) and the X'/T separator
    S('a1', T(0,'R','a2'), None)
    S('a2', T(1,'R','a3'), None)
    S('a3', T(1,'R','a4'), None)
    S('a4', T(1,'R','a5'), T(1,'R','a4'))
    S('a5', T(1,'L','a6'), None)
    S('a6', T(0,'L','PM1'), T(1,'L','a6'))        # past the R hole, then to the D hole

def counter(halt_state):
    S('Dm', T(0,'R',halt_state), T(1,'L','D0'))   # 0: c was 0: HALT
    for i in range(4):
        S(f'D{i}', T(1,'L', f'D{i+1}' if i < 3 else 'Dm'), T(0,'R','ret1'))
    S('ret1', T(0,'R','ret2'), T(1,'R','ret1'))
    S('ret2', T(0,'R','b2'), None)

def newk():
    # X = K: fill the gap (cells 0, 1), cross X', make T a region: hole at T[1]
    S('b2', T(1,'R','b3'), None)
    S('b3', T(1,'R','b4'), None)
    S('b4', T(0,'R','b5'), T(1,'R','b4'))
    S('b5', T(0,'R','b6'), None)
    S('b6', None, T(1,'R','b7'))
    S('b7', None, T(0,'R','c5'))

def build(halt_state='halt', c0=254599):
    global C0
    C0 = c0
    ST.clear(); ORDER.clear()
    seed(); modwalk(); rebuild(); wipe(); loop(); double_end(); counter(halt_state); newk()
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    what = ('every odd k < 509203 has a prime k*2^n-1 (no Riesel number below 509203)' if c0 == 254599
            else f'every odd k <= {2 * c0 + 5} has a prime k*2^n-1 (test variant)')
    lines = [f'; Halts iff {what}.',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'riesel.txt', 'w').write(out)
    print(len(ORDER), 'states')
