"""Generator for a 2-symbol Turing machine that halts iff Legendre's
conjecture is FALSE, i.e. iff for some n >= 1 there is no prime p with
n^2 < p < (n+1)^2.

It is an incremental sieve.  At checkpoint m (m >= 1) the tape is

    M 00 P_k 00 ... 00 P_1 000 S 0 F

* M      : 1^(m+2) (a plain counter, no hole), at the left end.
* P_i    : one block per prime p <= m (newest first): a left guard 1,
           a region of p cells containing one hole (a single 0), and a
           right guard 1.  The hole sits at region index p-1-(m mod p),
           so it moves one cell LEFT per increment and wraps from index 0
           to index p-1 exactly when the new m is divisible by p.
* S      : the square counter, same shape with a region of 2n+1 cells
           (n = isqrt m), hole at index 2n-(m-n^2).  It wraps exactly
           when the new m is a square; the region then grows by 2.
* F      : one cell, two cells right of S: 1 iff some prime p has
           n^2 < p <= m.
* The separator in front of S is the only run of exactly three 0s.

One increment m -> m+1:
  1. HomeG: go to the left end (four 0s), write a 1 there (M += 1), and
     start the sweep on M in "prime" mode.
  2. Sweep right over every P block, moving its hole; a wrap means
     m+1 is divisible by that prime, and the sweep continues in
     "composite" mode.  The three 0s before S end the sweep.
  3. S: move its hole.
       composite: a wrap means m+1 = (n+1)^2.  Then if F = 0 there was no
                  prime in (n^2, (n+1)^2): HALT.  If F = 1 the F cell
                  becomes the new right guard (region += 2, F cleared).
       prime:     set F; go home and copy M to its left (old M becomes
                  the block of the new prime, hole at its last index).
"""
import sys
ST = {}
ORDER = []
def S(name, t0, t1):
    assert name not in ST, name
    ST[name] = [t0, t1]; ORDER.append(name)
def T(w, d, n): return (w, d, n)

def home(prefix, last_states, k):
    """Go left over runs of at most three 0s until a fourth 0 (the left end)."""
    S(prefix+'1', T(0,'L',prefix+'2'), T(1,'L',prefix+'1'))
    S(prefix+'2', T(0,'L',prefix+'3'), T(1,'L',prefix+'1'))
    S(prefix+'3', T(0,'L',prefix+'4'), T(1,'L',prefix+'1'))
    S(prefix+'4', k, T(1,'L',prefix+'1'))

def sweep(m, nxt_found_mode, end):
    """Parser for mode m ('p' prime so far, 'q' composite): crosses blocks
    and separators, finds holes, moves each hole one cell left."""
    S(m+'1', T(0,'R',m+'2'), T(1,'R',m+'1'))
    S(m+'2', T(0,'R',m+'3'), T(1,'L',m+'A'))      # 1: hole found (we are one past it)
    S(m+'3', T(0,'R',end), T(1,'R',m+'1'))        # third 0: end of the P zone
    S(m+'A', T(1,'L',m+'B'), None)                # fill the hole
    S(m+'B', None, T(1,'L',m+'C'))
    S(m+'C', T(0,'R','W2'), T(1,'R',m+'D'))       # 0: hole was at index 0 -> wrap
    S(m+'D', None, T(0,'R',m+'1'))                # new hole one cell left

def build(halt_state='halt', set_f=True):
    ST.clear(); ORDER.clear()
    # ---- seed: m = 1:  M=111, 000, S = 1 [1 1 0] 1, F = 0
    pat = '111' + '000' + '11101'
    for i, ch in enumerate(pat):
        last = i + 1 == len(pat)
        S(f'seed{i}', T(int(ch), 'L' if last else 'R', 'hg1' if last else f'seed{i+1}'), None)
    # ---- 1. home and grow M
    home('hg', None, T(0,'R','hg5'))
    S('hg5', T(0,'R','hg6'), None)
    S('hg6', T(0,'R','hg7'), None)
    S('hg7', T(1,'R','p1'), None)
    # ---- 2. sweep
    sweep('p', None, 'sp1')
    sweep('q', None, 'sq1')
    S('W2', T(0,'L','W3'), T(1,'R','W2'))         # wrap: to the right end of the block
    S('W3', None, T(1,'L','W4'))                  # right guard
    S('W4', None, T(0,'R','q1'))                  # hole at the last index; composite
    # ---- 3a. S after a prime-mode sweep (no wrap possible): move hole, set F
    S('sp1', T(0,'R','sp2'), T(1,'R','sp1'))
    S('sp2', None, T(1,'L','sA'))
    S('sA', T(1,'L','sB'), None)
    S('sB', None, T(1,'L','sC'))
    S('sC', None, T(1,'R','sD'))
    S('sD', None, T(0,'R','sE'))
    S('sE', T(0,'R','sG'), T(1,'R','sE'))
    S('sG', T(1 if set_f else 0,'L','hc1'), T(1,'L','hc1'))   # F := 1
    # ---- 3b. S after a composite-mode sweep
    S('sq1', T(0,'R','sq2'), T(1,'R','sq1'))
    S('sq2', None, T(1,'L','tA'))
    S('tA', T(1,'L','tB'), None)
    S('tB', None, T(1,'L','tC'))
    S('tC', T(0,'R','tW'), T(1,'R','tD'))         # 0: square
    S('tD', None, T(0,'L','hg1'))
    S('tW', T(0,'R','tF'), T(1,'R','tW'))         # to the cell right of S's guard
    S('tF', T(0,'R',halt_state), T(1,'L','hg1'))  # F = 0: HALT; F = 1: it becomes the guard
    # ---- 4. prime: home, then copy M to its left
    home('hc', None, T(1,'R','hc5'))              # new M starts with two cells
    S('hc5', T(1,'R','hc6'), None)
    S('hc6', T(0,'R','hc7'), None)
    S('hc7', T(0,'R','hc8'), None)
    S('hc8', None, T(1,'R','hc9'))                # old M guard
    S('hc9', None, T(0,'L','cL1'))                # cursor at old M index 0
    S('cL1', T(0,'L','cL2'), T(1,'L','cL1'))
    S('cL2', T(0,'L','cL3'), None)
    S('cL3', T(1,'R','cR1'), T(1,'L','cL3'))      # new M += 1
    S('cR1', T(0,'R','cR2'), T(1,'R','cR1'))
    S('cR2', T(0,'R','cR1'), T(1,'R','cQ2'))      # found: one past the cursor
    S('cQ2', T(0,'L','hg1'), T(1,'L','cQ3'))      # 0: cursor at the last index -> done
    S('cQ3', None, T(0,'L','cQ4'))
    S('cQ4', T(1,'L','cL1'), None)
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    lines = ["; Halts iff Legendre's conjecture is false (no prime between n^2 and (n+1)^2 for some n >= 1).",
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'legendre.txt', 'w').write(out)
    print(len(ORDER), 'states')
