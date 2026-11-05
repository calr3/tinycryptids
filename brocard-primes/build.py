"""Generator for a 2-symbol Turing machine that halts iff Brocard's conjecture is FALSE,
i.e. iff for some consecutive primes 3 <= p < q there are fewer than 4 primes between
p^2 and q^2.

It is ../legendre-sieve's incremental sieve with two additions: a marker that separates
the primes whose square has been passed from the others, and a counter K of the primes
found since the last prime square.  At checkpoint m (m >= 2) the tape is

    M 00 P_k 00 ... 00 P_j 00100 P_(j-1) 00 ... 00 P_1 000 S 0 K

* M, P_i, S: as in ../legendre-sieve.  M = 1^(m+2); P_i = 1, a region of p cells with one
  hole at index p-1-(m mod p), 1; S = 1, a region of 2n+1 cells (n = isqrt m) with its
  hole at index 2n-(m-n^2), 1.
* The marker 00100 (a lone 1) stands right of the block of q, the smallest prime with
  q^2 > m (for m = 2, 3: right of M, resp. the block of 3, so that 4 is not a boundary).
  Parsers and the home routine cross it like a separator.
* K = 1^(c+1), c = number of primes found since the last prime square p^2 (p >= 3);
  before 9, c counts every prime (seed: m = 2, c = 1).

One increment m -> m+1 (sweep, home, copy: as in ../legendre-sieve):
  1. Home, M += 1, sweep: each block's hole moves; a wrap means m+1 is composite.
  2. S, prime mode: move its hole, K += 1 (append a 1), go home and copy M.
     S, composite mode: move its hole.  If it wraps, m+1 = n^2: S grows by 2 and K is moved
     2 cells right.  Then scan left to the marker: if the block left of it has its hole
     at the last index, q | n^2, so n = q is prime: a boundary.
  3. Boundary: move the marker one block left (the block of q moves 3 cells right), go to
     the right end and erase K from the right, keeping one cell: HALT if fewer than
     t+1 cells are erased (fewer than t primes since the last prime square).
"""
import sys
ST = {}
ORDER = []
def S(name, t0, t1):
    assert name not in ST, name
    ST[name] = [t0, t1]; ORDER.append(name)
def T(w, d, n): return (w, d, n)

def home(prefix, k):
    """Go left over runs of at most three 0s until a fourth 0 (the left end)."""
    S(prefix+'1', T(0,'L',prefix+'2'), T(1,'L',prefix+'1'))
    S(prefix+'2', T(0,'L',prefix+'3'), T(1,'L',prefix+'1'))
    S(prefix+'3', T(0,'L',prefix+'4'), T(1,'L',prefix+'1'))
    S(prefix+'4', k, T(1,'L',prefix+'1'))

def sweep(m, end):
    """Parser for mode m ('p' prime so far, 'q' composite): crosses blocks
    and separators, finds holes, moves each hole one cell left."""
    S(m+'1', T(0,'R',m+'2'), T(1,'R',m+'1'))
    S(m+'2', T(0,'R',m+'3'), T(1,'L',m+'A'))      # 1: hole found (we are one past it)
    S(m+'3', T(0,'R',end), T(1,'R',m+'1'))        # third 0: end of the P zone
    S(m+'A', T(1,'L',m+'B'), None)                # fill the hole
    S(m+'B', None, T(1,'L',m+'C'))
    S(m+'C', T(0,'R','W2'), T(1,'R',m+'D'))       # 0: hole was at index 0 -> wrap
    S(m+'D', None, T(0,'R',m+'1'))                # new hole one cell left

def build(t=4, c0=1, halt_state='halt'):
    ST.clear(); ORDER.clear()
    # ---- seed: m = 2:  M = 1111, marker, P(2) = 1 [1 0] 1, 000, S = 1 [1 0 1] 1, 0, K
    pat = '1111' + '00100' + '1101' + '000' + '11011' + '0' + '1' * (c0 + 1)
    for i, ch in enumerate(pat):
        last = i + 1 == len(pat)
        S(f'seed{i}', T(int(ch), 'L' if last else 'R', 'hg1' if last else f'seed{i+1}'), None)
    # ---- 1. home and grow M
    home('hg', T(0,'R','hg5'))
    S('hg5', T(0,'R','hg6'), None)
    S('hg6', T(0,'R','hg7'), None)
    S('hg7', T(1,'R','p1'), None)
    # ---- 2. sweep
    sweep('p', 'sp1')
    sweep('q', 'sq1')
    S('W2', T(0,'L','W3'), T(1,'R','W2'))         # wrap: to the right end of the block
    S('W3', None, T(1,'L','W4'))                  # right guard
    S('W4', None, T(0,'R','q1'))                  # hole at the last index; composite
    # ---- 3a. S after a prime-mode sweep (no wrap possible): move hole, K += 1
    S('sp1', T(0,'R','sp2'), T(1,'R','sp1'))
    S('sp2', None, T(1,'L','sA'))
    S('sA', T(1,'L','sB'), None)
    S('sB', None, T(1,'L','sC'))
    S('sC', None, T(1,'R','sD'))
    S('sD', None, T(0,'R','sE'))
    S('sE', T(0,'R','sG'), T(1,'R','sE'))         # to the gap
    S('sG', T(1,'L','hc1'), T(1,'R','sG'))        # append a 1 to K
    # ---- 3b. S after a composite-mode sweep
    S('sq1', T(0,'R','sq2'), T(1,'R','sq1'))
    S('sq2', None, T(1,'L','tA'))
    S('tA', T(1,'L','tB'), None)
    S('tB', None, T(1,'L','tC'))
    S('tC', T(0,'R','tW'), T(1,'R','tD'))         # 0: square
    S('tD', None, T(0,'L','hg1'))
    S('tW', T(0,'R','tF'), T(1,'R','tW'))         # the gap becomes S's last region cell
    S('tF', None, T(1,'R','u1'))                  # K's first cell becomes S's guard
    S('u1', T(0,'R','u3'), T(0,'R','u2'))         # K moves 2 cells right
    S('u2', T(1,'R','u3'), T(1,'R','u2'))
    S('u3', T(1,'L','la'), None)
    # ---- 4. scan left to the marker 00100
    S('la', T(0,'L','lb'), T(1,'L','la'))
    S('lb', T(0,'L','lc'), T(1,'L','la'))
    S('lc', T(0,'L','lc'), T(1,'L','ld'))         # >= 2 zeros, then a 1
    S('ld', T(0,'L','le'), T(1,'L','la'))
    S('le', T(0,'L','lf'), T(1,'L','la'))         # 0: the 1 was the marker
    S('lf', None, T(1,'L','lg'))                  # right guard of q's block
    S('lg', T(1,'R','mh'), T(1,'L','hg1'))        # 0: hole at the last index: boundary
    # ---- 5. boundary: q's block moves 3 cells right (old left guard = new marker)
    S('mh', None, T(1,'R','mi'))
    S('mi', T(1,'L','mj'), None)                  # the cell after the old right guard
    S('mj', T(0,'R','mk'), T(1,'L','mj'))
    S('mk', None, T(1,'R','ml'))
    S('ml', None, T(0,'R','mn'))
    S('mn', None, T(0,'R','r1'))
    # to the right end (four 0s), then erase K from the right
    S('r1', T(0,'R','r2'), T(1,'R','r1'))
    S('r2', T(0,'R','r3'), T(1,'R','r1'))
    S('r3', T(0,'R','r4'), T(1,'R','r1'))
    S('r4', T(0,'L','e0'), T(1,'R','r1'))
    S('e0', T(0,'L','e0'), T(0,'L','e2'))
    for i in range(2, t + 2):                     # cells 2 .. t+1 of K from the right
        S(f'e{i}', T(0,'R',halt_state), T(0,'L',f'e{i+1}'))
    S(f'e{t+2}', T(0,'R','ez'), T(0,'L',f'e{t+2}'))
    S('ez', T(1,'L','hg1'), None)                 # K = 1
    # ---- 6. prime: home, then copy M to its left
    home('hc', T(1,'R','hc5'))                    # new M starts with two cells
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
    refs = {x[2] for v in ST.values() for x in v if x}
    missing = refs - set(ST) - {halt_state}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    lines = ["; Halts iff Brocard's conjecture is false (fewer than 4 primes between p^2 and q^2",
             "; for some consecutive primes 3 <= p < q).",
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, x in enumerate(ST[n]):
            lines.append('    -' if x is None else f'    {r} {x[0]} {x[1]} {x[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'brocard_primes.txt', 'w').write(out)
    print(len(ORDER), 'states')
