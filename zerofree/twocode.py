"""Search the two codes of build.py: code A (3 cells for a in 0..4, between rounds) and
code B (what the pass writes), such that
 * the pass writes B one cell at a time as it reads A: B's cell i depends only on the old
   parity b and A's cells 0..i (B1(b,x), B2(b,x,y), B3(b,x,y,z)),
 * B determines a' = (2a + b) mod 5 of the new digit,
 * read right to left, A(a') is written one cell at a time from B (z from B3, y from B3 B2,
   x from all of B), and B's cell z equals A(a')'s (so the separator stays 0 0),
 * no A word is 000 or ends in 00, and no B word ends in 00 (blank group, separator).
Prints every solution (A, B as a table (b, a) -> word)."""
import itertools
f = lambda b, a: (2 * a + b) % 5
W = [w for w in map(''.join, itertools.product('01', repeat=3)) if w != '000' and not w.endswith('00')]
inputs = [(b, a) for b in (0, 1) for a in range(5)]
n = 0
for A in itertools.permutations(W, 5):
    b3 = {(b, a): int(A[f(b, a)][2]) for b, a in inputs}
    for m1 in range(16):
        beta1 = {(b, a): (m1 >> (2 * b + int(A[a][0]))) & 1 for b, a in inputs}
        for m2 in range(256):
            beta2 = {(b, a): (m2 >> (4 * b + 2 * int(A[a][0]) + int(A[a][1]))) & 1 for b, a in inputs}
            B = {k: (beta1[k], beta2[k], b3[k]) for k in inputs}
            tgt, ok = {}, True
            for k in inputs:
                w = B[k]
                if (w[1], w[2]) == (0, 0) or tgt.setdefault(w, f(*k)) != f(*k): ok = False; break
            if not ok: continue
            ys = {}
            if any(ys.setdefault((w[2], w[1]), A[a2][1]) != A[a2][1] for w, a2 in tgt.items()): continue
            n += 1
            print('A =', list(A))
            print('BETA =', {f'{b}{a}': ''.join(map(str, B[(b, a)])) for b, a in inputs})
print(n, 'solutions')
