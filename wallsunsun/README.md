# A Turing machine for Wall–Sun–Sun primes

**`machines/wallsunsun_50.txt`, a 50-state, 2-symbol Turing machine** (99 instructions, BBi).
Started on a blank tape, it **halts iff a Wall–Sun–Sun prime exists**: a prime `p` with
`p² ∣ F(p − (p/5))`, `F` the Fibonacci numbers and `(p/5)` the Legendre symbol. None is known.
Lean proves this (`TM.WallSunSun2.M50.halts_iff`):

    Halts M50.delta2 M50.start2 ↔ ∃ p, Prime p ∧ p * p ∣ fib (wssIndex p)

where `wssIndex p` is `p` if `p % 5 = 0`, `p − 1` if `p % 5 ∈ {1, 4}` and `p + 1` otherwise
(`../lean/TinyCryptids/Defs.lean`). `PROOF.md` walks through the proof, and `RECORDS.md` lists
the machines.

## The search

    for m = 2, 3, 4, …:
        N := F(m − 1) if m % 5 ∈ {1, 4} else F(m + 1)      (counted, not computed)
        if m² ∣ N: HALT

`F(m + 1)` is never written down. It is the number of binary strings of length `m − 1` without
two adjacent 1s, and `F(m − 1)` the number of those that start with `10`. An **odometer** steps
through these strings in increasing order (as Zeckendorf representations, adding 1 each time),
and for each string a **counter** with two base-`m` digits is advanced by one. So the counter
ends at its start value plus `N`, modulo `m²`, and is read off.

There is no primality test, and the machine still halts iff a Wall–Sun–Sun prime exists:

* A Wall–Sun–Sun prime `p` passes (`p ≠ 5`, and `(p/5) = 1` iff `p ≡ ±1 mod 5`).
* If `m` passes, every prime factor `q` of `m` is a Wall–Sun–Sun prime. `q` does not divide
  `m ∓ 1`, and `z(q²)` (the first index with `q² ∣ F`) is `z(q)` or `q·z(q)`. So `z(q²) = z(q)`,
  which divides `q − (q/5)`. The last step needs `q ∣ F(q − (q/5))` for every prime `q`, which
  is quadratic reciprocity for 5. Lean proves it from Gauss's lemma (`PROOF.md`).

## How it works

The tape at the start of round `m` (blocks of 1s, separators `00`, a hole is a single 0):

    B 00 E 00 D

* **B** (`m + 1` cells, no hole): the odometer; its `m − 1` inner cells are the bits, a 1-bit is
  a hole, the least significant bit on the right (next to E).
* **E** (`m + 2` cells): the **low digit**, its hole cycling through cells `1 … m`. A wrap of E
  advances D.
* **D** (`m + 2` cells, its hole on cell 1): the **high digit**.

E's hole is put on cell `m` (the counter is `m − 1`). Counting the `m` cells left of it mod 5
(5 states) decides the first string: `10…0` (B's first inner cell a hole) if `m % 5 ∈ {1, 4}`,
else `0…0`. Then: advance the counter, and repeat

* **next string**: from B's right end, clear holes going left until a cell whose left neighbour
  is not a hole; make it a hole. If there is none (the left marker is reached), stop.
* **advance**: to E's hole, move it one cell (on its last cell: back to cell 1, and then move D's
  hole too), back to B's right end.

The counter ends at `m − 1 + N` mod `m²`: the machine **halts** iff E's hole is on cell `m` and
D's on cell 1, i.e. iff `m² ∣ N`. Otherwise E's hole is filled, the separator left of E moves
one cell left (E grows by a cell, B gives its last cell), B gets two cells on its left, D's hole
is filled, D gets a cell on its right, and D's cell 1 becomes its hole: round `m + 1`.

The design `wallsunsun2.txt` (79 states, `build2.py`) is `../wallsunsuninf`'s design with its
beep (`q9` reading 0) made the halt; 15 of its states are the seed, which writes round 2.
`minimize_clique.py wallsunsun2.txt machines/wallsunsun_50.txt 900 cadical195` gives 50 states:
48 and 49 are unsatisfiable, so 50 is optimal for this design.

## Files

| File | Contents |
|------|----------|
| `build2.py`, `wallsunsun2.txt` | The 79-state design (variants: `extra` cells in B, other residues `holes`) |
| `machines/wallsunsun_50.txt` | The merged machine |
| `test_e2e2.py` | The design's checks m = 2…24 against a reference (B clean, E's and D's holes as the base-`m` digits of `m − 1 + N`), variants that halt where the reference says, and the design and the merged machine run 10⁸ steps with the same tape |
| `gen_lean2.py`, `gen_reduced_lean2.py` | `../lean/TinyCryptids/WallSunSun2/Machine.lean` and `M50.lean` |

The proof: `../lean/TinyCryptids/WallSunSun2/`.

The merged machine in bbchallenge standard text (states numbered, `Z` = halt):

    1R1,0L16_1R2,0L46_1R3,0L15_0R4,1R43_0R5,1L42_1R6,1R41_1R7,1R31_1R8,1R29_1R9,0L18_0R10,0L36_0R11,1L25_1R12,0R39_1R13,1R9_1R14,1R34_1L49,1R14_0L16,1L15_0L17,1L16_0L38,1L8_0R27,1L19_0L23,1L20_0R27,1L21_0R27,1L22_0L23,1L18_0L24,0R27_0R25,1L24_1L10,1R23_1L26,1L25_0R28,1R27_0R27,1L6_0L30,1L0_0R6,1L30_1R47,0R32_0R33,1R32_0R32,1L12_0L35,1L9_0R12,1L35_0L37,1L36_0L36,1L16_1L26,1L26_0R40,1R39_0R39,1R3_0LZ,1L4_0L43,1R2_0L44,1R43_1L45,1L44_0L1,1L44_1L31,1L46_0R48,1R47_0R47,1L13_0R42,1L49
