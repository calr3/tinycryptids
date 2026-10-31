# Goldbach's conjecture with 6 symbols: 34 instructions

**Best machine: `machines/goldbach_10.txt`, 10 states, 6 symbols, 34 instructions** (BBi: the
defined transitions, the halting one left undefined). Started on a blank tape it **halts iff
some even number `2n ≥ 4` is not the sum of two primes**. Lean proves this
(`TMK.Goldbach.M10.halts_iff`, `../lean/TinyCryptids/Goldbach/`, multi-symbol model
`Core/Multi.lean`):

    Halts M10.delta2 M10.start2 ↔ ∃ n, 2 ≤ n ∧ ∀ p q, Prime p → Prime q → p + q ≠ 2 * n

and `M10.halts_iff_not : Halts M10.delta2 M10.start2 ↔ ¬ GoldbachConjecture` (both definitions in
`Defs.lean`); axioms `propext`, `Classical.choice`, `Quot.sound`.

Standard text (states `A`–`J`, symbols 0–5; `---` is undefined, `G` reading 5 is the halt):

    1RD3LB---------5RF_0RD2RC2LB3LB---5RD_0LE2LB2RC3RC2LB5LE_1LD1LI1RD3LB------_0RH1RE1LE4LE1RA1LI_---1RG------------_---1RA------------_---1RH------1RH1LI_1RF5LJ------------_0RF1LJ---------1LJ

| Machine | Symbols | States | BBi | Lean |
|---------|-----:|-----:|-----:|------|
| Google DeepMind's `goldbach_21` (reduced from the published `goldbach_25`) | 2 | 21 | 41 | their own |
| `goldbach.txt` (the design, `build.py`) | 6 | 13 | 35 | `TMK.Goldbach.halts_iff` |
| **`machines/goldbach_10.txt`** (`minimize_clique.py goldbach.txt … e2:5`) | 6 | **10** | **34** | `TMK.Goldbach.M10.halts_iff` |

Ten states is optimal for merging this design (the clique bound is 10). The merge also saves an
instruction: `inc`'s walk over 1s became `chk`'s (both are `1 → 1R`), and the growth states
`g1`, `g2` joined `rst`. The halting slot `e2:5` is kept exclusive, so it stays undefined.

## Algorithm

Symbols: `0` blank, `1` a cell, `2` = x (a marked cell), `3` = B (the boundary, marked),
`4` = b (the boundary, unmarked), `5` = s (the separator). At the start of each pair `(p, q)`:

    0 0 [P: 1^p] s [Q: 1^q] 0 0        (Q may hold one stale b, on its 4th cell or later)

For each even `n` the pairs are `(n − 2, 2), (n − 3, 3), …`. P is tested first, then Q if P is
prime. If both are prime, the next stage is `(n, 2)` for `n + 2`: two cells are appended, the
separator is written on Q's last cell and the old separator is erased. If either is composite,
the separator moves one cell left (`p − 1, q + 1`). After `(2, n − 2)` comes `(1, n − 1)`: the
P test's entry (`e1`, `e2`) then reads the separator on P's second cell, an undefined transition,
and the machine halts. So it halts exactly at the first `n` with no pair.

**Primality of a block X** (between two delimiters, each `0` or `s`) by trial division in place.
The divisor `d` is X's first `d` cells D; the rest R (`r = x − d` cells) starts with the boundary.
`d ∣ x` iff `d ∣ r`. A round for `d`:

* `mark` marks R's first cell `B`. Then a zigzag marks one cell of R (`zr`: the first 1 to the
  right) and then one cell of D (`zl`: the last 1 of D, walking left). When D is fully marked,
  `zl` reaches the delimiter and `rst` unmarks D before marking its last cell (a lazy reset).
* When R runs out, `zr` reads the right delimiter, and `chk` unmarks everything from the right.
  It turns `B` into `b`, so the boundary is kept. If it meets an unmarked cell of D, then
  `d ∤ r`: `inc` moves `b` one cell right (`d + 1`), and `mark` starts the next round. If `b`
  falls off X, then `d = x`, no divisor was found, and X is prime. If `chk` reaches the left
  delimiter, D was fully marked, so `d ∣ r` (with `r ≥ 1`) and X is composite.
* The first round is set up by `e1`, `e2` (the boundary on the third cell: `d = 2`).

The exits are told apart by which delimiter is read: `s` or `0`. A prime P (`mark` reads `s`)
starts Q's test. A prime Q (`mark` reads 0) starts the growth to the next stage. A composite P
(`chk` reads 0) goes to `kr`, which erases P's `b` on the way to the separator and shifts. A
composite Q (`chk` reads `s`) shifts at once (`s → 1`, then `sh` writes `s` on P's last cell and
`wl` returns). That leaves Q's `b`, which is harmless: it lies on Q's 4th cell or later, in R
during the next first round, and `zr` treats it like a 1 (`b → x`).

The boot (one instruction, `sh` reading 0) runs the growth on the blank tape and reaches
`(2, 2)` after 13 steps.

## Files

| File | Contents |
|------|----------|
| `build.py` | The design generator (13 states, 35 instructions) → `goldbach.txt` |
| `machines/goldbach_10.txt` | The merged machine |
| `annotate.py` | Writes `machines/goldbach_10_annotated.txt` (every state and transition explained): `python3 annotate.py machines/goldbach_10.txt machines/goldbach_10_annotated.txt` |
| `RECORDS.md` | The machines and how each was obtained |
| `test_e2e.py [machine]` | The `(p, q)` sequence at every P test against a reference (up to `n = 148`); started on odd "stages" 11 and 13, it must halt at `(1, 10)` and `(1, 16)`; 10⁹ steps without halting |
| `gen_lean.py` | Writes `Machine.lean` (the design) and `M10.lean` (the merged machine, `phi`, `compat`, the transfer) |

## Proof (`../lean/TinyCryptids/Goldbach`)

* `Tape.lean`: configurations on `lst` lists; `CL q L R` has the head on `L 0`, where a left move
  lands. Walks `walkR`/`walkL` over any list (writing `f a`), `runR`/`runL` over runs.
* `Test.lean`: the test for any delimiters `l`, `rr` and outside tapes `Lc`, `Rc`. It defines
  `T d w` (a round starts), `Zc a j k v` (mid-zigzag: `j + 1` marks in D, `a` unmarked,
  `k + 1` marks in R, `v` left) and `Cx d k` (composite exit, X = `1^d b 1^k`). The step lemmas
  are `zstep_more`, `zstep_wrap` (the lazy reset), `zend_more` (`d ∤ r`: `d + 1`) and `zend_div`.
  `zig` is a round by induction on `v`, with the invariant `(j + 1) % d = (k + 1) % d`. `test`
  is the whole test by induction on R's length: prime → `T x []`, composite → `Cx m k` with
  `m ∣ x`.
* `Main.lean`: `Pc p Q`, `QOK`, `p_entry`, `q_entry`, `grow`, `p_comp`, `q_comp`, `shift`,
  `pair_step`, `boot` (13 steps checked by `decide` on finite tapes). Then `halts_iff`: (→) by
  `not_halts_of_progress` over pairs that keep "no larger `p'` worked", (←) by `halt_from`
  (induction on `2N − n`, then on `p`).
* `M10.lean`: the transfer by `halts_iff_of_sim` (`Core/Multi.lean`).
