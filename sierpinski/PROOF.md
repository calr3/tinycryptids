# The proof, in plain words

This is a guided tour of the Lean proof that the Sierpiński machine halts if and only if every
odd `k < 78557` has a prime `k·2^n + 1` with `n ≥ 1`. The proof is in
`../lean/TinyCryptids/Sierpinski/`; each step below names the lemma that carries it.

## What is proved

```lean
theorem TM.Sierpinski.halts_iff :
    Halts delta start ↔ ∀ k, k % 2 = 1 → k < 78557 → ∃ n, 1 ≤ n ∧ Prime (k * 2 ^ n + 1)
```

The merged machine's theorem (`TM.Sierpinski.M60.halts_iff`) states the same thing
for `delta2`, and is transferred from the design's (`M60.lean`). To trust it you need the Lean
kernel, the machine model (`../lean/TinyCryptids/Core/`) and the listing of the machine. The
theorem depends only on `propext`, `Classical.choice` and `Quot.sound` (`../lean/Check.lean`).

Tapes are written as streams seen from the head: `ones n s` is `n` cells of 1 followed by `s`,
`F` a 0, and `cfgL q s R` the machine in state `q` reading the first cell of `s`.

## Part 1: the mod walk (`Round.lean`)

`MW Y d r h j` is the walk for the divisor `d`: D (`d + 1` cells, its hole at cell `h`, home at
`h = d`), R (`r + 2` cells, its hole at cell `j`), and `Y` left of D (K, its separator and C).
It tests `P = d + r + 1`.

* `dadv`: the D hole moves from cell `h` to cell `h % d + 1` (from the last cell it wraps to
  cell 1). `pr_find`, `pm_find`: the parsers between the holes; when a hole is next to the
  separator they meet three 0s (`PPR.find3`, `PPM.find3`).
* `mw_step`: one round, `MW Y d r h j` to `MW Y d r (h % d + 1) (j + 1)`. `mw_upto`: after `j`
  rounds from home the D hole is at cell `(d + j − 1) % d + 1`.
* `mw_last`: in the last round the R hole falls off; the head comes back over R to D's last
  cell (`E3 Y d r h`).
* `comp_start`: the hole is home (`d ∣ P`): D, the separator and R become one block of ones.
  `shift`: it is not: the hole is filled, the separator's first cell is D's new home, R loses
  its cell 0 and gets its hole there, and the walk for `d + 1` starts: `MW Y (d + 1) r (d + 1) 0`.
  `prime_end`: the same with R left with a single cell: `P` is prime (`WP`).

## Part 2: one candidate (`Cycle.lean`)

* `test`: from `MW Y d r d 0`, if no `e` in `[2, d)` divides `P = d + r + 1`, the machine
  reaches `WP` when P is prime, and otherwise stops at a divisor `d'` with its hole home:
  `E3 Y d' r' d'`. It is an induction on `r`; each round either finds `d ∣ P` (the D hole is
  home after `r + 1` steps iff `d ∣ r + 1`) or shifts to `d + 1`.
* `rtail`, `comp_end`: from the divisor, D := 3 (hole home at cell 3), the separator, and R with
  `P − 2` cells and its hole at cell 0, the head on R's last cell: `cfgL s1 (ones (P − 3) (F ::: YR Y)) blank`.
* `loop_tail`, `loop_step`, `loop`, `loop0`: one round of the loop moves the last cell of X into
  X' and appends a cell to T, so from `m` cells of X the machine reaches `t1` with X' and T of
  `m` cells each, whatever lies left of X.
* `dfin`: when X was R (`t1` reads the separator), the gap and the X'/T separator are filled and
  the machine goes back to the D hole: `MW Y 3 (2m + 1) 3 0`, the walk for the next candidate.
* `wipe`: from `WP`, D and R are erased, a cell is appended to K, and the head is on it.

## Part 3: the counter and a new k (`Counter.lean`)

* `grp`, `Cs`: a group of the counter is its marker and four bits; `Cs v` is the counter
  holding `v`. `Mk q`: the state `q` reads a marker and goes on to bit 0; `t1` (the end of the
  loop on K) and `Dm` both do.
* `grp_zero`: a group 0 borrows (its bits become 1) and the walk goes on to the next group.
  `grp_dec`: a group `u > 0` becomes `u − 1` (four cases on the lowest set bit), and the
  machine runs right past C's separator. `cnt_dec`: the counter `w + 1` becomes `w`.
  `cnt_zero`: from 0 the borrow runs past the top group: **halt**.
* `newk`: the cell left of K' is filled (K gains 2 cells), and the copy T becomes the new
  region by `rtail`. `newk_pseudo`: the step to `k = 1`, where T is one cell short and `g6`
  makes R's hole on a blank cell.

## Part 4: putting it together (`Main.lean`)

* Checkpoints: `XK k v` is K (`k + 6` cells), its separator and `Cs v`; `CK k n v` is the mod
  walk for `P = k·2^n + 1` (`MW (XK k v) 3 (P − 4) 3 0`); `KT k v` is the end of the loop on K
  (`k + 5` cells) at the step to `k`.
* `kt_halt`: `KT k 0` halts. `kt_next`: `KT k (w + 1)` reaches `CK k 1 w`. `kt_pseudo`:
  `KT 1 (w + 1)` reaches `KT 3 w` (its candidate is 5: `test` with `prime5`).
* `cand`: from `CK k n v`, a prime P leads to `KT (k + 2) v`, a composite one strictly to
  `CK k (n + 1) v` (`cand_succ`: `k·2^(n+1) + 1 = 2P − 1`). The two checkpoints differ in R
  (`mw_R`), so the run takes at least one step (`reach1_of_ne`).
* `search`, `good_reach`: if `k` has a prime `k·2^N + 1`, `CK k 1 v` reaches `KT (k + 2) v`.
  `bad_loops`: if it has none, `CK k 1 v` never halts (`not_halts_of_progress` over the
  `CK k n v`).
* `seed_reach`: the seed writes `Cs 39278` and K and reaches `KT 1 39278`. `reach_i`: if the
  odd `k` from 3 to `1 + 2i` are all good, the machine reaches `KT (3 + 2i) (39277 − i)`.

The main theorem: (←) all `k` good gives `KT 78557 0` (`reach_i 39277`), which halts
(`haltAt_of`). (→) if the machine halts, induction over `i`: the machine reaches `CK k 1 w` for
`k = 3 + 2i`, and if `k` had no prime that configuration, and with it the start, would never halt
(`bad_loops`, `halts_det`); `k = 1` has the prime 3 (`good_one`).
