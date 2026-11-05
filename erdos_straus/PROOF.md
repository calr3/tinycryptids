# The proof, in plain words

This is a guided tour of the Lean proof that the 187-state design `erdos_straus.txt` and the
128-state machine `machines/erdos_straus_128.txt` halt if and only if the Erdős–Straus
conjecture is false. The proof is in `../lean/TinyCryptids/ErdosStraus/`, on top of the shared
machine model in `../lean/TinyCryptids/Core/`; each step below names the lemma that carries it.

## What is proved

```lean
theorem TM.ErdosStraus.halts_iff : Halts delta start ↔
    ∃ n, 2 ≤ n ∧ ∀ x y z, 1 ≤ x → 1 ≤ y → 1 ≤ z → 4 * x * y * z ≠ n * (x * y + y * z + z * x)
```

and the same for the merged machine (`TM.ErdosStraus.M128.halts_iff`, `delta2`). Both theorems depend only on `propext`, `Classical.choice` and `Quot.sound`
(`../lean/Check.lean`).

## Part 1: arithmetic (`Spec.lean`)

* `Hit n x y`: `m + 1 ≤ ay ≤ 2m + 2` and `ay − m ∣ my`, with `a = 4x − n`, `m = nx`.
* `D_eq`: `ay − m = 4xy − n(x + y)` (truncated subtraction on both sides).
* `test_of_hit`, then `sol_of_test` (from the compiled proof): a hit gives `z = my/D ≥ 1` with
  `4xyz = n(xy + yz + zx)`.
* `hit_of_sorted`: a solution with `x ≤ y ≤ z` has `n < 4x ≤ 3n` (from `4/n ≤ 3/x` and
  `zD = nxy > 0`), `D ≤ nx` (from `y ≤ z`) and `D ∣ nxy`: a hit.
* `solvable_iff`: `n` has a solution iff some `x` with `n < 4x ≤ 3n` has a hit (`sort3` sorts
  a solution).

## Part 2: the x step (`XStep.lean`)

The tape left of N is read from R's last cell: `Ld n U` in the debt (R has `2n + 3` cells and
its hole on cell `2n + 1 − 2U`, A is a single cell) and `Lb n a` after it (R has `2n + 3 − a`
cells, A `a + 1`). `G Y n m` is the x step's start, on N's cell 0, with `M = m + 1` and
`K = m + 4` cells.

* `g_start`, `cb_step`, `cb_next`, `cb_last`, **`nloop`**: the N loop. Per cell of N, M's
  separator moves one cell right and K gets two cells at its end (it loses its first cell to
  the separator): `G Y n m` to `QS Y n (m + n)`, back on N's last cell.
* **`debt_move`** (`U + 4 ≤ n`): R's hole walks 8 cells left; on to `G (Ld n (U + 4))`.
* `sfill` (the separator moves after the first), `sfill_over` (four moves on an R of three
  cells halt), `hcheck` (R keeps at least 3 cells, or the machine halts).
* **`cross_move`** (`U ≤ n < U + 4`): the walk meets the separator at unit `n − U + 1` (four
  cases); the other `U + 4 − n` units are separator moves. **`b_move`**, **`b_halt`**: after the
  debt, four separator moves; with `a + 4 > 2n` the machine halts.
* **`setup`**: to the end of the tape, K's hole on its last-but-one cell, `D = 11`, `P = 1`,
  then back to M's cell 1: `YS n a m 0 0`.

## Part 3: the y step (`YLoop.lean`, `Walk.lean`)

`KD' c e d Z` is `K 00 D 00 Z` with K's hole on cell `c`, `e` cells after it and `d` cells in D.
`YP X m j c e d p` is `P += M` with M's cursor on cell `j`.

* `pm_step`, `pm_next`, `pm_last`, **`pmloop`**: one cell onto P's end per cell of M; the way
  back crosses the one hole of K.
* **`consume_start`**: to A's cell 1 (the left end). `CU a i Z` is a unit with the A cursor on
  cell `i`, `AC a i Z` the return to it.
* **`unit1`** (first lap, `c ≥ 2`): K's hole one cell left. **`lap2_find`**, **`unit2`** (second
  lap, `c = 1`, `e ≥ 2`): the finder recognises the hole on K's cell 1 (`k_finder` in
  `build.py`: a 0 right after a separator's first cell), and the separator `K | D` moves one
  cell left. **`stop`** (`c = e = 1`): K, its separator and D merge back into K less four cells,
  P is erased, the A cursor is filled, and the next x step starts: `G (Lb n a) n m`.
* `ac_next`, `ac_last`; **`lap1_next`**: after the units in the first lap, the next y step.
* `Walk.lean`: `../OddPerfect`'s mod walk (`MW`, `E3`, `dadv`, `mw_step`, `mw_last`, same
  states), with **`mw_from`** (the walk from any hole positions) and **`walk1`**: from
  `MW Y d r 1 1` D's hole ends on cell `r % d + 1`. **`test_setup`**: after the units in the
  second lap, the walk's first step done by hand reaches `MW (KY …) d (p − 1) 1 1`.
  **`test_fail`**: not home, fill D's hole, the next y step.

## Part 4: the n step and the seed (`NStep.lean`)

* **`nstep`**: from a home D hole, cross K's hole, erase from M to four 0s, then
  **`nstep_tail`**: `N += 1`, R absorbs A and its separator, `A := 1` two cells further left,
  R's hole on its last-but-one cell, `M = 1`, `K = 1111`, back to N's cell 0:
  `G (Ld (n + 1) 0) (n + 1) 0`.
* **`seed_reach`**: the seed writes `11 00 1111 00 11` and reaches `nstep_tail` for `n = 1`,
  `a = 1`.

## Part 5: the loops and the main theorem (`Main.lean`)

* `kc`, `ke`, `kd`: the y counter's `(c, e, d)` at `W` (first lap `W ≤ m + 1`, second lap
  after), with `k_lap1`, `k_lap2`, `k_stop`. **`unitW`**: one unit at any `W ≤ 2m + 1`.
  **`cloop`**: the units from cursor `i` on, to the end (`W' ≤ 2m + 2`) or to the stop.
* **`ystep_lap1`**, **`ystep_test`** (hit: `nstep`; no hit: the next y step, using `mod_succ`),
  **`ystep_stop`**: one y step from `YC n a m W p`.
* **`yloop`**: from step `j + 1` (`W = aj`, `p = mj`), a hit at some `y > j` reaches the next
  `n`, none reaches the next x (by induction on `2m + 2 − aj`).
* `Gx n x`: the x step's start for `U = 4(x − 1)`, `m = n(x − 1)`. `xs_debt`, `xs_y`,
  `xs_halt`, `G_next`; **`xloop`**: a hit for some `x' ≥ x` reaches `C (n + 1)`, otherwise the
  machine halts.
* **`cycle`**: from `C n` the machine reaches `C (n + 1)` in at least one step (`C_ne`) if `n`
  has a hit, and halts otherwise. `start_reach`: the start reaches `C 2`.
* **`halts_iff`**: (←) `haltAt_of` runs `cycle` up to the first `n ≥ 2` without a solution
  (`found_iff`, `solvable_iff`); (→) if every `n ≥ 2` has a solution, `not_halts_of_progress`
  over the configurations `C n`.

## The merged machine (`M128.lean`)

Generated by `gen_reduced_lean.py`: `delta2`, the state map `phi`, `compat` (every defined
transition of the design is one of `delta2` under `phi`), and `M128.halts_iff` by
`halts_iff_of_sim` from `halts_iff` and `haltAt_of` (the design halts only through its
explicit `halt` state).
