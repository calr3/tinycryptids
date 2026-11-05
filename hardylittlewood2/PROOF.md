# The proof, in plain words

This is a guided tour of the Lean proof that the machine halts if and only if the second
Hardy–Littlewood conjecture fails. The proof is in `../lean/TinyCryptids/HardyLittlewood2/`;
each step below names the lemma that carries it.

## What is proved

```lean
theorem TM.HardyLittlewood2.halts_iff :
    Halts delta start ↔ ∃ x y, 2 ≤ x ∧ 2 ≤ y ∧ primeCount x + primeCount y < primeCount (x + y)
```

The merged machine's theorem (`TM.HardyLittlewood2.M79.halts_iff`) states the same
thing for `delta2` and is transferred from the design's (`M79.lean`). The theorem depends only on
`propext`, `Classical.choice` and `Quot.sound` (`../lean/Check.lean`).

Tapes are written as streams seen from the head: `ones n s` is `n` cells of 1 followed by `s`,
`F` a 0, `cfgL q s R` the machine in state `q` reading the first cell of `s`, and `bks l X` a
block of `h + 2` ones for each `h` in `l`, each followed by `00`, then `X`.

## Part 1: the arithmetic (`Spec.lean`)

* `Q n`: `n = 1` or `n` is an odd prime; `pq x` counts them up to `x`. `primeCount_eq`: for
  `x ≥ 2`, `primeCount x = pq x` (1 replaces 2; `q_iff_prime`).
* `B g i` is `h₁ + … + h_i` for the gap list `g`. `Fit g`: for each `i ≤ |g|`, `2·B g i` has
  `i` elements of `Q` below it and `2·B g i + 1` is the next one. So `2·B g i + 1` is `q_i`.
* `bad g`: some `i` in `[1, G − 1]` with `Σg < B_i + B_{G−i}`.
* `sound`: `bad g` with `Fit g` gives a counterexample: `y = 2·B_{G−i}`, `x = m − y`; then
  `π(y) = G − i`, `π(x) ≤ i`, `π(m) = G + 1`.
* `complete`: a counterexample `(x, y)`, with `m` the largest element of `Q` up to `x + y`
  (`last_q`), makes `bad` true for `i = G − π(y)`: `q_i > x` and `q_{π(y)} > y`.
* `ok e ts bs`: the counter process (add a top, subtract a bottom, never below 0); `ok_iff`
  (prefix sums) and `ok_iff_bad`: with tops `c, h_{G−1}, …, h₂` and bottoms `h₁, …, h_{G−1}`,
  the process never fails iff the new gap list is not `bad`.
* `Inv m g c`: the bookkeeping at the candidate `m` (`g` starts with 1, all gaps ≥ 1,
  `m = 2Σg + 1 + 2c`, `Fit g`, nothing of `Q` between the last element and `m`). `Inv.comp` and
  `Inv.prime` carry it to `m + 2`; `inv_five` starts it.

## Part 2: trial division (`Round.lean`)

`MW X d r c j` is the mod walk of `../legendre/`, with Legendre's lemmas (`mw_step`,
`mw_last_nodiv`, `shift`, `tail_more`, `tail_zero`, `mw_upto`), and `test`: from
`MW X 3 (m − 3) 0 1`, a prime `m` reaches `P6 X m` (R used up), a composite one a divisor
`MW X d' r' (d' − 1) r'`. The same file as in `../sierpinski/`.

## Part 3: the test at a prime (`Blocks.lean`, `Trip.lean`, `Pair.lean`, `Check.lean`)

* `PR_bks`, `PL_bks`: a parser crosses a list of blocks. `HomeL.gap`, `HomeL.hole`: the trip home
  crosses blocks and a hole and stops after the four 0s.
* `TF n Ub b jb M t jt Y` / `BF …`: the head on the top / bottom hole; `E` has `n` cells, `Ub` are
  the bottoms still to come, `b` the bottom block (hole at `jb`), `M` the blocks between, `t` the
  top block (hole at `jt`), `Y` the rest. `add_top`, `add_bot`: an add trip from either cursor
  (`E` gets a cell; the first one creates `E` with two); `sub_top`, `sub_bot`: a subtract trip;
  `sub_top_halt`, `sub_bot_halt`: from one cell the machine halts.
* `top_step`, `top_last`, `bot_step`, `bot_last`, `bot_end`: a cursor moves one cell, or to the
  next block, or (bottom, B' used up) ends the test. `top_phase`, `bot_phase`: a whole block.
* `pair`: one pair from `PS` (just after the bottom cursor moved): `t` adds, then `b` subtracts,
  halting iff `e + t < b`. `run`: all pairs, by induction on the bottoms still to come; it ends
  at `EP1` with `E` holding `okE … + 2` cells.
* `start_check`: from `P6`, the top hole goes into C and the bottom cursor leaves the parked
  hole. `end_check`: past the parked hole to the D hole.

## Part 4: the rebuilds (`Rebuild.lean`)

* `writer`: from three cells left of a hole, the fixed pattern (a cell, `00`, D = 3 with its hole,
  `00`, R's cell 0 and hole) and back to the D hole: `MW … 3 r 0 1`.
* `comp_rebuild`: after a divisor, C gets a cell and the region is rebuilt for `m + 2`.
* `prime_rebuild`: after the test, a new C of one cell and the region for `m + 2`.

## Part 5: putting it together (`Main.lean`)

* Checkpoints `CK m g c` (the mod walk for `m`) and `PC m g c` (`m` found prime).
* `cand`: a prime `m` leads to `PC`, a composite one strictly to `CK (m + 2) g (c + 1)`
  (`ck_R`, `reach1_of_ne`). `test_prime`: from `PC`, if `bad (g ++ [c])` the machine halts,
  otherwise it reaches `CK (m + 2) (g ++ [c]) 1` (`run`, `okE_sum`: `E` ends with `c` cells).
* `seed_reach`, `first_ck`: the seed reaches `PC 5 [1] 1`, which passes to `CK 7 [1, 1] 1`.
* `no_halt`: without a counterexample every check passes (`sound`) and the checkpoints go on
  forever (`not_halts_of_progress`). `haltAt_of`: with one, `complete` makes the test at the
  largest prime up to `x + y` fail; `reach_all` gets there, or the machine halted earlier.
