# The proof, in plain words

This is a guided tour of the Lean proof that the 27-state design `fermatprimes.txt` and the
25-state machine `machines/fermatprimes_25.txt` halt iff some Fermat number `2^(2^n) + 1`
with `n ≥ 5` is prime. The proof is about 720 hand-written lines in
`../lean/TinyCryptids/FermatPrimes/` (`Tac`, `Round`, `Spec`, `Main`; `Machine` and `M25` are
generated). Each step
below names the lemma that carries it.

## What is proved

```lean
theorem TM.FermatPrimes.halts_iff :
    Halts delta start ↔ ∃ n, 5 ≤ n ∧ Prime (2 ^ 2 ^ n + 1)
theorem TM.FermatPrimes.M25.halts_iff :
    Halts delta2 start2 ↔ ∃ n, 5 ≤ n ∧ Prime (2 ^ 2 ^ n + 1)
```

`delta` is the design and `delta2` the merged machine, generated from the text files; each
starts on a blank tape. `Prime` is the repository's definition. Both theorems depend only on
`propext`, `Classical.choice` and `Quot.sound`.

## Part 1: arithmetic (`Spec.lean`)

* `Good m e`: `e` divides neither `m` nor `m − 1`. `FP m` (a **pass**): `m` is prime and
  `m = 2^k + 1` for some `k`.
* **`dvd_pow_odd_add_one`**: `a + 1 ∣ a^(2t+1) + 1`, by induction on `t`, with an explicit
  quotient: if `a^(2t+1) + 1 = (a + 1) c` then `a^(2t+3) + 1 = (a + 1)(a² c − (a − 1))`.
* **`prime_pow_two_add_one`**: if `2^k + 1` is prime and `k ≥ 1`, then `k` is a power of 2. An
  odd factor `q ≥ 3` of `k = q j` would give the divisor `2^j + 1` of `(2^j)^q + 1`, strictly
  between 1 and `2^k + 1`. Then `pow2_of_no_odd`.
* **`fp_iff'`**: for odd `m ≥ 5`, `FP m` iff every odd `e` with `3 ≤ e ≤ m − 2` is good. Even
  `e` cannot divide the odd `m`; an odd divisor `q ≥ 3` of the even `m − 1` is at most `m − 2`;
  `odd_not_dvd_pow2` for the converse.
* **`prime_of_lt`**: trial division up to `b` with `p < b²` proves `p` prime (a divisor
  `d ≥ b` has a cofactor below `b`). `prime_17`, `prime_257`, `prime_65537` by `decide` on at
  most 257 divisors; `fp_5`.
* **`fp_small`**: for `7 ≤ m ≤ 65537`, `FP m` iff `m` is 17, 257 or 65537. `m = 2^k + 1` with
  `k = 2^n` (`prime_pow_two_add_one`) and `2^(2^n) ≤ 65536`, so `n ≤ 4`.
* **`fp_big_iff`**: `(∃ n, 5 ≤ n ∧ Prime (2^(2^n) + 1)) ↔ ∃ m, 65537 < m ∧ FP m`, by the same
  two facts.

## Part 2: the machine on the tape (`Round.lean`)

Tape `D 0 R`, then `F ::: Y` (at least one blank cell, then the rest: in `Main`, more blanks
and the counter). `Dp d c` is D read leftwards from its last cell; when `c = 0` the hole is the
blank left of D's ones.

| name | meaning |
|---|---|
| `W d r c k Y` | mod walk, `k` of `r` steps done, D's hole at `c`, R without a hole |
| `WS d r Y` | `W d r 0 0 Y`: the walk's start |
| `PassCfg n g j` | `G0` on the blank after a block of `n` ones, then `g` more blanks and the counter (`j` ones) |

* **`walk_step`, `walk_all`** (for any `Y`): `WS d r Y` reaches
  `W d r (r % d) r Y`.
* **`walk_end`**: `E` erases R's last cell, `V` fills the separator; `X1` reads D's last cell.
  The blank cells after R are one more.
* **The check.** `check_last` (`c = d − 1`: `X1` fills the hole, `C4` stands on the separator);
  `check_first` (`c = 0`: `X1`, `X` erase to the hole, `Q` reads the blank left of D, `HF`
  refills and turns back on the separator to `C4`); `check_ok` (`1 ≤ c ≤ d − 2`: `Q` reads a
  1, `H1` refills, `G0` reads R's cell 0 after a block of `d + 1` ones).
* **`shift`**: `G0` writes the separator, the walk for `d + 2` starts with `r − 2`. If R is
  empty, the configuration is `PassCfg (d + 1) …`.
* **`rebuild`**: `C4` in a block of `a + b` ones runs to its left end; `C4`, `H1` write `1 1`,
  `G0` the separator: `WS 3 (a + b − 1) Y`.
* **`pass_more`**: from `PassCfg n g (j + 2)`, `P1` runs to the counter and erases a cell, `P2`
  reads another, `P3` runs back, and `C4` stands in the block, with `j + 1` counter cells now
  `g + 2` blanks away. **`pass_halt`**: from `PassCfg n g 1`, `P2` reads the blank after the
  erased cell: the halting state (`HaltAt`).
* **`seed`**: `S1`–`S6` write six counter cells, `S7` leaves a blank, `C4` and `H1` write
  `1 1`: `PassCfg 2 0 6`.

## Part 3: the main theorem (`Main.lean`)

`CS m g j := WS 3 (m − 4) (zeros g (ones j blank))` is the start of candidate `m` with `j`
counter cells.

* **`fail_iff`**: after the walk the hole is on `c = r % d`, and for `d ≥ 3` and
  `m = d + r + 1`, `d` divides `m` or `m − 1` iff `c + 1 = d` or `c = 0`.
* **`test`** (induction on `t`, `r = 2t + 1`, `m = d + r + 1`): if every odd `e < d` is good,
  then `WS d r …` reaches a `PassCfg (m − 1)` when every odd `e` with `d ≤ e ≤ m − 2` is good,
  and some `CS (m + 2)` otherwise (FAIL: `check_last` or `check_first`, then `rebuild`).
* **`cand_fp`, `cand_not`, `cand_pass`, `after_pass`**: from `CS m g j` (odd `m ≥ 5`): a pass
  reaches `PassCfg (m − 1)`, and with `j ≥ 2` then `CS (m + 2) _ (j − 1)`; any other
  candidate reaches `CS (m + 2) _ j` (`fp_iff'`). **`fails`**: a run of failing candidates.
* **`reach_big`**: the start reaches `CS 65539 g 1`. The seed passes `m = 3` (`PassCfg 2 0 6`,
  then `CS 5 1 5`); 5 passes; `fp_small` says the only passes from 7 to 65537 are 17, 257 and
  65537, each costing a counter cell.
* **`haltAt_of`**: if some `N > 65537` passes, induction from `CS 65539 g 1` reaches the first
  pass `≤ N`, and `pass_halt` halts there.
* **`halts_iff`**: (←) by `haltAt_of` and `fp_big_iff`. (→) if no `m > 65537` passes, every
  `CS m g 1` with `m ≥ 65539` strictly reaches the next one (`CS_ne`, `reach1_of_ne`), so by
  `not_halts_of_progress` the run from `CS 65539 g 1` never halts; the run from the start
  reaches it, so the start never halts either.

## Part 4: the 25-state machine (`M25.lean`)

`gen_reduced_lean.py` emits the merged table `delta2`, the state map `phi` and `compat`, and
transfers `halts_iff` with `halts_iff_of_sim` (`../lean/TinyCryptids/Core/Basic.lean`), using
`haltAt_of` for the halting direction.

## What the proof does not cover

* Whether some Fermat number beyond `F_4` is prime: that is the open problem. The proof shows
  that the machine halts exactly when one is.
* Running time: the machine tests every odd `m` in unary; the pass at 257 comes after 1.5·10⁷
  steps, the one at 65537 far beyond reach. Nothing in the proof depends on speed.
* That the Lean `delta2`, `machines/fermatprimes_25.txt`, the standard text in `README.md` and
  the annotated listing are the same machine rests on the generator scripts, not on Lean.
