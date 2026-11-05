# The proof, in plain words

This is a guided tour of the Lean proof that the machine halts if and only if some composite `n`
has `φ(n) ∣ n − 1`. The proof is in `../lean/TinyCryptids/LehmerTotient/`; each step below names
the lemma that carries it.

## What is proved

```lean
theorem TM.LehmerTotient.halts_iff : Halts delta start ↔
    ∃ n, 2 ≤ n ∧ ¬ Prime n ∧ totient n ∣ n - 1
```

The merged machine's theorem (`TM.LehmerTotient.M67.halts_iff`) states the same thing
for `delta2` and is transferred from the design's (`M67.lean`). Both depend only on `propext`,
`Classical.choice` and `Quot.sound` (`../lean/Check.lean`).

Tapes are streams seen from the head: `ones n s` is `n` ones followed by `s`, `cfgL q s R` the
machine in state `q` reading the first cell of `s` (the cells left of the head are read
leftwards).

## Part 1: the coprimality walk (`Walk.lean`)

`../carmichael`'s lemmas, copied for this machine (its walk states are the same). `TK a b j e X`
is the walk with K's hole after `a` slots and before `b`, R's hole after `j` and before `e`, and
`X` right of R.

* `tick`, `tickW`, `wrapC`, `wrapM`, `wrapN`: one tick, and K's hole wrapping with R's hole on
  its first slot (coprime: `CV1`), in the middle (go on) or on its last slot (not coprime: `EC1`).
* `stride`, `strides`, `test`: from both holes on their first slots, the walk ends at `Res k r Y`,
  `CV1` if `gcd k r = 1` and `EC1` if not, both holes on their first slots again
  (`../carmichael/`'s `first_hit`).
* `shift`: from `EC1` with `r ≥ 2`, K/R's separator one cell right and the next test.
* `reset`: from R's hole at the round end, `(n − 1, 1) → (1, n)`, then on R's slot 2 (`PU1`).

## Part 2: one mod walk (`Test.lean`)

`../legendre`'s routines for a pair `D 00 P` between any two streams (as in `../lemoine`): `MW`
the mod walk, `SHT` the test start, `mw_step` and `mw_upto` the steps.

* `mw_last_div`: the walk over, D's hole back on cell 1: `k1` reads the 0 left of D and the
  machine halts.
* `mw_last_nodiv`: else `k1` reads a 1 and the walk ends at `ND`, `A` next to D's hole.
* `one_test`: from `SHT` with `d ≥ 2`, `r ≥ 1`: `r % d = 0` halts, else `ND`.

## Part 3: the routes (`Round.lean`)

`PR d p` is the pair from D's cell 0.

* `coprime`: from `CV1`, the parser finds D's hole, the separator moves (`d + 1`, `p − 1`), and
  `ret` goes back: a left parser to D's hole, one to R's hole, then `EC1` on R's slot 2.
* `to_test`: from `EC1` at the round end, `reset`, the parser to D's hole, the test start `SHT`.
* `prime_next` (`p = 0`): a cell after P. `nodiv_next`: on to P's end over D's hole and the
  separator, a cell after P.
* `norm`: from P's end, the separator and D's hole are filled and `1 0 1 0 0` is written from D's
  cell 0, for any position of the hole; `norm_ret`: then `ret`.

## Part 4: the theorem (`Spec.lean`, `Main.lean`)

* `cp n k` (`../carmichael/Spec.lean`) counts the `j < k` with `gcd j n = 1`, so `cp n n = φ(n)`;
  `cp_two`: `cp n 2 = 1`, `cp_lt`: `cp n k < k`, `totient_two`: `φ(n) ≥ 2` for `n ≥ 3`.
* `bad_iff`: for `n ≥ 2`, `¬ Prime n ∧ φ(n) ∣ n − 1` iff `Bad n`: `p = n − 1 − φ(n) ≥ 1` and
  `p % φ(n) = 0` (`totient_le_comp`: a composite misses 0 and a divisor; `totient_prime`).
* `Cn n`: round `n` starts, K/R `(2, n − 2)`, the pair `(1, n − 2)`.
* `test_count` and `sweep`: the tests of `k = 2, …, n − 1` (`gcd_sub`: `gcd(k, n − k) =
  gcd(k, n)`) end with the pair `(φ(n), n − 1 − φ(n))`.
* `round`: from `Cn n`, `Bad n` halts; otherwise the machine reaches `Cn (n + 1)` in at least one
  step (`next_tail`: `norm_ret`, then `shift`).
* `seed_reach`: the seed writes `Cn 3`.
* (←) `haltAt_of`: `halt_from` follows the rounds up to the counterexample; a smaller one halts
  the machine earlier. (→) `not_halts_of_progress` over the `Cn n`, if no `n ≥ 3` is `Bad`.
