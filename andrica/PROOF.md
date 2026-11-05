# The proof, in plain words

This is a guided tour of the Lean proof that the machine halts if and only if some consecutive
primes `p < q` have `4p ≤ (q − p − 1)²`. The proof is in `../lean/TinyCryptids/Andrica/`; each
step below names the lemma that carries it.

## What is proved

```lean
theorem TM.Andrica.halts_iff : Halts delta start ↔
    ∃ p q, Prime p ∧ Prime q ∧ p < q ∧ (∀ r, p < r → r < q → ¬ Prime r) ∧ 4 * p ≤ (q - p - 1) ^ 2
```

The merged machine's theorem (`TM.Andrica.M51.halts_iff`) states the same thing for
`delta2` and is transferred from the design's (`M51.lean`). Both depend only on `propext`,
`Classical.choice` and `Quot.sound` (`../lean/Check.lean`).

Tapes are streams seen from the head: `ones n s` is `n` ones followed by `s`, `cfgL q s R` the
machine in state `q` reading the first cell of `s` (the cells left of the head are read
leftwards).

## Part 1: the arithmetic (`Spec.lean`)

* `IsT m t`: `4m ≤ t²` and `(t − 1)² < 4m`, so `t = ⌈2√m⌉`. `isT_le_iff`: then `4m ≤ g²` iff
  `t ≤ g`; `isT_mono`: `t` grows with `m`.
* `Hinv m t x`: the phase block for `m`, as an equation, `4m + (t + 1) mod 2 = (t − 1)² +
  2(x + 1)` with `x` odd and `x + 1 ≤ t`. `hinv_isT`: it gives `IsT m t`. `hinv_next`: the
  machine's step (`x + 2`, or `t + 1` and `x = 1` when `x + 3 > t`, functions `tn`, `xn`) gives
  `Hinv (m + 1)`.
* `lpb m`, the largest prime below `m` (`lpb_spec`, `lpb_eq`), `exists_prime_gt` (a prime factor
  of `n! + 1`), and `next_prime`: if `(p, m]` has no prime, the next prime after `p` is above `m`.
* `Bad m`: `m` is composite and `4 · lpb m ≤ (m − lpb m)²`. `bad_iff`: some `m ≥ 3` is bad iff
  the conjecture fails. A bad `m` and the prime after it give a counterexample; a counterexample
  `p < q` makes `q − 1` bad.

## Part 2: one test (`Test.lean`)

`../legendre`'s trial division for a pair `D 00 R` between any two streams, copied from
`../lemoine`: `MW` the mod walk, `SHT` the test start, `mw_step`, `mw_upto`, `mw_last_nodiv`,
`mw_last_div`, `shift`, `tail_more`, `tail_zero`. `test`: from `SHT` with `d = 2`, a prime `m`
reaches `CP` (the head on R's last cell, heading left) and a composite reaches `CK d' r'` for some
divisor split `d' + r' = m` (the head left of D, in the countdown's scan).

## Part 3: the rest of a round (`Round.lean`)

`Lx t x u` is everything left of the pair: T (`t − u` cells), the U/T separator, U (`u` cells),
the H/U separator and H (`Hr t x`, its hole at `x`). `RS m t x u` is the round start.

* `comp`: from `CK`, the scan finds the U/T separator and moves it one cell right, ending at
  `HE t x (u + 1)` (the head just left of the separator). `comp_halt`: when T had one cell, the
  scan's last step reads the T/D separator and halts.
* `prime`: from `CP`, a parser crosses D's hole, the scan finds the separator, which is filled
  and written at U's left end: `HE t x 0`.
* `hadv`: a parser finds H's hole and moves it two cells right (`AH t (x + 2) u`). `hwrap` (with
  `hwrap_tail`): H's hole on one of its last two cells; H's last cell joins the separator, U gets
  a new cell 0, and two new cells on H's left hold the new hole: `AH (t + 1) 1 (u + 1)`.
* `ret` (with `rebuild`): a parser finds D's hole, `D := 2`, R gets one more cell: `RS (m + 1)`.

## Part 4: the main loop (`Main.lean`)

* `Inv m t x u`: `Hinv m t x`, T is not empty, and `|T| + (m − p) = t(p) + 1` for the last prime
  `p < m` (`IsT p tp`).
* `inv_bad`: under `Inv`, `Bad m` iff `m` is composite and `|T| = 1`.
* `after`: the phase step and the way back, from `HE` to `RS (m + 1)` with `tn`, `xn` and `un`
  (U grows with H).
* `round`: from `RS m`, a composite with `|T| = 1` halts (`HaltAt`); otherwise the machine
  reaches `RS (m + 1)` in at least one step, and `Inv` holds there: a prime resets the countdown
  to `t(m)` (`lpb (m + 1) = m`), a composite takes one off it.
* `seed_reach`: the seed writes `m = 2`, which is prime: `RS 3 4 1 1`, and `inv_three`.
* `halts_iff`: (→) if the conjecture holds, no `m` is bad, so every round reaches the next and
  `not_halts_of_progress` shows the machine never halts. (←) a counterexample gives a bad `N`
  (`bad_iff`); `halt_from` runs the rounds from 3 up to `N`, and the machine halts at `N` at the
  latest (`haltAt_of`).
