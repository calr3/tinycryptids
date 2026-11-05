# The proof, in plain words

This is a guided tour of the Lean proof that the machine halts if and only if some composite `n`
divides `1^(n−1) + 2^(n−1) + … + (n−1)^(n−1) + 1`. The proof is in
`../lean/TinyCryptids/AgohGiuga/`; each step below names the lemma that carries it.

## What is proved

```lean
theorem TM.AgohGiuga.halts_iff : Halts delta start ↔
    ∃ n, 2 ≤ n ∧ ¬ Prime n ∧ n ∣ powSum n (n - 1) + 1
```

The merged machine's theorem (`TM.AgohGiuga.M100.halts_iff`) states the same thing for `delta2`
and is transferred from the design's (`M100.lean`). Both depend only on `propext`,
`Classical.choice` and `Quot.sound` (`../lean/Check.lean`).

Tapes are streams seen from the head: `ones n s` is `n` ones followed by `s`, `cfgL q s R` the
machine in state `q` reading the first cell of `s` (the cells left of the head are read
leftwards), `app l s` a list of cells followed by `s`.

## Part 1: the arithmetic (`Fermat.lean`, `Spec.lean`)

* `fermat`: `a ^ (p − 1) % p = 1` for a prime `p` and `0 < a < p`. Core Lean has no Fermat, so
  `Fermat.lean` proves it: Euclid's lemma from `gcd` (`prime_dvd_mul`), `choose_mul`
  (`C(n+1, k+1)·(k+1) = (n+1)·C(n, k)`) and `prime_dvd_choose`, the binomial theorem for
  `(a + 1)^n` over a recursive sum `ssum` (`binom`), then `(a + 1)^p ≡ a^p + 1` and
  `a^p ≡ a` by induction on `a`.
* `nx`, `nxs`: the position of a cyclic hole after one or `k` advances; `nxs_mod`: from position
  `m % c + 1`, `k` advances lead to `(m + k) % c + 1`.
* `gsum n k = Σ (i^(n−1) − 1)` over the first `k` bases `i = n − 1, …, n − k`, and `fl n k`, the
  flag after them (`fl_iff`: some `gsum n j`, `1 ≤ j ≤ k`, is nonzero mod `n`).
* `gsum_last`: `powSum n (n − 1) + 1 = gsum n (n − 2) + n` (`powSum_gsum`, by induction on the
  bases), so `dvd_iff_gsum`: `n ∣ powSum n (n − 1) + 1` iff `gsum n (n − 2) % n = 0`.
* `gsum_prime` (by `fermat`) and `fl_prime`: a prime never sets the flag. `fl_comp`: a composite
  does, at the step of a divisor `d`, since `d ∣ n ∣ d^(n−1) − 1` and `d ∣ d^(n−1)` would give
  `d ∣ 1`.
* `Bad n`: the flag and `gsum n (n − 2) % n = 0`. `bad_iff'`: for `n ≥ 3`, `Bad n` iff `n` is
  composite and divides `powSum n (n − 1) + 1`; `bad_iff`: some `n ≥ 4` is bad iff the conjecture
  fails (2 and 3 are prime).

## Part 2: powers (`Horner.lean`, `Copy.lean`, `Blocks.lean`)

`../firoozbakht`'s Horner run, ported with one change: the block it skips between the base and
R is `skq a b` (a hole after `a` ones, here S with its hole anywhere) instead of a block with its
hole at cell 1. `Gap` lists what may lie between two blocks (separators around hole-less blocks).
`copy_full` copies R onto Q; `base_loop` makes `β − 1` copies as the base hole goes round;
`base_wrap` merges `R 00 Q`; `he_chain` goes back to the exponent; `exp_round` is one round
`R := β · R`, `exp_loop` all of them, and `horner`: from the exponent hole at cell `ep` and
`R = 1`, the run ends with `R = β ^ (e − ep)` at the exponent's cell 2 (state `PD1`).
`ParserL1` is a left parser without a transition for `00` (HE and PN only cross 1s before their
hole); leaving that transition undefined is what lets the merger reach 100 states.

## Part 3: `B += R − 1` (`Consume.lean`)

`CL Lx p q r`: R holds `r` (the head on its cell 3), S has its hole at cell `p`.

* `s_adv`: S's hole advances (to `nx (p + q − 1) p`), with or without wrap.
* `cons_step`: R's last cell is erased, a parser crosses R's hole and finds S's, the hole
  advances, a parser goes back to R's hole: `CL … (r − 1)`. `cons_loop`: down to `r = 1`, with
  `nxs` advances.
* `cons_entry`: from the end of the Horner run, three parsers to R's hole. `cons_done`: with
  `R = 101`, a parser finds S's hole and the head ends two cells left of it (state `k1`).

## Part 4: one base and the end of a round (`Round.lean`)

`IC n i j k p`: the start of a base (the Horner run at the exponent hole), I holding `i`, J with
`j` cells, K with `k`, S's hole at `p`. `gJK` is the gap between I and S, `Lw` the tape left of
S, `tc` the head on I's last cell.

* `run_cons`: the Horner run, `cons_entry` and `cons_loop`: from `IC n i j k p` to `R = 101`
  with S's hole `nxs n p (i^(n−1) − 1)`.
* `check_zero` (S's hole at cell 1: two scans to I's last cell) and `check_flag` (otherwise:
  the flag cells rewritten, `J` one cell longer if `K` had 2 cells, then to I's last cell).
* `shift`: for `i ≥ 3`, I's last cell joins the separator, J gets a cell, and two parsers reach
  the exponent hole: `IC n (i − 1) (j + 1) k p`.
* For `i = 2`: `round_pz` (I's hole and the I/J separator filled, a parser to S's hole);
  `round_halt` (S's hole at cell 1 and `K = 1`: the next steps reach `halt`); `round_a` and
  `round_b` (to S's cell 1, filling S's hole when it was elsewhere); `round_reset`: right to
  left, the fixed pattern of S's new start, K, J and the separators, then over the filled region
  to N, which gives two cells to I and grows by three on its left: `IC (n + 1) n 1 2 1`.

## Part 5: the main loop (`Main.lean`)

* `It n m`: round `n` after `m` bases: `IC n (n − 1 − m) (m + 1 + flag) (2 − flag)
  (gsum n m % n + 1)` with `flag = fl n m`.
* `hole_next`: S's new hole is at `gsum n (m + 1) % n + 1` (`nxs_mod`).
* `base_run`: `run_cons`, `cons_done` and the check give `tc` with the new `B` and flag, in at
  least one step. `base`: for `i ≥ 3`, `It n m` reaches `It n (m + 1)`.
* `last`: at `i = 2`, `Bad n` gives `HaltAt (It n m)`; otherwise `It (n + 1) 0` is reached.
* `seed_reach`: the seed writes the end of round 3 and the reset gives `It 4 0`.
* `halts_iff`: (→) if the conjecture holds, no `n` is bad, so every base and every round leads
  on and `not_halts_of_progress` shows the machine never halts. (←) a counterexample gives a bad
  `N ≥ 4` (`bad_iff`); `to_last` and `halt_from` run the rounds from 4 up to `N`, and the machine
  halts there at the latest (`haltAt_of`).
