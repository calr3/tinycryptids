# The proof, in plain words

This is a guided tour of the Lean proof that the machine halts if and only if Brocard's
conjecture fails. The proof is in `../lean/TinyCryptids/BrocardPrimes/`; each step below names
the lemma that carries it. The tape-level routines are `../legendre-sieve`'s (sweep, home, copy),
copied with their lemmas; what is new is the marker, the counter and the arithmetic of the split.

## What is proved

```lean
theorem TM.BrocardPrimes.halts_iff :
    Halts delta start ↔ ∃ p q, 3 ≤ p ∧ Prime p ∧ Prime q ∧ p < q ∧
      (∀ r, p < r → r < q → ¬ Prime r) ∧ primeCount (q ^ 2) - primeCount (p ^ 2) < 4
```

The merged machine's
theorem (`TM.BrocardPrimes.M72.halts_iff`) states the same thing for `delta2` and is transferred
from the design's (`M72.lean`, generated). Both depend only on `propext`, `Classical.choice` and
`Quot.sound` (`../lean/Check.lean`).

Tapes are streams seen from the head: `ones n s` is `n` ones followed by `s`, `blk a b s` a block
whose hole has `a` cells left of it and `b` right of it, `cfgL q s R` the machine in state `q`
reading the first cell of `s` (the cells left of the head are read leftwards).

## Part 1: arithmetic (`Arith.lean`, `Blocks.lean`)

* Primes in divisor form (`PrimeDvd`, `primeDvd_iff`); `not_prime_iff`: `m + 1` is composite iff
  a prime `≤ m` divides it; `prime_dvd_sq`: a prime dividing `k·k` is at most `k` (through
  `Nat.gcd`, core only).
* `primesDesc m`, the primes `≤ m` largest first, and `pc m` its length; `pc_eq_primeCount`
  links it to `primeCount`. `filter_split`, `filter_split_le`, `filter_single`: cutting the list
  at two thresholds; the only prime in `(t − 1, t]` is `t`.
* `lp n` is the largest prime `≤ n` (`lp_spec`), and `base n` the counter's base: `lp n ²` if
  `lp n ≥ 3`, else 1 (`base_le`).
* The split at the marker (`Blocks.lean`): `up m n` are the primes above `sv n = max n 2`, `lo m n`
  the others. `up_prime`/`lo_prime`, `up_comp`/`lo_comp`: a new prime joins `up`; `up_sq`,
  `lo_sq`: at a square whose root is not a prime `≥ 3` nothing moves; `up_bd`, `lo_bd`: at the
  square of a prime `n + 1 ≥ 3` it moves from the end of `up` to the front of `lo`;
  `up_not_dvd`: otherwise no prime of `up` divides `(n + 1)²`. `wraps_blocks`: the sweep ends in
  composite mode iff `m + 1` is composite.

## Part 2: the tape (`Tape.lean`)

`CW m n c` is the checkpoint tape as a list: `M`, `00`, the blocks of `up` (`upB`), the marker
`1 00`, the blocks of `lo` (`loB`), `0`, S (`sx`, `sy`: its hole), `0`, `1^(c+1)`. `chk m n c` is the
machine at the checkpoint (`chkW`, left of `M`). `sweep_all`: from the checkpoint, M grows and
the sweep crosses both zones (`zone`, from `Sweep.lean`, and `marker_cross`: the marker is
crossed like a separator), ending in the mode `wraps (upB m n) || wraps (loB m n)`.
`Clean3` lists (runs of at most three 0s) are crossed by the home routines (`Home4.cross`) and
by the trip to the right end (`rcross`).

## Part 3: the routines

* `SProc.lean`: `s_prime` (S's hole moves, K gets a 1, home to copy), `s_comp` (S's hole moves,
  home), `s_square` (S wraps: it grows by 2, K moves two cells, the scan starts).
* `Scan.lean`, `Left.lean`: the scan to the marker. `ls_blk` crosses one block leftwards,
  `ls_zone`/`ls_zone_b` a zone, `scan_K` the counter and S; `scan_all` ends on the cell left of the
  marker. `lf_home` (`Cycle.lean`): not at a prime square (the block left of the marker has a 1
  next to its guard, or there is no block, only `M`), the scan goes home to the next checkpoint.
* `Bound.lean`: `bd_shift`, the block of `q` (hole at its last index) moves three cells right and
  its old left guard becomes the marker; `rcross` to the right end; `e_reset` erases
  `1^(c+5)` down to one cell, `e_halt` halts on fewer.
* `Copy.lean`, `Home.lean`: copying `M` (`cpy_all`), going home (`home_chk`, `home_copy`).

## Part 4: one step (`Cycle.lean`)

The invariant `Inv m n c`: `m ≥ 2`, `n ≥ 1`, `n² ≤ m < (n + 1)²`, and `c = pc m − pc (base n)`,
the number of primes in `(base n, m]`. Five cases, each a lemma that reaches the next checkpoint
and re-establishes the invariant:

* `cyc_prime`: `m + 1` prime: `chk (m+1) n (c+1)`.
* `cyc_comp`: composite, not a square: `chk (m+1) n c`.
* `cyc_sq`: `m + 1 = (n + 1)²` with `n + 1` not a prime `≥ 3`: `chk (m+1) (n+1) c` (`base_sq`:
  the base does not change; at `n + 1 = 2` both bases are 1).
* `cyc_bd`: `m + 1 = (n + 1)²`, `n + 1 ≥ 3` prime, `c ≥ 4`: `chk (m+1) (n+1) 0` (via `reach_k`, the
  common part up to the right end).
* `cyc_halt`: the same with `c < 4`: `HaltAt`.

## Part 5: the main theorem (`Main.lean`)

`cycle` puts the cases together: the machine halts at checkpoint `m` exactly under `Stop m n c`
(`m + 1 = (n + 1)²`, `n + 1` prime, `n ≥ 2`, `c < 4`), and otherwise strictly progresses.
`seed_reach` and `inv_two`: the 24-cell seed reaches `chk 2 1 1`, with `c = 1 = pc 2 − pc 1`.
`stop_iff`: at a reachable checkpoint `Stop` holds iff `lp n` and `n + 1` are a counterexample.
For `lp n ≥ 3` the base is `lp n ²` and `c = pc (q² − 1) − pc (p²) = pc (q²) − pc (p²)`
(`pc_sq_pred`); `lp n = 2` forces `n = 2`, `m = 8` and `c = pc 8 − pc 1 = 4` (by `decide`), so the
square of 2 never counts. Then (→) by `not_halts_of_progress` over the reachable checkpoints, and
(←) by `haltAt_of_counterex`: `reach_all` reaches checkpoint `q² − 1`, where `n = q − 1`
(`isqrt_eq`) and `lp n = p` (`lp_eq`).
