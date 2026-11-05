# The proof, in plain words

This is a guided tour of the Lean proof that the Carmichael machine halts if and only if
Carmichael's totient conjecture fails. The proof is in `../lean/TinyCryptids/Carmichael/`; each
step below names the lemma that carries it.

## What is proved

```lean
theorem TM.Carmichael.halts_iff :
    Halts delta start ↔ ∃ m, 1 ≤ m ∧ ∀ n, n ≠ m → totient n ≠ totient m
```

`totient n` (`../lean/TinyCryptids/Defs.lean`) counts the `k < n` with `gcd k n = 1`: the usual
`φ`. The right-hand side is a counterexample to the conjecture: an `m ≥ 1` whose value `φ(m)` no
other `n` takes. The merged machine's theorem (`TM.Carmichael.M80.halts_iff`) states the
same thing for `delta2`, and is transferred from the design's (`M80.lean`).

To trust it you need the Lean kernel, the machine model (`../lean/TinyCryptids/Core/`) and
the listing of the machine. The theorem depends only on `propext`, `Classical.choice` and
`Quot.sound` (`../lean/Check.lean`).

## Part 1: arithmetic (`Spec.lean`)

* **The walk.** `hitC k r j` says the walk `0, k, 2k, …` (mod `r`) is at `1` after `j` steps,
  `hitN k r j` that it is at `0`. `first_hit`: at the first `j ≥ 1` where either holds, the walk
  is at `1` iff `gcd k r = 1`. If it is at `1`, any common divisor of `k` and `r` divides `1`.
  If `gcd k r = 1` and it is at `0`, then `r ∣ j` (`gauss`), so `j ≥ r`; but `k` has an inverse
  `i < r` (`inv_exists`: `j ↦ j k mod r` is injective on `[0, r)`, so it hits `1`), and the
  walk is at `1` after `i < j` steps, which contradicts "first". `hitN_r`: the walk is at `0`
  after `r` steps, so a first hit exists.
* **Counting.** `cp M K` counts the `k < K` with `gcd k M = 1`, so `cp M M = φ(M)`
  (`cp_self`), `cp M 1 = 0` for `M ≥ 2`, and `cp_succ` adds one `k`. `gcd_sub`:
  `gcd k (M - k) = gcd k M`, so testing `(k, M - k)` is testing `k` against `M`.
* **Windows.** `nm v N` counts the `M ≤ N` with `φ(M) = v`. `exists_iff`: if `W v ≥ 2 v²` for
  every `v ≥ 2`, a counterexample exists iff some `v ≥ 2` has `nm v (W v) = 1`. One direction
  uses `totient_bound` (`n ≤ 2 φ(n)²`, from `../lean/TinyCryptids/Carmichael/Totient.lean`) to
  put every `n` with `φ(n) = v` inside the window. In the other direction, `φ(m) ≥ 2` because
  `φ(1) = φ(2) = 1`.

## Part 2: one round on the tape (`Round.lean`)

The tape is `1 K 00 1 R 00 V 1 00 f 0 B 1`. `TK a b j e X` is the machine on K's hole with `a`
slots of K to its left and `b` to its right, R's hole with `j` slots to its left and `e` to its
right, and `X` for the rest of the tape.

* **Ticks.** `tick`: both holes move one slot right. `tickW`: the same, with R's hole wrapping
  from its last slot to its first. `tickg` and `ticks` restate this with R's hole at position
  `j mod r`.
* **Wraps.** When K's hole is on its last slot, the tick wraps it back to the first slot and
  checks R. In `wrapC`, R's hole is on its first slot: the pair is coprime. In `wrapN`, R's hole
  is on its last slot and wraps: the pair is not coprime. Otherwise (`wrapM`) the walk goes on.
* **The test.** `stride` follows one round of K's hole from the start of stride `q` (`SS`). It
  ends in the coprime result if the walk is at `1` after `q` strides, in the non-coprime result
  if it is at `0`, and otherwise at the start of stride `q + 1`; `mod_succ_eq` does the
  modular bookkeeping. `strides` and `test` chain the strides until the first hit and use
  `first_hit`: the test of `(k, r)` ends in `Res k r`, coprime iff `gcd k r = 1`.
* **The count.** `Vst v c` is V after `c` coprime pairs: the hole on slot `v + 1 - c`, or none
  for `c > v`. `coprime`: a coprime pair moves the hole one slot left, whether it falls off
  (`c = v`) or there is none. `test_count` combines the test and the count.
* **The sweep.** `shift`: `(k, r + 1) → (k + 1, r)`. `sweep`: from `k = 1`, the round tests every
  `k ≤ M - 1` and ends with `cp M M = φ(M)` pairs counted.
* **The round end.** `cross_match` handles V's hole on slot 1 (`φ(M) = v`) and
  `cross_nomatch` the other cases; both fill V's hole and reach the flag. `advance` moves
  B's hole one slot left, places V's hole on slot `v + 1`, and resets K/R with `reset`,
  `(M - 1, 1) → (1, M)`.
* **The next v.** `vg`: V gains a slot (the cursor) and B loses its first. `fill`, `append`,
  `grow_back`, `grow_last`, `grow`: each cursor step appends four slots to B. `kr_init` erases K/R
  back to `(1, 1)`. `rebuild1` (the window ended without a match) and `rebuild2` (a second match)
  reach `Start (v + 1) (s + 4v + 7)`. `seed`: from the blank tape to `Start 2 11`.

## Part 3: windows and the main theorem (`Main.lean`)

* `RS0 v M f s p` is the start of round `M` with flag `f` and B's hole on slot `p`. `round`
  runs the sweep. The six outcomes:
  * `r_first`: the first match, so set the flag and go to the next round.
  * `r_first_halt`: the first match in the last round, so halt.
  * `r_second`: a second match, so go to the next `v`.
  * `r_none`: no match, so go to the next round.
  * `r_none_halt`: no match in the last round, with the flag set, so halt.
  * `r_none_end`: no match in the last round, with the flag clear, so go to the next `v`.
* `loop`, `window`: the window of `v` runs `M = 2, …, s + 1` with the flag set iff exactly one
  earlier `M` matched. It halts iff `nm v (s + 1) = 1`, and otherwise strictly reaches the start
  of the next window.
* `sz`: the window sizes, `11` for `v = 2` and growing by `4v + 7`; `sz_bound` gives
  `sz + 1 ≥ 2 v²`.

(←) With a counterexample, `exists_iff` gives a `v` whose window has one match. `reach`: the
machine halts earlier or reaches that window, and `window` halts there (`haltAt_of`).

(→) Without a counterexample no window has exactly one match. So each window start strictly
reaches the next one, and none of them halts (`not_halts_of_progress`). The start reaches the
first window (`seed`), so it does not halt either.
