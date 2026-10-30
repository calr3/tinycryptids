# The proof, in plain words

This is a guided tour of the Lean proof that the 15-state design `mersenne.txt` and the
14-state machine `machines/mersenne_14.txt` quasihalt iff the Mersenne prime conjecture is
false. The proof is about 600 hand-written lines in `../lean/TinyCryptids/Mersenne/` (`Tac`,
`Round`, `Spec`, `Main`; `Machine` and `M14` are generated), on top of
`../lean/TinyCryptids/Core/Beep.lean` (the beeping semantics, for any machine, shared with
`../twinprimes`). Each step below names the lemma that carries it.

## What is proved

```lean
theorem TM.Mersenne.quasihalts_iff :
    QuasiHalts delta St.G0 false start ↔ ¬ MersennePrimeConjecture
theorem TM.Mersenne.never_halts : ¬ Halts delta start
theorem TM.Mersenne.beeps_forever_iff :
    (∀ N, ∃ n, N ≤ n ∧ BeepsAt delta St.G0 false start n) ↔ MersennePrimeConjecture

theorem TM.Mersenne.M14.quasihalts_iff :
    QuasiHalts delta2 St2.G0 false start2 ↔ ¬ MersennePrimeConjecture
theorem TM.Mersenne.M14.never_halts : ¬ Halts delta2 start2
```

* `delta` is the design and `delta2` the merged machine, generated from the text files. Each
  has its own `start` on a blank tape. The model (`Core/Basic.lean`, shared by every machine in
  the repository) has 2 symbols, a two-way infinite tape, and a head that always moves.
* `BeepsAt δ qb bb c n`: after `n` steps from `c` the machine is in state `qb` reading `bb`,
  and that transition exists, so step `n + 1` is the beep. `QuasiHalts δ qb bb c`: from some
  `N` on, no step is the beep (`Core/Beep.lean`).
* `MersennePrimeConjecture := ∀ n, ∃ k, n ≤ k ∧ Prime (2 ^ k - 1)` (`Defs.lean`), with the
  repository's `Prime`.

To trust the result you need the Lean kernel, these definitions, and the listing of the
machine. Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## The idea of the proof

Candidate `m` (odd, `m ≥ 5`) starts at a configuration `CS m` (the start of the mod walk for
`d = 3`). There are two cases:

* `m` is a Mersenne prime: the run reaches `BeepCfg (m − 1)` (state `G0` on the blank after a
  block of `m − 1` ones), takes the beep transition there, and reaches `CS (m + 2)`;
* otherwise: the run reaches `CS (m + 2)` **without ever being at the beep**.

As in `../twinprimes`, every routine is proved for `deltaNB`, the design with its beep
transition removed. A run of `deltaNB` is a run of `delta` that never passes the beep
(`deltaNB_sub`, `Reach.sub`). Only one step of the whole proof uses `delta` itself: the beep
(`beep_step`). The start is a short run to `BeepCfg 2`, the beep for `m = 3` (`seed`).

## Part 1: arithmetic (`Spec.lean`)

* `Good m e`: `e` divides neither `m` nor `m + 1`. `MP m`: `m` is prime and `m + 1` is a power
  of 2.
* **`odd_not_dvd_pow2`**: an odd `q ≥ 3` divides no `2 ^ k`. By induction on `k`: if
  `q · t = 2 ^ (k + 1)` then `t` is even (`q` is odd), so `q · (t / 2) = 2 ^ k`.
* **`pow2_of_no_odd`**: a number `n ≥ 1` without odd divisors `≥ 3` is a power of 2 (strong
  induction: halve an even `n`; an odd `n ≥ 3` divides itself).
* **`mersenne_iff`**: for odd `m ≥ 3`, `MP m ↔ ∀ e, 3 ≤ e → e < m → e odd → Good m e`. An even
  `e` cannot divide the odd `m`. An odd divisor `q ≥ 3` of `m + 1` with `q ≥ m` would be `m`
  (and `m ∤ m + 1`) or larger than `m + 1`.
* **`mpc_iff`**: the conjecture holds iff `MP` numbers are unbounded (`2 ^ k > k`, and
  `2 ^ k` grows with `k`).

## Part 2: the machine on the tape (`Round.lean`)

Tape `D 0 R` (blank on both sides): D has `d` cells with a hole at cell `c`, then one 0, then R
with `r` cells, `d + r = m − 1`. `Dp d c` is D read leftwards from its last cell. When `c = 0`
the hole is the blank cell left of D's ones. The checkpoints are:

| name | meaning |
|---|---|
| `W d r c k` | mod walk, `k` of `r` steps done: `B2` on R's cell `k` (or the blank after R when `k = r`), D's hole at `c`, R without a hole |
| `WS d r` | `W d r 0 0`: the walk's start, D's hole on cell 0, `B2` on R's cell 0 |
| `CS m` | `WS 3 (m − 4)`: candidate `m` |
| `BeepCfg n` | `G0` on the blank after a block of `n` ones |

**Lemma 1 (one step, `walk_step`).** `W d r c k` reaches `W d r ((c + 1) % d) (k + 1)`. `B2`
makes R's hole on cell `k`. A scanner (`Y1`, `Y2`) passes the separator to D's hole and fills
it. `A2` makes the next hole, or on the separator wraps (`W1` runs to the blank, `W2` puts the
hole on cell 0). A scanner (`Z1`, `Z2`) returns to R's hole, fills it, and steps right.

**Lemma 2 (the walk, `walk`, `walk_all`).** By induction, `WS d r` reaches `W d r (r % d) r`.

**Lemma 3 (end of the walk, `walk_end`).** With `r = j + 1`: `B2` reads the blank after R, `E`
erases R's last cell, and `V` scans back and fills the separator. `X1` then reads D's last
cell, and R (with the filled separator in front) has `j` cells.

**Lemma 4 (the check, `check_fail`, `check_ok`).** `X1` and `X2` erase D's cells leftwards,
alternating (`alt`: `2 i` cells), until one of them reads the hole and fills it.

| D's hole | what the machine does | lemma |
|---|---|---|
| `c + 1 = d` or `c + 2 = d` | `C4` reads the filled separator: rebuild, `CS (d + j + 4)` = `CS (m + 2)` | `check_fail` (+ `rebuild`) |
| `c + 3 ≤ d` | `C4` reads an erased cell; the erased cells are all refilled, `G0` reads R's cell 0 after a block of `d + 1` ones | `check_ok` (+ `ok_dance`) |

`ok_dance` covers the exchange after the hole is filled, with `k ≥ 2` erased cells left (the
first 0 is the head's cell). `C4` writes 1 and steps left, `H1` steps right, `G0` erases the
cell and steps right, `B2` reads the next 0 and steps left, and `E` writes 1 and steps right.
Then `H1` refills the other `k − 1` cells and meets the filled separator (`fillR`). The parity
of the distance from the hole to the separator decides which of `X1`, `X2` finds the hole.
Both cases end in the same configuration.

**Lemma 5 (the shift, `shift`).** If R has `j + 1 ≥ 1` cells, `G0` writes the separator on R's
cell 0 and `B2` starts the next walk: `WS (d + 2) j`. D gained the old separator and, as its
new cell 0, the blank on its left. If R is empty, the configuration is `BeepCfg (d + 1)`.

**Lemma 6 (the rebuild, `rebuild`).** `C4` in a block of `a + b` ones runs to the blank before
it and writes a 1. `H1` writes another 1 and moves right, and `G0` writes the separator after
these two: `CS (a + b + 3)`.

**Lemma 7 (the beep, `beep_step`; the seed, `seed`).** With `delta`, the beep transition
leads from `BeepCfg (n + 1)` to `C4` inside the block, and the rebuild follows. From a blank
tape, `C4`, `H1`, `H1` reach `BeepCfg 2`.

## Part 3: the main theorem (`Main.lean`)

**`fail_iff`.** After the walk the hole is on `c = r % d`, and for `d ≥ 3`,
`¬ Good (d + r + 1) d ↔ c + 1 = d ∨ c + 2 = d`. Write `r = q d + c`. Then
`(d + r + 1) % d = (c + 1) % d` and `(d + r + 2) % d = (c + 2) % d`.

**Lemma 8 (trial division, `test`).** By induction on `t`, with `r = 2 t + 1` and
`m = d + r + 1`. If every odd `e` with `3 ≤ e < d` is good, then `WS d r` reaches
`BeepCfg (m − 1)` if all odd `e` in `[d, m)` are good, and `CS (m + 2)` otherwise. The walk,
Lemma 3 and Lemma 4 decide `d` (`fail_iff`). Then Lemma 5 continues with `d + 2`, or ends in
the beep configuration when `t = 0`.

**Lemma 9 (one candidate, `cand_mp`, `cand_not`, `after_beep`).** From `CS m` (odd `m ≥ 5`): a
Mersenne prime reaches `BeepCfg (m − 1)` (`deltaNB`) and then `CS (m + 2)` (one beep step,
then `deltaNB` again). Any other `m` reaches `CS (m + 2)` with `deltaNB` (`mersenne_iff`).
`CS_ne` (the tapes differ at one cell) makes each of these runs at least one step long
(`cand_step`). So `reach_cs`: `CS (2 k + 5)` is reached after at least `k` steps.

**Never halts (`never_halts`).** Every `CS m` strictly reaches `CS (m + 2)`
(`not_halts_of_progress`).

**Quasihalts ⟹ the conjecture fails.** Suppose there is no beep after step `N`, and yet the
conjecture holds. Take a Mersenne prime `m ≥ 2 N + 5` (`mpc_iff`; it is odd, `MP.odd`). `CS m`
is reached after at least `(m − 5)/2 ≥ N` steps, and the beep follows it: a contradiction.

**The conjecture fails ⟹ quasihalts.** Take `N` with no Mersenne prime `m ≥ N`. From
`CS (2 N + 5)`, `deltaNB` goes from candidate to candidate forever (`cand_not`,
`not_halts_of_progress`). So it never halts, and `quasihalts_of_sub` says `delta` never beeps
after reaching `CS (2 N + 5)`.

## Part 4: the 14-state machine (`M14.lean`)

`gen_reduced_lean.py` emits the merged table `delta2`, the state map `phi`, `compat` (each
design transition is matched by `delta2` on `phi`), `excl` (only `G0` maps to the merged beep
state `G0`) and `beep_transition`. `quasihalts_iff_of_sim` and `not_halts_of_sim` carry
`quasihalts_iff` and `never_halts` over.

## What the proof does not cover

* It says nothing about whether there are infinitely many Mersenne primes; that is the open
  problem. It shows the machine beeps exactly once per Mersenne prime.
* Running time: trial division by every odd `d < m` in unary is slow. The beep for 127 comes
  at step 1,244,157; the one for 8191 is out of reach of simulation (a candidate `m` whose
  `m + 1` has no small odd factor costs about `m³` steps). Nothing in the proof depends on
  speed.
* That the Lean `delta2`, `machines/mersenne_14.txt`, the standard text in `README.md` and the
  annotated listing are the same machine rests on the generator scripts, not on Lean.
