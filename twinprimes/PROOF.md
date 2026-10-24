# The proof, in plain words

This is a guided tour of the Lean proof that the 19-state design `twinprimes.txt` and the
18-state machine `machines/twinprimes_18.txt` quasihalt iff the twin prime conjecture is
false. The proof is about 650 hand-written lines: `../lean/TinyCryptids/Core/Beep.lean` (the
beeping semantics, for any machine) and `../lean/TinyCryptids/TwinPrimes/` (`Tac`, `Round`,
`Spec`, `Main`; `Machine` and `M18` are generated). Each step below names the lemma that
carries it.

## What is proved

```lean
theorem TM.TwinPrimes.quasihalts_iff :
    QuasiHalts delta St.G2 false start ↔ ¬ TwinPrimeConjecture
theorem TM.TwinPrimes.never_halts : ¬ Halts delta start
theorem TM.TwinPrimes.beeps_forever_iff :
    (∀ N, ∃ n, N ≤ n ∧ BeepsAt delta St.G2 false start n) ↔ TwinPrimeConjecture

theorem TM.TwinPrimes.M18.quasihalts_iff :
    QuasiHalts delta2 St2.G2 false start2 ↔ ¬ TwinPrimeConjecture
theorem TM.TwinPrimes.M18.never_halts : ¬ Halts delta2 start2
```

* `delta` is the design and `delta2` the merged machine, generated from the text files. Each
  has its own `start` on a blank tape. The model (`Core/Basic.lean`, shared by every machine in
  the repository) has 2 symbols, a two-way infinite tape, and a head that always moves.
* `BeepsAt δ qb bb c n`: after `n` steps from `c` the machine is in state `qb` reading `bb`,
  and that transition exists, so step `n + 1` is the beep. `QuasiHalts δ qb bb c`: from some
  `N` on, no step is the beep (`Core/Beep.lean`).
* `TwinPrimeConjecture := ∀ n, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2)` (`Defs.lean`), with the
  repository's `Prime`.

To trust the result you need the Lean kernel, these definitions, and the listing of the
machine. Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## The idea of the proof

Candidate `m` starts at a configuration `CS m` (the start of the mod walk for `d = 2`). There
are two cases:

* `m` and `m + 2` both prime: the run reaches `BeepCfg (m − 1)` (state `G2` on a blank),
  takes the beep transition there, and reaches `CS (m + 1)`;
* otherwise: the run reaches `CS (m + 1)` **without ever being at the beep**.

The second kind of run is proved for `deltaNB`, the design with its beep transition removed
(generated next to `delta` in `Machine.lean`). In fact every routine is proved for `deltaNB`.
A run of `deltaNB` is a run of `delta` (`run_sub`, `Reach.sub`, with
`deltaNB_sub : deltaNB ⊆ delta`), and it cannot pass through the beep configuration, because
`deltaNB` would halt there. Only one step of the whole proof uses `delta` itself: the beep
(`beep_step`).

## Part 1: beeping semantics (`Core/Beep.lean`, for any machine)

* **`run_sub`**: a machine `δ'` defined only where `δ` is, and agreeing there, runs as `δ`
  does.
* **`not_at_of_not_halts`**: if `δ'` has no transition on `(qb, bb)` and never halts from `c`,
  its run from `c` is never in state `qb` reading `bb`.
* **`quasihalts_of_sub`**: if `δ` reaches `c0`, and from `c0` the machine without its beep
  never halts, then `δ` quasihalts (no beep after the step that reached `c0`).
* **`beepsAt_iff_of_sim`, `quasihalts_iff_of_sim`, `not_halts_of_sim`**: a merged machine
  (`Compat`, as for `halts_iff_of_sim`) beeps at exactly the same steps as the design.
  This needs two facts. The design never halts. And every design state that `φ` maps to the
  merged beep state is the beep state itself, or never reads the beep symbol (`excl` in
  `M18.lean`, checked state by state).

## Part 2: the machine on the tape (`Round.lean`)

Tape `D 0 R` (blank on both sides): D has `d` cells with a hole at cell `c`, then one 0, then R
with `r` cells. `Dp d c` is D read leftwards from its last cell. The checkpoints are:

| name | meaning |
|---|---|
| `W d r c (k + 1)` | mod walk, `k + 1` steps left: `B2` on R's cell `k`, D's hole at `c`, R without a hole |
| `W d r c 0` | the walk is over: `B2` on the separator |
| `WS d r` | `W d r (d − 1) r`: the walk's start, D's hole on its last cell, `B2` on R's last cell |
| `CS m` | `WS 2 (m − 2)`: candidate `m` |
| `BeepCfg d` | `G2` on the blank after an empty R, D with `d + 1` cells and its hole on its last cell |

**Lemma 1 (one step, `walk_core`, `walk_step`).** `W d r c (k + 1)` reaches
`W d r ((c + 1) % d) k`. `B2` makes R's hole on cell `k`. A scanner (`Y1`, `Y2`) passes
the separator to D's hole and fills it. `A2` makes the next hole, or on the separator wraps
(`W1` runs to the blank, the hole goes on cell 0). A scanner (`Z1`, `Z2`) returns to R's hole
and fills it.

**Lemma 2 (the walk, `walk`).** By induction, `W d r c k` reaches `W d r ((c + k) % d) 0`.
From `WS d r` D's hole ends on `(d − 1 + r) % d`.

**Lemma 3 (the check, `check_fail`, `check_ok`).** From `W d r c 0`, `X1`, `X2`, `X3` read D's
cells `d − 1, d − 2, d − 3`:

| D's hole | what the machine does | lemma |
|---|---|---|
| `c + 1 = d` or `c + 3 = d` | fill it, rebuild: `CS (d + r + 1)` | `check_fail` (+ `rebuild`) |
| `c + 2 = d` or `c + 4 ≤ d` | fill it (`H0` finds it if it is further left): `H1` on its way right | `check_ok` |

**Lemma 4 (the shift, `shift_more`, `shift_beep`).** `H1` runs to the separator (it stays 0:
D's new last cell, the next hole), and `G1` erases R's cell 0 (the new separator). If `r ≥ 2`,
`G2` reads a 1 and `SC` starts the next walk: `WS (d + 1) (r − 1)`. If `r = 1`, R is now empty:
`BeepCfg d`.

**Lemma 5 (the rebuild, `rebuild`).** `C1` fills the separator. `C4` runs to the blank before
D and writes a 1 there (the tape grows by one cell). `C5` writes D's hole, `G1` the separator,
and `G2`, `SC` start the walk for candidate `m + 1`: `CS (a + b + r + 1)`.

**Lemma 6 (the beep, `beep_step`).** With `delta`: from `BeepCfg d` the beep transition leads
to `W (d + 1) 0 d 0`. The walk with `r = 0` has ended, and Lemma 3 fails it, since the hole is
on D's last cell.

**Lemma 7 (the seed, `seed`).** `Z2` on a blank tape writes a 1. `B2` and `X1` take the FAIL
path, and `rebuild` builds `CS 3`.

## Part 3: arithmetic (`Spec.lean`)

* `Good m e`: `e` divides neither `m` nor `m + 2`.
* **`fail_iff`**: for `d ≥ 2`, `¬ Good m d ↔ c + 1 = d ∨ c + 3 = d` with `c = (m − 1) % d`.
  Write `m − 1 = qd + c`; then `m % d = (c + 1) % d` and `(m + 2) % d = (c + 3) % d`, and
  `c + 3 = 2d` only when `d = 2, c = 1`.
* **`twin_iff`**: for `m ≥ 3`, `Prime m ∧ Prime (m + 2) ↔ ∀ e, 2 ≤ e → e < m → Good m e`. The
  divisors `m` and `m + 1` of `m + 2` need no test: they leave remainders 2 and 1.

## Part 4: the main theorem (`Main.lean`)

**Lemma 8 (trial division, `test`).** By induction on `r`: if every `e` with `2 ≤ e < d` is
good for `m = d + r`, then `WS d r` reaches `BeepCfg (m − 1)` if all `e` in `[d, m)` are good,
and `CS (m + 1)` otherwise. The walk and Lemma 3 decide `d` (`fail_iff`). Then Lemma 4
continues with `d + 1`, or ends in the beep configuration when `r = 1`.

**Lemma 9 (one candidate, `cand_twin`, `cand_not`, `after_beep`).** From `CS m` (`m ≥ 3`): a
twin prime reaches `BeepCfg (m − 1)` (`deltaNB`) and then `CS (m + 1)` (one beep step, then
`deltaNB` again). Any other `m` reaches `CS (m + 1)` with `deltaNB`. `CS_ne` (the tapes differ
at one cell) makes each of these runs at least one step long (`cand_step`). So `reach_cs`:
`CS (k + 3)` is reached after at least `k` steps.

**Never halts (`never_halts`).** Every `CS m` strictly reaches `CS (m + 1)`
(`not_halts_of_progress`).

**Quasihalts ⟹ the conjecture fails.** Suppose there is no beep after step `N`, and yet the
conjecture holds. Take a twin prime `p ≥ N + 3`. `CS p` is reached after at least `p − 3 ≥ N`
steps, and the beep follows it: a contradiction.

**The conjecture fails ⟹ quasihalts.** Take `N` with no twin prime `p ≥ N`. From
`CS (N + 3)`, `deltaNB` goes from candidate to candidate forever (`cand_not`,
`not_halts_of_progress`), so it never halts, and `quasihalts_of_sub` says `delta` never beeps
after reaching `CS (N + 3)`.

## Part 5: the 18-state machine (`M18.lean`)

`gen_reduced_lean.py` emits the merged table `delta2`, the state map `phi`, `compat` (each
design transition is matched by `delta2` on `phi`), `excl` (only `G2` maps to the merged beep
state `G2`) and `beep_transition`. `quasihalts_iff_of_sim` and `not_halts_of_sim` (Part 1)
carry `quasihalts_iff` and `never_halts` over.

## What the proof does not cover

* It says nothing about whether the twin prime conjecture is true; that is the open
  problem. It shows the machine beeps exactly as often as there are twin primes.
* Running time: trial division by every `d < m` in unary is slow (the 30th beep, at `p = 659`,
  comes after 1.2·10⁹ steps). Nothing in the proof depends on speed.
* That the Lean `delta2`, `machines/twinprimes_18.txt`, the standard text in `README.md` and
  the annotated listing are the same machine rests on the generator scripts, not on Lean.
