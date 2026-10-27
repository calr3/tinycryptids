# The proof, in plain words

This is a guided tour of the Lean proof that the 17-state design `fermatprimesinf.txt` and the
16-state machine `machines/fermatprimesinf_16.txt` quasihalt iff there are only finitely many
Fermat primes. The proof is about 500 hand-written lines in
`../lean/TinyCryptids/FermatPrimesInf/` (`Tac`, `Round`, `Spec`, `Main`; `Machine` and `M16`
are generated). Almost all of it is assembled from two earlier proofs:

* `../twinprimes`'s (`../lean/TinyCryptids/TwinPrimes/`): the beeping argument;
* `../fermatprimes`'s (`../lean/TinyCryptids/FermatPrimes/`): the arithmetic (`Good`, `FP`,
  `fp_iff'`, `fail_iff`, imported) and the check (`check_last`, `check_first`, `check_ok`).

Each step below names the lemma that carries it. `../twinprimes/PROOF.md` and
`../fermatprimes/PROOF.md` explain the shared lemmas in more detail.

## What is proved

```lean
theorem TM.FermatPrimesInf.quasihalts_iff :
    QuasiHalts delta St.G0 false start ↔ ¬ InfinitelyManyFermatPrimes
theorem TM.FermatPrimesInf.never_halts : ¬ Halts delta start
theorem TM.FermatPrimesInf.beeps_forever_iff :
    (∀ N, ∃ n, N ≤ n ∧ BeepsAt delta St.G0 false start n) ↔ InfinitelyManyFermatPrimes

theorem TM.FermatPrimesInf.M16.quasihalts_iff :
    QuasiHalts delta2 St2.G0 false start2 ↔ ¬ InfinitelyManyFermatPrimes
theorem TM.FermatPrimesInf.M16.never_halts : ¬ Halts delta2 start2
```

* `delta` is the design and `delta2` the merged machine, generated from the text files. Each
  has its own `start` on a blank tape.
* `BeepsAt` and `QuasiHalts` are those of `Core/Beep.lean`: step `n + 1` is the beep, and from
  some `N` on no step is.
* `InfinitelyManyFermatPrimes := ∀ n, ∃ k, n ≤ k ∧ Prime (2 ^ 2 ^ k + 1)` (`Defs.lean`), with
  the repository's `Prime`.

Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## The idea of the proof

Candidate `m` (odd, `m ≥ 5`) starts at `CS m` (the start of the mod walk for `d = 3`):

* if `m` is a pass (`FP m`: `m` prime and `m − 1` a power of 2), the run reaches
  `BeepCfg (m − 1)` (`G0` on the blank after a block of `m − 1` ones), takes the beep there,
  and reaches `CS (m + 2)`;
* otherwise the run reaches `CS (m + 2)` without ever being at the beep.

Every routine is proved for `deltaNB`, the design without its beep transition; only the beep
step (`beep_step`) uses `delta`. The start reaches `BeepCfg 2`, the beep for `m = 3` (`seed`).

## Part 1: arithmetic (`Spec.lean`, and `../FermatPrimes/Spec.lean`)

* `Good m e`: `e` divides neither `m` nor `m − 1`. `FP m`: `m` is prime and `m = 2^k + 1`.
* **`fp_iff'`** (from `../fermatprimes`): for odd `m ≥ 5`, `FP m` iff every odd `e` with
  `3 ≤ e ≤ m − 2` is good.
* **`fpi_iff`**: `InfinitelyManyFermatPrimes` iff the passes are unbounded. A Fermat prime
  `2^(2^k) + 1` is a pass, and `2^(2^k) > 2^k > k`. Conversely, a pass `m = 2^k + 1` has
  `k = 2^j` (`prime_pow_two_add_one`, from `../fermatprimes`); if `m > 2^(2^n) + 1` then
  `j ≥ n`, since `2^(2^j)` grows with `j`.

## Part 2: the machine on the tape (`Round.lean`)

The checkpoints: `W d r c k` (mod walk, `k` of `r` steps done),
`WS d r` (its start), `CS m = WS 3 (m − 4)`, `BeepCfg n`.

* **`walk_step`, `walk`, `walk_all`** (as in `../fermatprimes`): `WS d r` reaches
  `W d r (r % d) r`.
* **`walk_end`**: `E` erases R's last cell, `V` fills the separator, `X1` reads D's last cell.
* **The check** (as in `../fermatprimes`, with nothing right of R):

  | D's hole | what the machine does | lemma |
  |---|---|---|
  | `c + 1 = d` (`d ∣ m`) | `X1` fills the hole; `C4` on the separator | `check_last` |
  | `c = 0` (`d ∣ m − 1`) | `X1`, `X` erase to the hole; `Q` reads the blank left of D; `HF` refills and turns back | `check_first` |
  | `1 ≤ c ≤ d − 2` | `Q` reads a 1; `H1` refills; `G0` reads R's cell 0 after a block of `d + 1` ones | `check_ok` |

  **`check_fail`** joins the first two with the rebuild: both reach `CS (m + 2)`.
* **`shift`**: `G0` writes the separator; the walk for `d + 2` starts with `r − 2`. If R is
  empty, the configuration is `BeepCfg (d + 1)`.
* **`rebuild`**: `C4` in a block of `a + b` ones writes `1 1` at its left end and `G0` the
  separator: `CS (a + b + 3)`.
* **`beep_step`** (with `delta`): `G0` reads 0, moves left into the block as `C4`. **`seed`**:
  `C4`, `H1`, `H1` on a blank tape reach `BeepCfg 2`.

## Part 3: the main theorem (`Main.lean`)

* **`fail_iff`** (from `../fermatprimes`): after the walk the hole is on `c = r % d`, and
  `¬ Good (d + r + 1) d ↔ c + 1 = d ∨ c = 0`.
* **`test`**: by induction on `t`, with `r = 2 t + 1` and `m = d + r + 1`. If every odd `e < d`
  is good, `WS d r` reaches `BeepCfg (m − 1)` when every odd `e` with `d ≤ e ≤ m − 2` is good,
  and `CS (m + 2)` otherwise. For the last divisor (`t = 0`, `d = m − 2`) the hole is on cell 1,
  so it always passes.
* **`cand_fp`, `cand_not`, `after_beep`, `cand_step`, `reach_cs`**: a pass reaches
  `BeepCfg (m − 1)` and, after the beep and the rebuild, `CS (m + 2)`; any other candidate
  reaches `CS (m + 2)` with `deltaNB`. Each of these runs is at least one step (`CS_ne`), so
  `CS (2 k + 5)` is reached after at least `k` steps.
* **`never_halts`**: every `CS m` strictly reaches `CS (m + 2)` (`not_halts_of_progress`).
* **`quasihalts_iff`**. (→) If no beep comes after step `N` but the passes are unbounded
  (`fpi_iff`), a pass `m ≥ 2 N + 5` (odd: `FP.odd`) beeps after step `N`. (←) If no pass is
  `≥ N`, `deltaNB` runs from `CS (2 N + 5)` forever, so `delta` never beeps after reaching it
  (`quasihalts_of_sub`).

## Part 4: the 16-state machine (`M16.lean`)

`gen_reduced_lean.py` emits the merged table `delta2`, the state map `phi`, `compat`, `excl`
(only `G0` maps to the merged beep state) and `beep_transition`, and carries `quasihalts_iff`
and `never_halts` over with `quasihalts_iff_of_sim` and `not_halts_of_sim`.

## What the proof does not cover

* Whether there are infinitely many Fermat primes: that is the open problem. The proof shows
  that the machine beeps exactly once per Fermat prime.
* Running time: the beep for 257 comes at step 14,613,466; the one for 65537 is out of reach of
  simulation. Nothing in the proof depends on speed.
* That the Lean `delta2`, `machines/fermatprimesinf_16.txt`, the standard text in `README.md`
  and the annotated listing are the same machine rests on the generator scripts, not on Lean.
