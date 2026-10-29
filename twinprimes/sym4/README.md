# A 4-symbol beeping Turing machine for the twin prime conjecture

**`machines/twinprimes4_10.txt`, a 10-state, 4-symbol beeping Turing machine with 27
instructions** (named-state format, see `../../tools/tm.py`; readable:
`machines/twinprimes4_10_annotated.txt`). Started on a blank tape, it never halts, and it
**quasihalts iff the twin prime conjecture is false**: it takes its beep transition only
finitely often iff there are only finitely many primes `p` with `p + 2` prime.

The 2-symbol machine of `..` has 18 states and 34 instructions. With two more symbols the same
algorithm needs 27 instructions.

**The beep is the transition of state `beep` reading 0** (`J` in the standard text). It is
taken once at step 2 and then once for every lesser twin prime `p` other than 5, in order: 3,
11, 17, 29, 41, 59, 71, 101, … Neither difference changes whether the beeps run out.

Standard text (bbchallenge format, `---` = unused; symbols 0–3):

    3RI1LA---1RA_0LC1RB1LC3RB_---2LD1RA3LG_---1LD3RE3LD_---1LF2LF2RB_0RE---3RI3LF_------3RI3LH_------1RA3LF_1RJ2RB---3RI_0LA---------

**Beep: `J` reading 0 → write 0, move left, go to `A`.**

## What is proved

Lean (`../../lean/TinyCryptids/TwinPrimes4/`, core Lean 4.15.0, no Mathlib; the 4-symbol
model is `Core/Multi.lean`, the beep notions `Core/BeepK.lean`):

    theorem TMK.TwinPrimes4.quasihalts_iff :
        QuasiHalts delta St.beep 0 start ↔ ¬ TwinPrimeConjecture
    theorem TMK.TwinPrimes4.never_halts : ¬ Halts delta start
    theorem TMK.TwinPrimes4.beeps_forever_iff :
        (∀ N, ∃ n, N ≤ n ∧ BeepsAt delta St.beep 0 start n) ↔ TwinPrimeConjecture

`BeepsAt`, `QuasiHalts` and `TwinPrimeConjecture` are as in `..` (`Core/Beep.lean`, with
`Nat` symbols in place of `Bool`). All three theorems depend only on `propext`,
`Classical.choice` and `Quot.sound` (`../../lean/Check.lean`).

## How it works

The algorithm is that of the 2-symbol machine (`../README.md`). Candidates `m` are tested by
trial division with `d = 2, 3, …`, and one mod walk per `d` tests both `m` and `m + 2`. The
extra symbols remove the separator between D and R.

Symbols: `0` blank, `1` an R cell, `2` the D marker or the R cursor, `3` a D cell. Tape (blank
elsewhere):

    D R

* **D** has `d` cells, all 3 except the **marker** 2 on cell `c`, a counter mod `d`.
* **R** has `r = m − d` cells, all 1; during the walk the **cursor** 2 moves left through it.

Every scan passes 1s and 3s and stops at a 2 or a blank, so there are no zero-counting
scanners.

* **Walk.** The marker starts on D's last cell. `r` times: `cur` makes the cursor one cell
  further left (R's last cell first), `toM` runs left to the marker, and `adv` moves it one cell
  right. Past D's last cell `adv` reads R's cell 0, a 1 or the cursor, and `wrap` puts the marker
  on cell 0. `toR` then runs right to the cursor and fills it. The marker ends on cell
  `(m − 1) mod d`.
* **Check.** When `cur` reaches D's last cell, the marker there means `d ∣ m`, and on cell `d − 3`
  (`chk3`) it means `d ∣ m + 2`: **FAIL**. On `d − 2` (`chk2`), or further left (`wrap` runs to
  it), `d` passed.
* **Shift** `d := d + 1`, `r := r − 1`. The marker is erased, and `grow` runs right and makes R's
  cell 0 the marker, which is D's new last cell. `toR` runs to R's end and the walk starts.
* **Rebuild** (FAIL). `reb` turns D's 3s into 1s with a zigzag (`3 → 1 R`, then back left over
  the 1), writes a 3 on the blank left of the tape, and `grow` makes the next cell the marker:
  `D = 3 2`, `R = 1^(m−1)`. This is candidate `m + 1`.
* **Beep.** If R is empty after a shift, then `d = m` and every `d < m` passed. The walk ends at
  once and the check fails (`m ∣ m`). `reb` then reads the blank right of D, writes a 3 there,
  `grow` writes a 1, and `beep` reads the next blank: the **beep**. The rebuild that follows
  makes candidate `m + 3`. Skipping `m + 1` and `m + 2` loses nothing for `m ≥ 5`: `m + 1` is
  even, and `m`, `m + 2`, `m + 4` cannot all be prime unless `m = 3`. After 3 the twin prime 5
  is skipped.
* **Start.** On the blank tape, `reb` takes the beep path with an empty D, beeping at step 2,
  and the rebuild makes candidate 3. No instruction is spent on a seed.

| state | role | 0 | 1 | 2 | 3 |
|---|---|---|---|---|---|
| `reb` | rebuild | new D cell | | – | 3 → 1, zigzag |
| `toR` | run right to the cursor | R's end: walk | | fill the cursor | |
| `cur` | move the cursor / check `d − 1` | – | cursor | FAIL (`d ∣ m`) | check `d − 2` |
| `toM` | run left to the marker | – | | erase it | |
| `adv` | advance the marker | – | wrap | wrap | the marker |
| `wrap` | wrap / run to the marker | D's cell 0 | – | erase it: shift | |
| `chk2` | check `d − 2` | – | – | shift | check `d − 3` |
| `chk3` | check `d − 3` | – | – | FAIL (`d ∣ m + 2`) | run to the marker |
| `grow` | shift / rebuild | beep path: a 1 | the marker | – | |
| `beep` | the beep | **BEEP** | – | – | – |

Compared with the 2-symbol machine (18 states, 34 instructions):

* With no separator, `cur` reads D's last cell itself (the first check), and `grow` writes the
  new marker straight onto R's cell 0.
* `toR` also runs to R's end at the start of each walk (no `SC`), and `wrap` also finds the
  marker after a passed check (no `H0`).
* `reb`'s zigzag also converts the two D cells right of a marker on `d − 3`.
* The beep test costs only the beep transition. `cur`'s FAIL goes right into `reb`, which finds
  either R's cell 0 (a 1: go left) or a blank (R is empty: the beep path, through `grow`'s
  0-transition, which is also the start).

`RECORDS.md` lists how the machine was found, including a local search that found no
26-instruction machine nearby.

## The proof (`../../lean/TinyCryptids/TwinPrimes4/`)

* `Tac.lean`: blocks `rp a n s` (`n` cells holding `a`), `cfgL`, one-step tactics and scans for
  `deltaNB` (the machine without its beep transition, so its runs never beep), and the steps on a
  blank cell.
* `Round.lean`: `Dp d c` (D read leftwards), `W d r c k` (the walk with `k` steps left), `ZS d r`
  (the start of the walk for `d`), `CS m`, `BeepAt n j`. The lemmas are `walk_step` and `walk`
  (the marker ends on `(c + k) % d`), `zig` and `rebuild` (the zigzag), `check_fail` and
  `check_ok`, `zs_beep` (R empty reaches the beep), `start_beep`, `beep_step` (the only step of
  `delta`) and `after_beep` (the candidate `n + j + 3`).
* `Main.lean`: `test` (induction on `r`, using `../Spec.lean`'s `fail_iff` and `twin_iff`),
  `cand_twin` and `cand_not`. Then `reach_cand`: every `m ≥ 3` is a candidate or lies just after a
  twin prime candidate. `twin_gap` shows that two lesser twin primes `q < p < q + 3` are 3 and 5,
  so every lesser twin prime other than 5 is reached (`reach_twin`), at a step that grows with it.
  (→) a twin prime beyond `3N + 7` beeps after step `N`. (←) `deltaNB` never halts from a
  candidate beyond the last twin prime (`not_halts_of_progress`), so `quasihalts_of_sub`.

## Files and checks

| File | Contents |
|------|----------|
| `build.py` | The generator (`python3 build.py twinprimes4.txt`; variant `halt`: the beep replaced by a halt) |
| `twinprimes4.txt` = `machines/twinprimes4_10.txt` | The machine |
| `machines/twinprimes4_10_annotated.txt` | The machine with each state's role and the beep marked (`annotate.py twinprimes4.txt machines/twinprimes4_10_annotated.txt`) |
| `test_e2e.py` | Every check up to `m = 149` (921 divisors) against a Python model of `(m, d, c)` and the tape; the first 31 beeps (step 2, then the lesser twin primes 3, 11, …, 809, 1.6·10⁹ steps); the variant halts at step 3; 10⁸ steps without halting |
| `gen_lean.py` | Writes `../../lean/TinyCryptids/TwinPrimes4/Machine.lean` (`delta`, `deltaNB`, `start`) |
