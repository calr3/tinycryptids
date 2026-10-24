# A beeping Turing machine for the twin prime conjecture

**Current best: `machines/twinprimes_18.txt`, an 18-state, 2-symbol beeping Turing machine.**
Started on a blank tape, it never halts, and it **quasihalts iff the twin prime conjecture is
false**: it takes its beep transition only finitely often iff there are only finitely many
primes `p` with `p + 2` prime.

**The beep is the transition of state `N` reading 0** (`0LB`, the first entry of the 14th
group in the standard text below; `G2` in the design and the Lean files). It is taken exactly
once for every lesser twin prime `p ≥ 3`, in order: 3, 5, 11, 17, 29, 41, 59, 71, 101, …

## Standard text (bbchallenge format, 18 states)

    1LB1RA_0LH0LC_0LD1LC_1RE1LD_0LF0RG_0RE1LF_0RA1RG_1RP1LI_1RL1LJ_1RP1LK_1RL1LK_0RM1RL_---0RN_0LB1RO_0LB1RO_1LQ1RP_1RR1LQ_---0RM

States are `A`–`R` in order, `A` is the start state, and `---` marks the two transitions the
run never uses (`M` and `R` reading 0). **Beep: `N` reading 0 → write 0, move left, go to `B`.**
`O` reading 0 has the same action, but it is not the beep.

## What is proved

Lean (`../lean/TinyCryptids/TwinPrimes/`, core Lean 4.15.0, no Mathlib):

    theorem TM.TwinPrimes.M18.quasihalts_iff :
        QuasiHalts delta2 St2.G2 false start2 ↔ ¬ TwinPrimeConjecture
    theorem TM.TwinPrimes.M18.never_halts : ¬ Halts delta2 start2
    theorem TM.TwinPrimes.M18.beep_transition :
        delta2 St2.G2 false = some (false, Dir.L, St2.B2)

with (`../lean/TinyCryptids/Core/Beep.lean`, `../lean/TinyCryptids/Defs.lean`)

    def BeepsAt δ qb bb c n := ∃ c', run δ n c = some c' ∧ c'.q = qb ∧ c'.R 0 = bb ∧ δ qb bb ≠ none
    def QuasiHalts δ qb bb c := ∃ N, ∀ n, N ≤ n → ¬ BeepsAt δ qb bb c n
    def TwinPrimeConjecture := ∀ n, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2)

`BeepsAt … n` says that step `n + 1` of the run is the beep transition (state `qb` reading
`bb`). `QuasiHalts` says that there is a last beep, or none. `Prime` is the repository's
definition (`2 ≤ p` and no `d` with `2 ≤ d < p` divides `p`). The 19-state design has the
same theorems (`TM.TwinPrimes.quasihalts_iff`, `never_halts`), plus `beeps_forever_iff`: it
beeps infinitely often iff the conjecture holds. All of them depend only on `propext`,
`Classical.choice` and `Quot.sound` (`../lean/Check.lean`).

`RECORDS.md` lists the machines and how each was obtained. `PROOF.md` walks through the
proof in plain words.

### Why a beeping machine

The twin prime conjecture is a Π₂ statement: "for every n there is a twin prime pair above
n". A machine that *halts* on a counterexample can only refute Π₁ statements (Goldbach,
Legendre, …): there is no finite counterexample to look for here. A beeping machine fits
Π₂: it searches forever and beeps at each twin prime pair, so it has a last beep iff the pairs
run out. This is the idea of A. Akinshin's note *Beeping Busy Beavers and the twin prime
conjecture* (2022), and this machine makes it concrete. Let `BBB(18)` be the most steps that
an 18-state machine with a designated beep transition runs before its last beep, taken over
the machines that quasihalt. If `BBB(18)` were known, running this machine for `BBB(18)` steps
would settle the conjecture. A beep after that point means the conjecture is true; none
means it is false. (Aaronson's Beeping Busy Beaver designates a beep *state*. A beep
*transition*, the form asked for here, is the same idea attached to one table entry.)

## How it works

For `m ≥ 3`, `m` and `m + 2` are both prime iff no `d` with `2 ≤ d ≤ m − 1` divides `m` or
`m + 2`. The machine tests `m = 3, 4, 5, …` in turn by trial division, and **one mod walk per
divisor tests both numbers**.

Tape (blank left of D and right of R):

    D 0 R

* **D** has `d` cells, all 1 except a **hole** (a single 0) at cell `c`, a counter mod `d`.
* A single 0 separates D and R.
* **R** has `r = m − d` cells; during the mod walk a hole moves left through it.

Holes are found by scanners that **count zeros**: from one block, pass the separator and stop
at the next 0. A parser that only detects a 0 between 1s (the 2-state parsers of
`../lean/TinyCryptids/Core/Lemmas.lean`) would need a 1 on
both sides of every hole. With the zero-counting scanners a hole may sit next to the separator
or at a block's end. That saves the extra end cells and the step from "one past the hole" back
onto it.

* **Walk.** D's hole starts on D's **last** cell. `r` times: make R's hole one cell further left
  (starting at R's last cell), scan left to D's hole and move it one cell right (from the last
  cell back to cell 0), scan right to R's hole and fill it. D's hole ends on cell
  `(d − 1 + r) mod d = (m − 1) mod d`.
* **Check**, reading D's cells `d − 1, d − 2, d − 3` from the separator: the hole on `d − 1`
  means `d ∣ m`, on `d − 3` means `d ∣ m + 2` (for `d = 2` both mean "m even"). Either is a
  **FAIL**. Otherwise `d` passed.
* **Shift** `d := d + 1`, `r := r − 1`: fill the hole. The separator stays 0 and becomes D's
  new last cell, which is exactly where the next walk's hole must start. R's cell 0 is erased
  and becomes the new separator. If R is now empty, `d = m` was reached and every `d` passed:
  **BEEP**. The beep's successor is the normal path: the walk with `r = 0` ends at once, the
  check sees the hole on D's last cell (`m` divides `m`), and the FAIL path follows.
* **Rebuild** (FAIL): fill the hole and the separator, write a 1 at the left end, then
  `D = 10` (`d = 2`, its hole on its last cell) and the separator. This is candidate `m + 1`.
* **Start.** The start state writes a 1 and runs the FAIL path once (a pseudo-round, no beep),
  which builds candidate 3. There are no seed states.

The 19-state design (`twinprimes.txt`, from `build.py`) is: walk 8 (two scanners of 2 states,
the R step, the D step, the wrap 2), check 4, shift and beep 4, rebuild 3. Merging
(`../tools/minimize_clique.py … G2:0`) joins the wrap's last state with the D step: 18 states.
The clique bound is also 18, so this is optimal for the design. The merger keeps the beep
exclusive: no state that reads 0 may share the beep state's class. So the merged machine takes
its beep transition exactly where the design takes it.

## Files and checks

| File | Contents |
|------|----------|
| `build.py` | The generator of the design (variant `halt`: the beep replaced by a halt) |
| `twinprimes.txt` = `machines/twinprimes_19.txt` | The 19-state design |
| `machines/twinprimes_18.txt`, `_annotated.txt` | The merged machine, and the same machine with each state's roles and the beep marked |
| `test_e2e.py` | Every check up to `m = 120` (621 divisors) against a Python model of `(m, d, c)` and the tape; the first 30 beeps at the first 30 lesser twin primes (3 … 659, 1.2·10⁹ steps); the variant halts at `m = 3`; 10⁸ steps without halting |
| `gen_lean.py`, `gen_reduced_lean.py`, `annotate.py` | `Machine.lean` (`delta` and `deltaNB`, the design without its beep), `M18.lean`, the annotated listing |

Shared tools: `../tools/sim.c` and `../tools/tm.py` report beep transitions
(`tm.run(…, beep=('G2', 0), maxtrace=k)` returns the step and tape of the first `k` beeps).
`../tools/minimize_clique.py in out timeout solver G2:0` merges states and keeps the beep
transition exclusive. `../tools/same_run.py` checks that the merged machine has the design's
tapes (10³ … 10⁹ steps).
