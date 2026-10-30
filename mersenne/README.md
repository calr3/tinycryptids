# A beeping Turing machine for the Mersenne prime conjecture

**Current best: `machines/mersenne_14.txt`, a 14-state, 2-symbol beeping Turing machine.**
Started on a blank tape, it never halts, and it **quasihalts iff the Mersenne prime
conjecture is false**: it takes its beep transition only finitely often iff there are only
finitely many primes of the form `2^k − 1`.

**The beep is the transition of state `N` reading 0** (`0LA`, the first entry of the 14th
group in the standard text below; `G0` in the design and the Lean files). It is taken exactly
once for every Mersenne prime, in order: 3, 7, 31, 127, 8191, …

## Standard text (bbchallenge format, 14 states)

    1LM1LA_0LI0LC_0LD1LC_1RE1LD_0LF0RG_0RE1LF_0RH1RG_1RB1RH_1RM0LJ_1LK1LJ_1RA0LL_1RK0LK_1RM1RN_0LA0RB

States are `A`–`N` in order, `A` is the start state, and every transition is used.
**Beep: `N` reading 0 → write 0, move left, go to `A`.**

## What is proved

Lean (`../lean/TinyCryptids/Mersenne/`, core Lean 4.15.0, no Mathlib):

    theorem TM.Mersenne.M14.quasihalts_iff :
        QuasiHalts delta2 St2.G0 false start2 ↔ ¬ MersennePrimeConjecture
    theorem TM.Mersenne.M14.never_halts : ¬ Halts delta2 start2
    theorem TM.Mersenne.M14.beep_transition :
        delta2 St2.G0 false = some (false, Dir.L, St2.C4)

with (`../lean/TinyCryptids/Core/Beep.lean`, `../lean/TinyCryptids/Defs.lean`)

    def BeepsAt δ qb bb c n := ∃ c', run δ n c = some c' ∧ c'.q = qb ∧ c'.R 0 = bb ∧ δ qb bb ≠ none
    def QuasiHalts δ qb bb c := ∃ N, ∀ n, N ≤ n → ¬ BeepsAt δ qb bb c n
    def MersennePrimeConjecture := ∀ n, ∃ k, n ≤ k ∧ Prime (2 ^ k - 1)

`BeepsAt … n` says that step `n + 1` of the run is the beep transition (state `qb` reading
`bb`). `QuasiHalts` says that there is a last beep, or none. `Prime` is the repository's
definition (`2 ≤ p` and no `d` with `2 ≤ d < p` divides `p`). The 15-state design has the same
theorems (`TM.Mersenne.quasihalts_iff`, `never_halts`), plus `beeps_forever_iff`: it beeps
infinitely often iff the conjecture holds. All of them depend only on `propext`,
`Classical.choice` and `Quot.sound` (`../lean/Check.lean`).

`RECORDS.md` lists the machines and how each was obtained. `PROOF.md` walks through the
proof in plain words.

### Why a beeping machine

"There are infinitely many Mersenne primes" is a Π₂ statement: for every `n` there is a
`k ≥ n` with `2^k − 1` prime. No finite counterexample refutes it, so no machine *halts* iff
it is false. A beeping machine searches forever and beeps at each Mersenne prime, so it has a
last beep iff they run out (the Beeping Busy Beaver setting; see `../twinprimes/README.md`).
If `BBB(14)` were known, running this machine for `BBB(14)` steps would settle the conjecture.

## How it works

For odd `m ≥ 3`, **`m` is a Mersenne prime iff no odd `d` with `3 ≤ d < m` divides `m` or
`m + 1`.** No odd `d` divides `m` iff `m` is prime, since `m` is odd. No odd `d ≥ 3` divides
`m + 1` iff `m + 1` is a power of 2, since an odd prime factor `q` of `m + 1` has
`q ≤ (m + 1)/2 < m`. So the machine needs no doubling and no power test. It tests
`m = 5, 7, 9, …` in turn by trial division with `d = 3, 5, 7, …`, and **one mod walk per
divisor tests both numbers**. The start beeps for `m = 3`.

Tape (blank left of D and right of R):

    D 0 R

* **D** has `d` cells, all 1 except a **hole** (a single 0) at cell `c`, a counter mod `d`.
  Before a walk the hole is on cell 0, which is **the blank cell left of D's `d − 1` ones**.
  So D grows by one cell on its left for free whenever `d` grows.
* A single 0 separates D and R.
* **R** has `r` cells, `d + r = m − 1`; during the walk a hole moves right through it.

Holes are found by scanners that count zeros, as in `../twinprimes`. From one block, a scanner
passes the separator and stops at the next 0.

* **Walk.** `r` times: make the next R cell the R hole (R's cell 0 first), scan left to D's
  hole and move it one cell right (from the last cell back to cell 0), scan right to the R
  hole and fill it. D's hole ends on cell `c = r mod d = (m − 1) mod d`. So `d ∣ m` iff
  `c = d − 1`, and `d ∣ m + 1` iff `c = d − 2`.
* **End of the walk.** `E` erases R's last cell (`r := r − 1`). `V` scans back and fills the
  separator. `X1` and `X2` alternate while they erase D's cells leftwards from cell `d − 1`
  until they meet the hole. Whichever state meets it fills it and moves right; from `X2`,
  `X1` refills one more cell. Then `C4` reads the next cell:
  * the filled separator (a 1): the hole was on `d − 1` or `d − 2`, so `d` divides `m` or
    `m + 1`: **FAIL**. `C4` carries on left: the rebuild.
  * an erased cell (a 0): **`d` passed**. `C4` writes 1 and steps back, `H1` steps on, `G0`
    erases the cell, `B2` reads the next erased cell and steps back, and `E` writes 1 there
    and steps on. Every cell is filled after this exchange. `H1` refills the remaining erased
    cells. The first 1 it meets is the old separator, which is now a cell of D. `G0`, on R's
    cell 0, writes the new separator. With the blank left of D as the next hole, `d` grows by
    2 and `r` shrinks by 2. If R is empty instead, `d = m − 2` was the last odd divisor and
    every one passed: **BEEP**.
* **Rebuild** (after a FAIL or the beep). The tape holds one block of `m − 1` ones. `C4` runs
  to its left end and writes a 1, `H1` writes another, and `G0` writes the separator after
  them. That gives `D = 1 1` with its hole on the blank (`d = 3`) and `R = m − 2` ones: the
  candidate `m + 2`.
* **Start.** `C4` and `H1` write `1 1` on the blank tape, and `G0` reads the blank after them.
  That is the beep for `m = 3` (a block of `m − 1 = 2` ones), and the rebuild follows.

The 15-state design (`mersenne.txt`, from `build.py`) is: walk 8 (two scanners of 2 states,
the R step, the D step, the wrap 2), end of the walk and check 4, shift and rebuild 3.
Merging (`../tools/minimize_clique.py … G0:0`) joins the wrap's last state with the D step:
14 states. The clique bound is also 14, so this is optimal for the design. Every transition of
the merged machine is used. The merger keeps the beep exclusive: no state that reads 0 may
share the beep state's class.

### How the design was found

The walk is the one from `../twinprimes`. The round end (everything except the 7 walk states)
was found by **SAT synthesis**. The walk was fixed, and `k` free states were given any
transitions. A solver then had to reproduce every round end of a working design: for each
`(m, d)` with `m ≤ 31`, from the walk's end to the next walk's start, with the beep exactly
where it belongs. `k = 8` gave a first 15-state machine. `k = 7` gave this one, which
generalises (the beeps at 3, 7, 31, 127 and every round up to `m = 201` match). `k = 6` is
unsatisfiable within the step bounds. `RECORDS.md` has the history and the limits of that search
(`../tools/synth_round.py`).

## Files and checks

| File | Contents |
|------|----------|
| `build.py` | The generator of the design (variant `halt`: the beep replaced by a halt) |
| `mersenne.txt` = `machines/mersenne_15.txt` | The 15-state design |
| `machines/mersenne_14.txt`, `_annotated.txt` | The merged machine, and the same machine with each state's roles and the beep marked |
| `test_e2e.py` | Every walk start and every check up to `m = 201` (372 divisors) against a Python model of `(m, d, c)` and the tape; the beeps at 3, 7, 31, 127 with the tape at each beep, and no other beep in 10¹⁰ steps (8191 is out of reach: some candidates below it take about `m³` steps); the variant halts at `m = 3`; 10⁸ steps without halting |
| `gen_lean.py`, `gen_reduced_lean.py`, `annotate.py` | `Machine.lean` (`delta` and `deltaNB`, the design without its beep), `M14.lean`, the annotated listing |

Shared tools: `../tools/sim.c` and `../tools/tm.py` report beep transitions
(`tm.run(…, beep=('G0', 0), maxtrace=k)`). `../tools/minimize_clique.py in out timeout solver
G0:0` merges states and keeps the beep exclusive. `../tools/same_run.py` checks that the
merged machine has the design's tapes (10³ … 10⁸ steps).
