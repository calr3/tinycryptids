# A beeping Turing machine for the Sophie Germain primes

**Current best: `machines/sophiegermain_17.txt`, a 17-state, 2-symbol beeping Turing machine.**
Started on a blank tape, it never halts, and it **quasihalts iff there are only finitely many
Sophie Germain primes**: it takes its beep transition only finitely often iff only finitely
many primes `p` have `2p + 1` prime.

**The beep is the transition of state `Q` reading 0** (`0LK`, the first entry of the 17th
group in the standard text below; `G0` in the design and the Lean files). It is taken exactly
once for every Sophie Germain prime `p ≥ 3`, in order: 3, 5, 11, 23, 29, 41, 53, 83, 89, …
(`p = 2` is the only one it skips).

## Standard text (bbchallenge format, 17 states)

    0LJ0LB_0LC1LB_1RD1LC_0LG1RE_0LF0RH_0RE1LF_0RD1LG_0RI1RH_1RA1RI_0LK0RA_0LL1LK_1RM1LL_1RQ1RN_1RK1RO_1LK1RP_1RQ1RP_0LK0RA

States are `A`–`Q` in order, `A` is the start state, and every transition is used (34
instructions). **Beep: `Q` reading 0 → write 0, move left, go to `K`.**

## What is proved

Lean (`../lean/TinyCryptids/SophieGermain/`, core Lean 4.15.0, no Mathlib):

    theorem TM.SophieGermain.M17.quasihalts_iff :
        QuasiHalts delta2 St2.G0 false start2 ↔ FinitelyManySophieGermainPrimes
    theorem TM.SophieGermain.M17.never_halts : ¬ Halts delta2 start2
    theorem TM.SophieGermain.M17.beep_transition :
        delta2 St2.G0 false = some (false, Dir.L, St2.V)

with (`../lean/TinyCryptids/Core/Beep.lean`, `../lean/TinyCryptids/Defs.lean`)

    def BeepsAt δ qb bb c n := ∃ c', run δ n c = some c' ∧ c'.q = qb ∧ c'.R 0 = bb ∧ δ qb bb ≠ none
    def QuasiHalts δ qb bb c := ∃ N, ∀ n, N ≤ n → ¬ BeepsAt δ qb bb c n
    def SophieGermainPrime p := Prime p ∧ Prime (2 * p + 1)
    def FinitelyManySophieGermainPrimes := ∃ N, ∀ p, SophieGermainPrime p → p < N

`BeepsAt … n` says that step `n + 1` of the run is the beep transition (state `qb` reading
`bb`). `QuasiHalts` says that there is a last beep, or none. `Prime` is the repository's
definition (`2 ≤ p` and no `d` with `2 ≤ d < p` divides `p`). The machine is the design
itself (`sophiegermain.txt`, states in the same order), so the design has the same theorems
(`TM.SophieGermain.quasihalts_iff`, `never_halts`), plus `beeps_forever_iff`: it beeps
infinitely often iff for every `N` there is a Sophie Germain prime `p ≥ N`. All of them depend
only on `propext`, `Classical.choice` and `Quot.sound` (`../lean/Check.lean`).

`RECORDS.md` lists the machines and how each was obtained. `PROOF.md` walks through the
proof in plain words.

### Why a beeping machine

"There are infinitely many Sophie Germain primes" is a Π₂ statement: for every `n` there is a
`p ≥ n` with `p` and `2p + 1` prime. No finite counterexample refutes it, so no machine
*halts* iff it is false. A beeping machine searches forever and beeps at each Sophie Germain
prime, so it has a last beep iff they run out (the Beeping Busy Beaver setting; see
`../twinprimes/README.md`). If `BBB(17)` were known, running this machine for `BBB(17)` steps
would settle the question.

## How it works

For odd `n ≥ 5`, **`n` is a Sophie Germain prime iff no odd `d` with `3 ≤ d ≤ n − 2` divides
`n` or `2n + 1`.** An odd `n` with no odd divisor in that range is prime. If `2n + 1 = d·k`
with `1 < d < 2n + 1`, both factors are odd and `k ≥ 3`, so `d ≤ (2n + 1)/3 ≤ n − 2`
(`Spec.sg_iff`). The machine tests `n = 5, 7, 9, …` in turn by trial division with
`d = 3, 5, 7, …`, and **one mod walk per divisor tests both numbers**. The start beeps for
`n = 3`.

Tape (blank left of D and right of R), as in `../mersenne`:

    D 0 R

* **D** has `d` cells, all 1 except a **hole** (a single 0) at cell `c`, a counter mod `d`.
  Before a walk the hole is on cell 0, which is **the blank cell left of D's `d − 1` ones**.
  So D grows by one cell on its left for free whenever `d` grows.
* A single 0 separates D and R.
* **R** has `r` cells, `d + r = n − 1`; during the walk a hole moves right through it.

* **Walk.** `r` times: make the next R cell the R hole (R's cell 0 first), scan left to D's
  hole and **move it two cells right** (cyclically: from cell `d − 2` to 0, from `d − 1` to
  1), scan right to the R hole and fill it. D's hole ends on cell
  `c = 2r mod d = (2n − 2) mod d`, so (d is odd) **`d ∣ n` iff `c = d − 2`, and `d ∣ 2n + 1`
  iff `c = d − 3`**. The double step is the only change to `../mersenne`'s walk; it costs two
  states (`A3` and the second wrap `W3`).
* **End of the walk.** `B2` reads the blank after R and steps back: `E` erases R's last cell
  (`r := r − 1`) and steps right onto `B2` again, which reads the blank and steps back, and
  `E` now reads the erased cell. `V` scans left to the separator, `X` on to the hole, which
  it fills. `K1`, `K2`, `K3` read the next three cells:
  * the separator right after the hole (`c = d − 1`), or, found later by `H`
    (`c ≤ d − 4`): **`d` passed**. The separator is filled and becomes a cell of D, and `G0`
    writes the new separator on R's cell 0. With the blank left of D as the next walk's
    hole, `d` grows by 2 and `r` shrinks by 2. If R is empty instead, `d = n − 2` was the
    last odd divisor and every one passed: **BEEP**.
  * the separator two or three cells on (`c = d − 2` or `d − 3`): **FAIL**. The separator is
    filled and `V` scans to the left end.
* **Rebuild** (after a FAIL or the beep). The tape holds one block of `n − 1` ones and `V`
  runs to its left end. There the check runs again on the blank: `V` takes the blank for the
  separator, `X` takes the next blank for the hole and fills it, and `K1` finds the
  "separator" right after it, fills it and hands over to `G0`. So `X` and `K1` write `1 1`,
  and `G0` writes the separator after them: `D = 1 1` with its hole on the blank (`d = 3`)
  and `R = n − 2` ones, the tape for `n + 2`.
* **Start.** `B2` on the blank tape: `E` and `V` pass, `X` and `K1` write `1 1`, and `G0`
  reads the blank after them. That is the beep for `n = 3` (a block of `n − 1 = 2` ones),
  and the rebuild follows.

The design (`sophiegermain.txt`, from `build.py`) is: walk 9 (two scanners of 2 states, the R
step `B2`, the double D step `A2`, `A3`, the wraps `W1`, `W3`), round end 8 (`E`, `V`, `X`,
`K1`, `K2`, `K3`, `H`, `G0`). The merger finds nothing to join (the clique bound is 17). The
round end was found by **SAT synthesis** (`../tools/synth_round.py`) with the walk fixed. With
this walk no round end of 7 states (6 states) fits the reference's rounds within 4 extra steps
per round: the solver proved both unsatisfiable. See `RECORDS.md`.

| State (std) | Design | Reading 0 | Reading 1 |
|---|---|---|---|
| A | `B2` | past R's end: walk done (`E`) | make the R hole, go to D |
| B, C | `Y1`, `Y2` | pass the separator; fill D's hole | scan left |
| D, E | `A2`, `A3` | wrap (hole was on `d − 1` / `d − 2`) | step; make the new D hole |
| F, G | `W1`, `W3` | left end: new hole on cell 0 / 1 | scan left |
| H, I | `Z1`, `Z2` | pass the separator; fill the R hole | scan right |
| J | `E` | erased cell: to `V` | erase R's last cell, back to `B2` |
| K | `V` | separator (or left end): to `X` | scan left |
| L | `X` | the hole: fill it | scan left |
| M | `K1` | separator on `c + 1`: OK, fill it | to `K2` |
| N | `K2` | separator on `c + 2`: FAIL (`d ∣ n`) | to `K3` |
| O | `K3` | separator on `c + 3`: FAIL (`d ∣ 2n + 1`) | to `H` |
| P | `H` | separator: OK, fill it | scan right |
| Q | `G0` | R empty: **BEEP** | new separator, start the walk |

## Files and checks

| File | Contents |
|------|----------|
| `build.py` | The generator of the design (variant `halt`: the beep replaced by a halt; variant `ref`: the 20-state hand design used as the synthesis reference) |
| `sophiegermain.txt` = `machines/sophiegermain_17.txt` | The 17-state design, the best machine |
| `sophiegermain_ref.txt` = `machines/sophiegermain_20.txt` | The 20-state hand design |
| `test_e2e.py` | Every walk start and every check up to `n = 301` (1376 divisors) against a Python model of `(n, d, c)` and the tape; the first 40 beeps at the first 40 Sophie Germain primes (3 … 1049, 2.9·10⁹ steps) with the tape at each beep, for the design and the reference; the variant halts at `n = 3`; 10⁸ steps without halting |
| `gen_lean.py`, `gen_reduced_lean.py` | `Machine.lean` (`delta` and `deltaNB`, the design without its beep), `M17.lean` (the machine in standard state order, `beep_transition`) |
