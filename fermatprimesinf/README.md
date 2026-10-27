# A beeping Turing machine for the Fermat primes: are there infinitely many?

**Current best: `machines/fermatprimesinf_16.txt`, a 16-state, 2-symbol beeping Turing
machine.** Started on a blank tape, it never halts, and it **quasihalts iff there are only
finitely many Fermat primes**: it takes its beep transition only finitely often iff only
finitely many numbers `2^(2^n) + 1` are prime.

**The beep is the transition of state `P` reading 0** (`0LA`, the first entry of the 16th
group in the standard text below; `G0` in the design and the Lean files). It is taken exactly
once for every Fermat prime, in order: 3, 5, 17, 257, 65537, …

This is `../fermatprimes`'s machine (which halts iff a Fermat prime beyond 65537 exists)
without its counter: every pass beeps.

## Standard text (bbchallenge format, 16 states)

    1LO1LA_0LI0LC_0LD1LC_1RE1LD_0LF0RG_0RE1LF_0RH1RG_1RB1RH_---0LJ_1LK1LJ_1RA0LL_0LM0LL_0RN1RO_1RN1LA_1RO1RP_0LA0RB

States are `A`–`P` in order, `A` is the start state. `---` marks a transition the machine
never uses (`I`, the walk end's erase, only ever reads a 1).
**Beep: `P` reading 0 → write 0, move left, go to `A`.**

## What is proved

Lean (`../lean/TinyCryptids/FermatPrimesInf/`, core Lean 4.15.0, no Mathlib):

    theorem TM.FermatPrimesInf.M16.quasihalts_iff :
        QuasiHalts delta2 St2.G0 false start2 ↔ ¬ InfinitelyManyFermatPrimes
    theorem TM.FermatPrimesInf.M16.never_halts : ¬ Halts delta2 start2
    theorem TM.FermatPrimesInf.M16.beep_transition :
        delta2 St2.G0 false = some (false, Dir.L, St2.C4)

with (`../lean/TinyCryptids/Core/Beep.lean`, `../lean/TinyCryptids/Defs.lean`)

    def BeepsAt δ qb bb c n := ∃ c', run δ n c = some c' ∧ c'.q = qb ∧ c'.R 0 = bb ∧ δ qb bb ≠ none
    def QuasiHalts δ qb bb c := ∃ N, ∀ n, N ≤ n → ¬ BeepsAt δ qb bb c n
    def InfinitelyManyFermatPrimes := ∀ n, ∃ k, n ≤ k ∧ Prime (2 ^ 2 ^ k + 1)

`BeepsAt … n` says that step `n + 1` of the run is the beep transition (state `qb` reading
`bb`). `QuasiHalts` says that there is a last beep, or none. `Prime` is the repository's
definition (`2 ≤ p` and no `d` with `2 ≤ d < p` divides `p`). The 17-state design has the same
theorems (`TM.FermatPrimesInf.quasihalts_iff`, `never_halts`), plus `beeps_forever_iff`: it
beeps infinitely often iff there are infinitely many Fermat primes. All of them depend only on
`propext`, `Classical.choice` and `Quot.sound` (`../lean/Check.lean`).

`RECORDS.md` lists the machines and how each was obtained. `PROOF.md` walks through the
proof in plain words.

### Why a beeping machine

"There are infinitely many Fermat primes" is a Π₂ statement: for every `n` there is a `k ≥ n`
with `2^(2^k) + 1` prime. No finite run refutes it, so no machine *halts* iff it is false. A
beeping machine searches forever and beeps at each Fermat prime, so it has a last beep iff
they run out (the Beeping Busy Beaver setting; see `../twinprimes/README.md`). If `BBB(16)`
were known, running this machine for `BBB(16)` steps would settle the question. (It is
expected that there are only finitely many, possibly no more than the five known ones.)

## How it works

A prime of the form `2^k + 1` has `k` a power of 2 (if `k` has an odd factor `q > 1`, then
`2^(k/q) + 1` divides `2^k + 1`). So the Fermat primes are exactly **the primes `m` with
`m − 1` a power of 2**, and for odd `m ≥ 5` these are the `m` such that **no odd `d` with
`3 ≤ d ≤ m − 2` divides `m` or `m − 1`**. No odd `d` divides `m` iff `m` is prime, since `m` is
odd. No odd `d ≥ 3` divides `m − 1` iff `m − 1` is a power of 2, since an odd prime factor of
`m − 1` is at most `(m − 1)/2`. The machine tests `m = 5, 7, 9, …` in turn by trial division
with `d = 3, 5, 7, …`, and **one mod walk per divisor tests both numbers**. The start beeps for
`m = 3`.

Tape (blank left of D and right of R):

    D 0 R

* **D** has `d` cells, all 1 except a **hole** (a single 0) at cell `c`, a counter mod `d`.
  Before a walk the hole is on cell 0, which is **the blank cell left of D's `d − 1` ones**.
  So D grows by one cell on its left for free whenever `d` grows.
* A single 0 separates D and R.
* **R** has `r` cells, `d + r = m − 1`; during the walk a hole moves right through it.

* **Walk**. `r` times: make the next R cell the R hole (R's cell 0
  first), scan left to D's hole and move it one cell right (from the last cell back to cell
  0), scan right to the R hole and fill it. D's hole ends on cell `c = (m − 1) mod d`. So
  `d ∣ m` iff `c = d − 1`, and `d ∣ m − 1` iff `c = 0`.
* **Check** (as in `../fermatprimes`). `E` erases R's last cell (`r := r − 1`) and `V` scans
  back and fills the separator. `X1` reads D's cell `d − 1`: a 0 is the hole, `d ∣ m`:
  **FAIL**. Otherwise `X` erases D's cells leftwards to the hole and steps past it, and `Q`
  reads that cell: the blank left of D means `c = 0`, `d ∣ m − 1`: **FAIL** (`HF` refills and
  turns back); a 1 means **`d` passed**.
* **Shift.** `H1` refills the hole and the erased cells. The first 1 it meets is the old
  separator, now a cell of D, and `G0` writes the new separator on R's cell 0. With the blank
  left of D as the next hole, `d` grows by 2 and `r` shrinks by 2. If R is empty instead,
  `d = m − 2` was the last odd divisor and every one passed: **BEEP**.
* **Rebuild** (after a FAIL or the beep). The tape holds one block of `m − 1` ones. `C4` runs
  to its left end and writes a 1, `H1` writes another, and `G0` writes the separator after
  them: `D = 1 1` with its hole on the blank (`d = 3`) and `R = m − 2` ones, the candidate
  `m + 2`.
* **Start.** `C4` and `H1` write `1 1` on the blank tape, and `G0` reads the blank after them.
  That is the beep for `m = 3` (a block of `m − 1 = 2` ones), and the rebuild follows.

The 17-state design (`fermatprimesinf.txt`, from `build.py`) is: walk 8, end of the walk and
check 6, shift, beep and rebuild 3. Merging (`../tools/minimize_clique.py … G0:0`) joins the
wrap's last state with the D step: 16 states. The clique bound is also 16, so this is optimal
for the design. The merger keeps the beep exclusive: no state that reads 0 may share the beep
state's class.

## Files and checks

| File | Contents |
|------|----------|
| `build.py` | The generator of the design (variant `halt`: the beep replaced by a halt) |
| `fermatprimesinf.txt` = `machines/fermatprimesinf_17.txt` | The 17-state design |
| `machines/fermatprimesinf_16.txt`, `_annotated.txt` | The merged machine, and the same machine with each state's roles and the beep marked |
| `test_e2e.py` | Every walk start and every check up to `m = 201` (339 divisors) against a Python model of `(m, d, c)` and the tape; the beeps at 3, 5, 17, 257 with the tape at each beep, and no other beep in 10¹⁰ steps (65537 is out of reach); the variant halts at `m = 3`; 10⁸ steps without halting |
| `gen_lean.py`, `gen_reduced_lean.py`, `annotate.py` | `Machine.lean` (`delta` and `deltaNB`, the design without its beep), `M16.lean`, the annotated listing |
