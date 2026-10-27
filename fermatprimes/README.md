# A Turing machine for the Fermat primes: is F₄ = 65537 the last one?

**Current best: `machines/fermatprimes_25.txt`, a 25-state, 2-symbol Turing machine.**
Started on a blank tape, it **halts iff some Fermat number `F_n = 2^(2^n) + 1` with `n ≥ 5`
is prime**, i.e. iff 65537 is not the last Fermat prime. The machine settles nothing by itself;
whether it halts is the open problem.

## Standard text (bbchallenge format, 25 states)

    1LB---_1LC---_1LD---_1LE---_1LF---_1LG0LO_0LY0RM_0LF0LI_0LJ1LI_1RK1LJ_0LL0RM_0RG1LL_0RN1RM_1RH1RN_1LP1LO_1RY0LQ_0LR0LQ_0RS1RT_1RS1LY_1RT1RU_0RV0RH_0RV0RW_0LZ1LX_0LX1LY_1LT1LY

States are `A`–`Y` in order, `A` is the start state; `Z` is the halting state, reached only by
`W` reading 0. `---` marks a transition the machine never uses.

## What is proved

Lean (`../lean/TinyCryptids/FermatPrimes/`, core Lean 4.15.0, no Mathlib):

    theorem TM.FermatPrimes.M25.halts_iff :
        Halts delta2 start2 ↔ ∃ n, 5 ≤ n ∧ Prime (2 ^ 2 ^ n + 1)

`Prime` is the repository's definition (`2 ≤ p` and no `d` with `2 ≤ d < p` divides `p`,
`../lean/TinyCryptids/Defs.lean`). The 27-state design has the same theorem
(`TM.FermatPrimes.halts_iff`). Both depend only on `propext`, `Classical.choice` and
`Quot.sound` (`../lean/Check.lean`). `RECORDS.md` lists the machines; `PROOF.md` walks through
the proof in plain words.

## How it works

A prime of the form `2^k + 1` has `k` a power of 2 (if `k` has an odd factor `q > 1`, then
`2^(k/q) + 1` divides `2^k + 1`). So the Fermat primes are exactly **the primes `m` with `m − 1`
a power of 2**, and for odd `m ≥ 5` these are the `m` such that no odd `d` with
`3 ≤ d ≤ m − 2` divides `m` or `m − 1`. No odd divisor of `m` means `m` is prime (it is odd);
no odd divisor `≥ 3` of `m − 1` means `m − 1` is a power of 2 (an odd prime factor of `m − 1`
is at most `(m − 1)/2`). The machine tests `m = 3, 5, 7, …` by trial division with
`d = 3, 5, 7, …`, **one mod walk per divisor for both numbers**. Such an `m` is a **pass**.

The passes up to 65537 are 3, 5, 17, 257 and 65537. **A counter of 6 cells**, written far right
at the start, loses one cell at each pass, and the pass that erases its last cell halts: the
6th pass, which is a Fermat prime above 65537.

Tape (blank left of D):

    D 0 R 0 … 0 K

* **D** has `d` cells, all 1 except a **hole** at cell `c`, a counter mod `d`. Before a walk
  the hole is on cell 0, **the blank cell left of D's `d − 1` ones** (D grows there for free).
* A single 0 separates D and R. **R** has `r` cells, `d + r = m − 1`.
* **K**, the counter, lies right of some blank cells. R only ever shrinks at its right end,
  so the search never reaches K.

* **Walk**. `r` times: make the next R cell the R hole, scan left to D's
  hole and move it one cell right (from the last cell back to cell 0), scan right to the R
  hole and fill it. D's hole ends on cell `c = (m − 1) mod d`: `d ∣ m` iff `c = d − 1`, and
  `d ∣ m − 1` iff `c = 0`.
* **Check.** `E` erases R's last cell (`r := r − 1`) and `V` scans back and fills the
  separator. `X1` reads D's cell `d − 1`: a 0 is the hole, `d ∣ m`: **FAIL**. Otherwise `X`
  erases D's cells leftwards to the hole and steps past it, and `Q` reads that cell: the
  blank left of D means `c = 0`, `d ∣ m − 1`: **FAIL**; a 1 means **`d` passed**.
* **Shift.** `H1` refills the hole and the erased cells. The first 1 it meets is the old
  separator, now a cell of D, and `G0` writes the new separator on R's cell 0. With the blank
  left of D as the next hole, `d` grows by 2 and `r` shrinks by 2. If R is empty instead,
  `d = m − 2` was the last odd divisor and every one passed: **PASS**.
* **Pass.** `P1` runs right over the blanks to K and erases its first cell; `P2` reads the
  next: 1, `P3` runs back to the block; 0, it was K's last cell: **HALT**.
* **Rebuild** (after a FAIL or a pass). The tape holds one block of `m − 1` ones: `C4` runs to
  its left end and writes a 1, `H1` writes another, and `G0` writes the separator after them.
  That is `D = 1 1` with its hole on the blank (`d = 3`) and `R = m − 2`: the candidate `m + 2`.
* **Start.** `S1`–`S6` write K, `S7` leaves a blank, `C4` and `H1` write `1 1`, and `G0` reads
  the blank: the pass for `m = 3`.

The 27-state design (`fermatprimes.txt`, from `build.py`) is: start 7, walk 8, check 6, shift
and pass 5, rebuild 1. Merging (`../tools/minimize_clique.py`) puts the start's last two states
into the walk end's `E` and the wrap's `W2`: 25 states, equal to the clique bound.

## Files and checks

| File | Contents |
|------|----------|
| `build.py` | The generator of the design; `build(k)` writes a counter of `k` cells |
| `fermatprimes.txt` = `machines/fermatprimes_27.txt` | The 27-state design |
| `machines/fermatprimes_25.txt`, `_annotated.txt` | The merged machine, and the same machine with each state's roles |
| `test_e2e.py` | Every walk start and every check up to `m = 201` (339 divisors) against a Python model of `(m, d, c)` and the tape; the passes at 3, 5, 17, 257 with the counter at 6, 5, 4, 3 cells, and no other pass in 10¹⁰ steps; counters of 2, 3, 4 cells halt at `m` = 5, 17, 257; 10⁸ steps without halting |
| `gen_lean.py`, `gen_reduced_lean.py`, `annotate.py` | `Machine.lean`, `M25.lean`, the annotated listing |
