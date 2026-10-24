# A Turing machine for the Riesel problem (below 509203)

A [Riesel number](https://en.wikipedia.org/wiki/Riesel_number) is an odd number k such that `k·2^n − 1` is [composite](https://en.wikipedia.org/wiki/Composite_number) for all `n ≥ 1`.
The Riesel conjecture is that 509,203 is the smallest Riesel number. This machine halts iff that is the case.

**Current best: `machines/riesel_min.txt`, a 68-state, 2-symbol Turing machine**
(named-state format, see `../tools/tm.py`). Started on a blank tape, it **halts iff no odd
k < 509203 is a Riesel number**: iff every odd `k < 509203` has some `n ≥ 1` with
`k·2^n − 1` prime:

    Halts delta start ↔
      ∀ k, k % 2 = 1 → k < 509203 → ∃ n, 1 ≤ n ∧ Prime (k * 2 ^ n - 1)

where `Prime p := 2 ≤ p ∧ ∀ d, d < p → 2 ≤ d → p % d ≠ 0` (`../lean/TinyCryptids/Defs.lean`).
The Lean development in `../lean/TinyCryptids/Riesel/` states this for the design machine
(`TM.Riesel.halts_iff`).

The statement is Σ₁ ("for each of finitely many k there is an n"), so unlike the other
machines this one halts iff the statement is **true**. 509203 is a Riesel number (every
`509203·2^n − 1` has a factor among 3, 5, 7, 13, 17, 241; the six cover all residues of n
mod 24), and it is conjectured to be the smallest; the machine halts iff that is so. At the
time of writing many `k` below it have no known prime (2293, 9221, 23669, 31859, 38473,
46663, …).

The 68-state machine is obtained in two stages:

1. `riesel.txt` (= `machines/riesel_91.txt`) is the readable **91-state design**, generated
   by `build.py`. The Lean development is written for this machine.
2. `../tools/minimize_clique.py` merges states of the design that never disagree on a
   transition the run uses (an exact SAT search that starts from a clique of pairwise
   incompatible states). The merge has 68 states, and the 68-clique proves no smaller merge
   exists; `machines/riesel_min_annotated.txt` is the same machine with each state named
   after its roles in the design.

## The search

    for k = 3, 5, ..., 509201:            (k = 1: 1·2^2 − 1 = 3 is prime)
        for n = 1, 2, ...:
            if k·2^n − 1 is prime: next k
    HALT

Trial division by a mod walk. There are no multiplications: the next candidate for the same
`k` is `2Q + 1` (Q doubled in unary), and the first candidate for the next `k` is built from a
copy of K.

The constant 509203 itself has to be stored: halting at the first `k` with a covering set would
need a Lean computation over all smaller `k`, and since 2293 is still open the bound cannot be
lowered to a power of two (262144) with the `k` above it proven by explicit primes.

## How it works

The tape, left to right (blocks of 1s, a hole is a single `0` inside a block):

    C 0 K 0 D 00 R

* **C** is a binary counter: five groups of four bits `b3 b2 b1 b0`, each followed by a marker
  1, most significant group first (25 cells). It holds the number of `k` still to come; the
  seed writes 254600, one of which the `k = 1` round spends before the first candidate.
* **K** has `k + 4` cells while `k` is tested.
* **D** has `d + 1` cells (cells `0 … d`), the trial divisor `d`. Its hole steps cyclically over
  cells `1 … d`; its **home** is cell `d`, D's last cell.
* **R** has `r + 2` cells, `r = Q − d − 1`. During the mod walk its hole steps from cell 0 to
  cell `r` and then falls off the end.

**Trial division.** For `d = 3, 4, …` (Q is odd): the mod walk advances the D hole `r + 1`
times, one step per step of the R hole (from D's last cell it wraps to cell 1); then `d | Q`
iff the D hole is home. The walk ends right of R, so the head comes back over R and the
separator and reads D's last cell: 0 is a divisor, and Q is composite. Otherwise the hole is
filled, and the **shift** needs no work on D: the first cell of the separator becomes D's new
last cell, and it is already 0, i.e. the hole is home again (`d := d + 1`). R loses its cell 0
(`r := r − 1`) and gets its hole at its new cell 0; if R is then a single cell, `d = Q` and Q
is prime.

**The loop** (`s1 … s7c`, `t1`) is the one routine that copies. Let X be a block whose last
cell is under the head, with blocks X' and T to its right, single 0s between them (both empty
at first). One round erases the last cell of X; it reappears as the first cell of X' (X' grows
to the left), and one more cell is appended to T. The loop stops at the first 0 it meets in X.
So X ends up moved one cell to the right as X', and T is a copy of it. `t1` reads the cell left
of the stop: 0 (the separator) for R, C's lowest marker for K.

**Composite** (`x1 … g7`, `a1 … a6`). Fill the hole and the separator; then from D's cell 1,
D := 3 (cells 1, 2, its hole home at cell 3), the separator, and R's hole at R's cell 0, which
leaves `Q − 2` cells for R; then run the loop on R: it stops at R's hole. Filling the gap left
by the loop and the X'/T separator joins R, X' and T, and two cells are appended: R gets
`2|R| + 3` cells, so the next candidate is `3 + 2(|R| + 1) = 2Q + 1 = k·2^(n+1) − 1`. The R
hole is already at cell 0 for the next mod walk.

**Prime** (`w1 … w3`, `Dm … ret`, `b2 … b6`). Wipe D and R (no hole left in D to step around)
and append a cell to K, then run the loop on K: it stops at the separator left of K. Then
decrement C: the borrow runs through the five groups; if it runs past the top group, C was 0
and the machine **halts** (this happens after `k = 509201`). Filling the cell left of K' gives
K two more cells (`k := k + 2`). T, a copy of the old K, becomes D := 3 and R from its cell 1
(`g1`), and the loop doubles R and appends two cells: the first candidate for the new `k` is
`2(k + 2) − 1`.

**The seed** writes C (254600) and K for `k = 1`; its region lacks R's cell 0, which `g6` makes
as the hole on a blank cell. `k = 1` needs no trial division (`1·2^2 − 1 = 3` is prime): one
round over K moves it, decrements C and fills the gap (`k := 3`), and T becomes D := 3 and R.
With no T block behind it, the loop over R is a *pseudo-round*: the doubling appends nothing,
so the first candidate is `Q = 2·3 − 1 = 5`. The pseudo-round saves two seed states (a run of
1s that merges with nothing).

State budget of the 91-state design: seed 32, mod walk and divisor test 16, shift 6, composite
4, D := 3 and the R hole 7, wipe 3, loop 7, end of the doubling 7, counter 6, new k 3.

## Files and checks

| File | Contents |
|------|----------|
| `build.py` | The generator of the design (`build(c0=…, nf=…)`: a smaller counter and a seed without the pseudo-round, for tests) |
| `riesel.txt` = `machines/riesel_91.txt` | The 91-state design |
| `machines/riesel_min.txt`, `_annotated.txt` | The merged machine, and the same machine with each state's roles |
| `test_routines.py` | The counter decrement on 1,172 values (and the halt at 0), the loop on R (`m = 0 … 39`) and on K (`|K| = 1 … 39`), and trial division of every odd Q from 5 to 399, on hand-placed tapes |
| `test_e2e.py` | From a blank tape: the region for every candidate reached in 3·10⁸ steps, with C, K, D and R checked at the end of each doubling; variants with a counter `c0 = 0 … 5` halt after `k = 2·c0 + 3`; 10⁸ steps of the real machine |
| `gen_lean.py` | Emits `../lean/TinyCryptids/Riesel/Machine.lean` |
| `annotate.py` | The annotated listing for a merged machine |

Shared tools in `../tools/`: `tm.py` (format, standard text), `sim.c` (`gcc -O2 -o ../tools/sim
../tools/sim.c`), `same_run.py A B k` (identical tapes after 10³ … 10^k steps), `minimize.py`,
`minimize_clique.py`, `greedy_merge.py`.

## Standard text (bbchallenge format, 68 states)

    0R1,---_0R2,1L1_1R3,1R33_1R4,0R48_1R5,---_1R6,---_1R7,---_1R8,---_0R9,1R8_1R10,1L9_0R11,1R10_0R12,1R44_1R13,0R42_0R14,1L13_1R15,1R44_1R16,---_0R17,---_0R18,---_0R19,---_1R20,---_1R21,---_0R22,---_0R23,---_0R24,---_1R25,---_0R26,---_1R27,---_1R28,---_1R29,---_1R30,---_1R31,---_0R45,---_1R33,0L39_0L1,0R34_0R35,1R34_0R34,1L36_1R37,1L9_1R44,1R38_0L41,1L32_0L40,1L39_0L39,1R32_0L42,1L41_0L36,0R43_0L50,1L40_1L13,1R45_1R53,1R46_1R59,0R47_1L62,0R3_0R49,0R49_0L52,1R49_0L50,0L51_1R49,0L51_0L57,0R45_0R54,1R53_1L55,1R54_0L56,1L55_0L52,1L56_0R58,1L64_0R46,---_1R60,1R59_0L62,1R61_1R47,1R61_0L39,1L62_0RZ,1L64_1L65,0R8_1L66,0R8_1L67,0R8_1L63,0R8

(States are numbered from 0 in file order; `Z` is the halting state, reached only from the counter.)
