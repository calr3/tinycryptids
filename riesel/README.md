# A Turing machine for the Riesel problem (below 509203)

A [Riesel number](https://en.wikipedia.org/wiki/Riesel_number) is an odd number k such that `k·2^n − 1` is [composite](https://en.wikipedia.org/wiki/Composite_number) for all n.
The Riesel problem is to show that 509,203 is the smallest Riesel number. This machine halts iff that is the case.

**Current best: `machines/riesel_76.txt`, a 76-state, 2-symbol Turing machine**
(named-state format, see `../tools/tm.py`). Started on a blank tape, it **halts iff no odd
k < 509203 is a Riesel number**: iff every odd `k < 509203` has some `n ≥ 1` with
`k·2^n − 1` prime. Lean proves this (`TM.Riesel.M76.halts_iff`):

    Halts M76.delta2 M76.start2 ↔
      ∀ k, k % 2 = 1 → k < 509203 → ∃ n, 1 ≤ n ∧ Prime (k * 2 ^ n - 1)

where `Prime p := 2 ≤ p ∧ ∀ d, d < p → 2 ≤ d → p % d ≠ 0` (`TinyCryptids.Prime`,
`../lean/TinyCryptids/Defs.lean`). `RECORDS.md` lists the machines, and `PROOF.md` walks
through the proof.

The statement is Σ₁, so the machine halts iff it is **true**. 509203 is a Riesel number
(every `509203·2^n − 1` has a factor among 3, 5, 7, 13, 17, 241) and is conjectured to be the
smallest; several dozen `k` below it still have no known prime.

The machine is an earlier 110-state design of the Sierpiński machine (a copy loop with
two-cell separators, a mod walk from d = 3; not kept in `../sierpinski/`) with `−1` in place of
`+1`. The Sierpiński machine has since been redesigned (83 states, merged 60), and the same
changes should apply here. The differences from that earlier design:

* The next candidate for the same `k` is `2P + 1`, so the composite rebuild keeps all `P − 1`
  cells of R (Sierpiński drops one): one state less.
* The first candidate for a new `k` is `2k − 1`, so K has `k + 7` cells while `k` is tested.
* The machine starts at `k = 5` (`1·4 − 1 = 3` and `3·2 − 1 = 5` are prime; the step to
  `k = 3` would leave R a single cell, too short for its hole).
* The counter needs 18 bits: five groups of four bits (25 cells), starting at 254599 = 0x3E287.
  The seed leaves its two leading 0 bits blank.

The design has **113 states** (`riesel.txt`, `build.py`); `../tools/minimize.py` merges it to
76. The Lean proof (`../lean/TinyCryptids/Riesel/`) is that of Sierpiński's earlier design, with the counter
lemmas written for any number of groups (`Cg`, `cg_dec`, `cg_zero`).

## Files and checks

| File | Contents |
|------|----------|
| `build.py` | The generator of the design (`build(c0=…)`: a smaller counter, for tests) |
| `riesel.txt` = `machines/riesel_113.txt` | The 113-state design |
| `machines/riesel_76.txt`, `_annotated.txt` | The merged machine, and the same machine with each state's roles |
| `test_routines.py` | The counter decrement on 1,426 values (and the halt at 0), the loop on R and on K |
| `test_e2e.py` | From a blank tape: the region for every candidate up to `k = 43`; variants with a counter `c0 = 0 … 5` halt after `k = 2·c0 + 3`; 10⁸ steps of the real machine |
| `gen_lean.py`, `gen_reduced_lean.py`, `annotate.py` | As in `../sierpinski/` |

## Standard text (bbchallenge format, 76 states)

    1R1,0R53_1R2,0R36_1R3,1R35_1R4,1R38_1R5,0R36_1R6,1R5_0R7,0L39_1R8,0R8_0R9,1R12_0R10,1L9_1R11,1R1_0R12,0R51_1R13,1R45_1R14,1R17_0R15,1R14_0R16,---_0R17,1R11_1R18,0R52_0R19,1R26_1R20,1R46_1R21,---_1R22,---_1R23,---_0R24,1L23_0R25,1R44_1R26,---_1R27,1R43_1R28,1R0_1R29,---_1R30,---_1R31,---_1R32,---_1R33,---_1R34,---_0R50,1R13_0L9,1L4_0R37,1R36_0R36,1L2_0L41,1L6_0L40,1L39_0L39,1R1_0L42,1L41_0L41,1L18_1L23,---_1R67,0R5_0L54,1L6_0R47,---_1R48,1R47_1R49,---_0L50,1R49_0R51,1L50_1R58,1R34_0L55,0R27_0L57,1R53_0L52,0L54_0L56,0L55_0L57,0L55_0L64,0R50_0R59,1R58_0R60,---_1L61,1R60_0L62,1L61_0L63,---_0L53,1L63_0L70,1R65_0R66,---_1R44,---_1R68,1R67_1L69,---_0L39,1L69_0RZ,1L71_1L72,0R75_1L73,0R75_1L74,0R75_1L70,0R75_0R11,1R75

(States are numbered from 0 in file order; `Z` is the halting state, reached only from the counter.)
