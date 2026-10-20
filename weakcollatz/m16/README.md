# The given 16-state machine

*Superseded by the 14-state machine in `../`, which is this machine with two states removed.
Kept with its proof as the starting point.*

`machines/weakcollatz_16.txt` (readable: `machines/weakcollatz_16_annotated.txt`) is the
16-state blank-tape cycle detector of the release *Two exact binary Collatz Turing machines*
(which has its own Lean 4.30 proof and attribution notes). `build.py` regenerates it transition
for transition, with states named after their roles:

    1RP1LA_0LC0LC_0RD1LC_1RP1RE_1LB0RF_1LG1RF_0RI0LH_1RE1LH_0LA0LJ_1LK1LJ_0RN0RL_1RM1RL_0LA1RI_0RO1RN_0RZ1LB_0LC1RP

Lean proves it halts iff the Collatz map has a cycle other than 1 → 4 → 2 → 1
(`TM.WeakCollatz16.halts_iff`, `../../lean/TinyCryptids/WeakCollatz16/`, using the shared
arithmetic `Spec.lean` and `Cycle.lean` of `../../lean/TinyCryptids/WeakCollatz/`).

It works like the 14-state machine (see `../README.md`), except:

* the marker starts on cell **1** (`disp` only steps right), so an even `v` meets the hole on
  the same cell (`mark` reads 0) and `cut` writes the result hole one cell to the left, and an
  odd `v` meets on neighbouring cells (`stepH` reads 0);
* after the hole runs off the block (or for `v = 1`), `fill` fills the marker and `grow` runs
  right to the end of the block before going home, although the tape is already right.

Files: `build.py`, `test_e2e.py` (same checks as `../test_e2e.py`), `annotate.py`,
`gen_lean.py` (writes `../../lean/TinyCryptids/WeakCollatz16/Machine.lean`).
