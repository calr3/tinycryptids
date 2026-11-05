# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff some 2^n with n > 8 has no
digit 2 in base 3 (`∃ n, 8 < n ∧ 2 ∉ digits3 (2 ^ n)`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **15** | `machines/erdos_15.txt` (readable: `erdos_15_annotated.txt`) | Given (Stérin and Woods built a 15-state machine for this conjecture, [arXiv:2107.12475](https://arxiv.org/abs/2107.12475)) | Proven in Lean: `TM.Erdos.halts_iff` |

## Merging does not help

The state merging that shrinks the designs in other folders (`../tools/minimize.py`) needs
transitions that the run never uses. This machine has almost none:
- In 10^10 steps, all 29 of its defined transitions are used. The only one never used is
  the halting one (`L` reading 1).
- The exact SAT merge to 14 states is UNSAT. No 14-state machine can be made by merging
  states of this one.

A smaller machine would need a different algorithm or tape layout.
