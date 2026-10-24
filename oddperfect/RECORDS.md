# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff an odd perfect
number exists (`∃ n, n % 2 = 1 ∧ properDivSum n = n`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **37** | `machines/oddperfect_37.txt` (readable: `oddperfect_37_annotated.txt`) | `../tools/minimize_clique.py` on the 50-state design: optimal for this design (34, 35 and 36 are unsatisfiable; the clique bound is 34) | Proven in Lean: `TM.OddPerfect.M37.halts_iff` |
| 50 | `machines/oddperfect_50.txt` (= `oddperfect.txt`) | `build.py`: `../sierpinski`'s mod walk (D's home on its last cell), the add loop moves the D hole down while T's hole saturates for free, one round end that writes R's new cells, marks D's cell 1, checks and regrows T; the seed is a pseudo-round n = -1 | Proven in Lean: `TM.OddPerfect.halts_iff` |

How merged machines are proven: `minimize.py` / `greedy_merge.py` only merge states whose
defined transitions agree, so the merged machine follows the same run. `sim_run` and
`halts_iff_of_sim` (`lean/TinyCryptids/Core/Basic.lean`) turns this into a proof: `gen_reduced_lean.py` emits the merged machine,
the state map `phi`, a `compat` check (one case per transition) and the transferred theorem.

## Notes on the 50-state design

* Without the seed, the 43 working states merge to 34 (a fully specified machine, no
  transition left undefined); the seed costs 3 more. Seeds tried: the end of the round
  n = 1 written as fresh states (11 states: 39), the same through the shift states f1..f5
  (39), the pseudo-round n = -1 (7 states: 37), and booting through existing states with
  three new 0-transitions (start in `ma1`, its wrap-around comes back to write D: 37).
* Searches for a cheaper boot (none found): 30 different 34-state merges of the core, each
  with one extra start state (all 2 x 141 x 140 choices of its transitions, simulated: the
  run must reach the round end of n = -1 or n = 1); and, by SAT (the merged machine's free
  transitions and the boot run as variables, at most 24 steps), 40 merges into 35 classes
  with 0 or 1 extra state and 40 merges into 34 classes with 2 extra states. So 36 would
  need another seed idea or another core.
* Variants of the round end merge to the same 34-state core: checking the T hole from the
  T/D boundary instead of a parser (`c2 … c5`), and marking D's cell 1 with the mod walk's
  own wrap-around (a pseudo-walk whose R hole is the cell before R's new last cell).
* `minimize.py` (descending K) did not finish K = 38 on the first variant in 30 minutes;
  `minimize_clique.py` proves 38 unsatisfiable in seconds.
