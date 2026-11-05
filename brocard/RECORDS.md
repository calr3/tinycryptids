# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff Brocard's problem
has a solution beyond 4, 5, 7 (`∃ n m, 8 ≤ n ∧ fact n + 1 = m * m`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **61** | `machines/brocard_61.txt` (readable: `brocard_61_annotated.txt`) | `minimize.py` (`cadical195`, `kissat404` and `maplechrono` all reach 61) on the 98-state design | Proven in Lean: `TM.Brocard.M61.halts_iff` |
| 98 | `machines/brocard_98.txt` (= `brocard.txt`) | `build.py`: unary factorial by copying, square test by odd sums, 7-round warm-up | Proven in Lean: `TM.Brocard.halts_iff` |

How merged machines are proven: `minimize.py` only merges states whose defined
transitions agree, so the merged machine follows the same run. `sim_run` and
`halts_iff_of_sim` (`lean/TinyCryptids/Core/Basic.lean`) turns this into a proof: `gen_reduced_lean.py` emits the merged
machine, the state map `phi`, a `compat` check and the transferred theorem.
