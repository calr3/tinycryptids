# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff Legendre's
conjecture is false (`∃ n, 1 ≤ n ∧ ∀ p, n ^ 2 < p → p < (n + 1) ^ 2 → ¬ IsPrime p`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **44** | `machines/legendre_44.txt` (readable: `legendre_44_annotated.txt`) | `minimize.py` (`cadical195` and `maplechrono` both reach 44) on the 71-state design | Proven in Lean: `TM.Legendre.M44.halts_iff` |
| 71 | `machines/legendre_71.txt` (= `legendre.txt`) | `build.py`: trial division by mod walk, Q counter with a flag | Proven in Lean: `TM.Legendre.halts_iff` |

How merged machines are proven: `minimize.py` only merges states whose defined
transitions agree, so the merged machine follows the same run. `sim_run` and
`halts_iff_of_sim` (`lean/TinyCryptids/Core/Basic.lean`) turns this into a proof: `gen_reduced_lean.py` emits the merged
machine, the state map `phi`, a `compat` check and the transferred theorem.
