# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff the Goormaghtigh conjecture is
false (`∃ x y m n, 1 < y ∧ y < x ∧ 2 < m ∧ 2 < n ∧ rep x m = rep y n ∧ rep x m ≠ 31 ∧ rep x m ≠ 8191`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **53** | `machines/goormaghtigh_53.txt` (readable: `goormaghtigh_53_annotated.txt`) | `minimize_clique.py` (`kissat404`) on the 73-state design: clique bound 52, 52 UNSAT, 53 SAT (optimal for this design) | Proven in Lean: `TM.Goormaghtigh.M53.halts_iff` |
| 73 | `machines/goormaghtigh_73.txt` (= `goormaghtigh.txt`) | `build.py`: the walks `r := r·b + 1` in one region `R H D` of `V + 1` cells (copying and comparing in one motion), the base as a hole in Vb, a countdown F of bad values | Proven in Lean: `TM.Goormaghtigh.halts_iff` |
| 54 | (not kept) | `minimize_clique.py` on a 74-state design with F right of the region (it had to move F when the region grew) | — |
| 56 | (not kept) | `minimize_clique.py` on the first 78-state design (F right of the region, halting at the second hit) | — |

How merged machines are proven: the merger only merges states whose defined transitions
agree, so the merged machine follows the same run. The design halts by a transition to an
explicit `halt` state, which merging must keep. `gen_reduced_lean.py` emits the merged machine,
the state map `phi`, a `compat` check and the theorem transferred by `halts_iff_of_sim`.
