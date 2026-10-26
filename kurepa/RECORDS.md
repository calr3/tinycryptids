# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff Kurepa's conjecture is false
(`∃ p, Prime p ∧ 2 < p ∧ p ∣ leftFact p`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **38** | `machines/kurepa_38.txt` (readable: `kurepa_38_annotated.txt`) | `greedy_merge.py` on the 47-state design; `minimize.py` (`kissat404`, `cadical195`, `maplechrono`) proves 37 unsatisfiable | Proven in Lean: `TM.Kurepa.M38.halts_iff` |
| 47 | `machines/kurepa_47.txt` (= `kurepa.txt`) | `build.py`: every `n ≥ 3` tested for `n ∣ !n` by a hole walking L against a cyclic N hole; `(n+1)!` by copying, `!(n+1)` by filling a marker | Proven in Lean: `TM.Kurepa.halts_iff` |

Variants of the design tried on the way, all 38 after merging with 37 unsatisfiable: the seed
written left to right into the first copy (41 before the copy cursor and the check were
reworked), the seed entering at `kk` (one cell shorter), and the copy cursor walking F right to
left (no scan back to `m1`). A first design with `00` separators between L, F and Q, a
padded F and an `n + 1`-cell N merged to 50.

How merged machines are proven: `minimize.py` only merges states whose defined
transitions agree, so the merged machine follows the same run. `sim_run` and
`halts_iff_of_sim` (`lean/TinyCryptids/Core/Basic.lean`) turns this into a proof: `gen_reduced_lean.py` emits the merged
machine, the state map `phi`, a `compat` check and the transferred theorem.
