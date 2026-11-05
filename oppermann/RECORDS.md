# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff Oppermann's conjecture is false
(`∃ n, 2 ≤ n ∧ ((∀ p, n * n - n < p → p < n * n → ¬ Prime p) ∨ (∀ p, n * n < p → p < n * n + n → ¬ Prime p))`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **45** | `machines/oppermann_45.txt` (readable: `oppermann_45_annotated.txt`) | `minimize.py` (`kissat404`, `cadical195` and `maplechrono` all reach 45) on the 74-state design; 44 not found in an hour by any of them (`maplechrono` timed out, the others were stopped) | Proven in Lean: `TM.Oppermann.M45.halts_iff` |
| 74 | `machines/oppermann_74.txt` (= `oppermann.txt`) | `build.py`: `../legendre`'s trial division and flag, with intervals `[⌊j²/4⌋, ⌊(j+1)²/4⌋)`: a Q block of `j` cells whose hole moves two cells per number, grown by one cell per interval | Proven in Lean: `TM.Oppermann.halts_iff` |

How merged machines are proven: `minimize.py` only merges states whose defined transitions
agree, so the merged machine follows the same run. The design halts by a transition to an
explicit `halt` state, which merging must keep. `gen_reduced_lean.py` emits the merged machine,
the state map `phi`, a `compat` check and the theorem transferred by `halts_iff_of_sim`.
