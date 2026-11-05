# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff Andrica's conjecture is false
(`∃ p q, Prime p ∧ Prime q ∧ p < q ∧ (∀ r, p < r → r < q → ¬ Prime r) ∧ 4 * p ≤ (q - p - 1) ^ 2`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **51** | `machines/andrica_51.txt` (readable: `andrica_51_annotated.txt`) | `minimize.py` (`kissat404`, `cadical195` and `maplechrono` all reached 51) on the 88-state design; greedy merging gave 56; the searches for 50 were stopped after an hour without a result (`maplechrono` timed out; to resume: `MIN_SOLVER=kissat404 python3 ../tools/minimize.py andrica.txt out.txt 50`) | Proven in Lean: `TM.Andrica.M51.halts_iff` |
| 88 | `machines/andrica_88.txt` (= `andrica.txt`) | `build.py`: `../legendre`'s trial division of `m = 2, 3, …`, a phase block that keeps `t(m) = ⌈2√m⌉`, and a countdown `\|T\|` in `U 00 T` reset to `t(m)` at each prime | Proven in Lean: `TM.Andrica.halts_iff` |
| 54 | (not kept) | `minimize.py` on an earlier 90-state design whose countdown was a hole in T; the way back needed one more parser | — |

How merged machines are proven: `minimize.py` only merges states whose defined transitions
agree, so the merged machine follows the same run. The design halts by a transition to an
explicit `halt` state, which merging must keep. `gen_reduced_lean.py` emits the merged machine,
the state map `phi`, a `compat` check and the theorem transferred by `halts_iff_of_sim`.
