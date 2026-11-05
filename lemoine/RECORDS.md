# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff Lemoine's conjecture is false
(`∃ n, 7 ≤ n ∧ n % 2 = 1 ∧ ∀ p q, Prime p → Prime q → p + 2 * q ≠ n`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **54** | `machines/lemoine_54.txt` (readable: `lemoine_54_annotated.txt`) | `minimize.py` (`kissat404`, `cadical195` and `maplechrono` all reached 54) on the 84-state design; the searches for 53 were stopped after an hour without a result (`maplechrono` timed out; to resume: `MIN_SOLVER=kissat404 python3 ../tools/minimize.py lemoine.txt out.txt 53`) | Proven in Lean: `TM.Lemoine.M54.halts_iff` |
| 84 | `machines/lemoine_84.txt` (= `lemoine.txt`) | `build.py`: two pairs under `../legendre`'s trial division, sentinels, the gap that records `2q` | Proven in Lean: `TM.Lemoine.halts_iff` |

Earlier design (not kept): 90 states → 54, with `q += 1` by scans to the end of Q, a separate
pass to the end of Q before normalizing it, and the next `n` erasing Q one routine per block.
The 84-state design replaced those by the parser that finds the single 0 before the right sentinel
and a 2-state erase (`U`, `X`); the merged size stayed 54.

How merged machines are proven: `minimize.py` only merges states whose defined transitions
agree, so the merged machine follows the same run. The design halts by a transition to an
explicit `halt` state, which merging must keep. `gen_reduced_lean.py` emits the merged machine,
the state map `phi`, a `compat` check and the theorem transferred by `halts_iff_of_sim`.
