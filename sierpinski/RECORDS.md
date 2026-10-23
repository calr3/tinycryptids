# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff no odd k < 78557 is a
Sierpiński number (`∀ k, k % 2 = 1 → k < 78557 → ∃ n, 1 ≤ n ∧ Prime (k * 2 ^ n + 1)`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **60** | `machines/sierpinski_60.txt` (readable: `sierpinski_60_annotated.txt`) | `minimize.py` (`kissat404`) on the 83-state design; the searches for 59 (`kissat404`, `cadical195`, `maplechrono`) found nothing in the time they were given | Proven in Lean: `TM.Sierpinski.M60.halts_iff` |
| 83 | `machines/sierpinski_83.txt` (= `sierpinski.txt`) | `build.py`: one-cell separators in the copy loop, R's hole from cell 0, the D hole's home on D's last cell (divisor test on the way back, shift without a reset), single-0 separators C/K and K/D, a pseudo-round for k = 1 | Proven in Lean: `TM.Sierpinski.halts_iff` |

An earlier design of 110 states (a copy loop with two-cell separators, a mod walk
from d = 3; merged to 72 states by `minimize.py`) was proven in Lean when it was current and
is not kept here.

How merged machines are proven: `minimize.py` only merges states whose defined transitions
agree, so the merged machine follows the same run. The design halts by a transition to an
explicit `halt` state, which merging must keep. `gen_reduced_lean.py` emits the merged machine,
the state map `phi`, a `compat` check and the theorem transferred by `halts_iff_of_sim`.
