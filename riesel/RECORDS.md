# Best machines so far

All machines are 2-symbol, start on a blank tape, and halt iff no odd k < 509203 is a
Riesel number (`∀ k, k % 2 = 1 → k < 509203 → ∃ n, 1 ≤ n ∧ Prime (k * 2 ^ n - 1)`).

| States | File | How obtained | Status |
|-------:|------|--------------|--------|
| **76** | `machines/riesel_76.txt` (readable: `riesel_76_annotated.txt`) | `minimize.py` (`kissat404`, `cadical195` and `maplechrono` all reach 76) on the 113-state design; the search for 75 ran for over half an hour on all three without a result when this was committed (resume: `MIN_SOLVER=kissat404 python3 ../tools/minimize.py riesel.txt out.txt 75`) | Proven in Lean: `TM.Riesel.M76.halts_iff` |
| 113 | `machines/riesel_113.txt` (= `riesel.txt`) | `build.py`: the earlier 110-state Sierpiński design with `k·2^n − 1`, a five-group counter, start at `k = 5` | Proven in Lean: `TM.Riesel.halts_iff` |

The design is three states larger than that Sierpiński design: the counter has 5 more cells (2 of them
left blank), K one more, and the rebuild one state less.

How merged machines are proven: as in `../sierpinski/RECORDS.md` (`gen_reduced_lean.py`,
`halts_iff_of_sim`).
